#!/usr/bin/env python3
"""Breaks a proof that one `bv_decide` call can't finish into smaller lemmas, keeps the ones that check, and
reuses them in the next proof.

A prototype, for research only. README.md next to this says what each file is, and docs/lemma-reuse.md
what it found. Each goal in goals.toml is a theorem that a rewrite returns what clang's code returns, on
every input, and for each one this:

1. Tries the theorem the way tests/llvm/Rewrites.lean would, as one `bv_decide` call at its default limit.
2. Runs clang's code on test inputs, to find cut points: values partway through that hold, field by field,
   counts of the input's set bits. Nothing found this way is trusted. It only decides what to ask Lean.
3. States a lemma for each step between cut points, over fresh variables where it can, and looks for it in the
   store: the same statement, or one that says the same under weaker hypotheses.
4. Checks what isn't there, each lemma in a module of its own, as general as simulation says it holds, falling
   back to what the goal needs if Lean disagrees. A first step that runs out of time is cut at every cut point
   inside it.
5. Saves what checked to the store, and continues the original proof from where `bv_decide` gave up, rewriting
   with the lemmas.
6. Checks the finished theorem's axioms, and replays it and every module it uses through the kernel.

usage: prototypes/lemma-reuse/lemmas.py prove [THEOREM ...] [--store DIR] [--fresh] [--baseline [S]]
       prototypes/lemma-reuse/lemmas.py rewrite THEOREM [--write]

Run it in the dev shell, after `lake build` and building build/ir-lean.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
import tomllib
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "tests"))
from llvm import LIMIT, PROOFS, Pipeline  # noqa: E402

GOALS = HERE / "goals.toml"
STORE = HERE / "store"
BUILD = ROOT / "build" / "lemma-reuse"
SEEDS = [PROOFS / "Kit.lean", PROOFS / "Bits.lean", HERE / "Count.lean"]
# A lemma's `bv_decide` gets this long, in seconds. The steps here take well under one.
LEMMA_SOLVER_SECONDS = 60
# Any one Lean process. Past this, what it would have said is unknown.
PROCESS_SECONDS = 900
FIELD_WIDTHS = (2, 4, 8, 16, 32, 64)
TESTS = 256
# What a proved goal rests on that nothing here checks. docs/lemma-reuse.md says more of each.
ASSUMPTIONS = [
    "scope: a theorem about the two functions as this LLVM IR, in this project's model of it, as "
    "docs/trust.md says",
    "emitter: ir-lean's translation of each function is trusted, as for every proof in this repo",
    "bv_decide: each lemma's and the goal's bv_decide axioms are checked by tests/check_axioms.lean, which "
    "reruns the toolchain's LRAT checker on them, as tests/llvm.py does",
    "kernel: the goal, each lemma and Count.lean are replayed by leanchecker, so neither the store nor its "
    "index is trusted, only Lean's kernel and the toolchain",
    "search: cut points, how fields add up, and how general a lemma is come from running the code on test "
    "inputs, and are only what to ask Lean. A wrong guess costs a failed lemma, never a wrong theorem",
    "flags: llvm_exec discharges nuw, nsw and the return's range with bv_decide on the whole input, before "
    "any cut",
]

# ------------------------------------------------------------------------------------------------------------
# Straight-line LLVM IR: what clang left, parsed, run on integers, and written out as `llvm_exec` leaves it.


@dataclass(frozen=True)
class Node:
    name: str
    op: str
    width: int
    args: tuple[str | int, ...]
    # The operand's width, for a cast.
    source: int = 0


@dataclass
class Function:
    symbol: str
    param: str
    width: int
    result: int
    nodes: dict[str, Node]
    ret: str | int

    def order(self) -> list[str]:
        return list(self.nodes)


DEFINE = re.compile(r"^define\b[^@]*\bi(\d+) @([\w.$]+)\(i(\d+)(?: noundef)? %([\w.]+)\)")
BINARY = re.compile(
    r"^%([\w.]+) = (add|sub|mul|and|or|xor|shl|lshr|ashr)((?: (?:nuw|nsw|exact|disjoint))*) "
    r"i(\d+) (\S+), (\S+)$"
)
CAST = re.compile(r"^%([\w.]+) = (trunc|zext)((?: (?:nuw|nsw|nneg))*) i(\d+) (\S+) to i(\d+)$")
CTPOP = re.compile(r"^%([\w.]+) = (?:tail )?call i(\d+) @llvm\.ctpop\.i\d+\(i\d+ (\S+)\)$")
RET = re.compile(r"^ret i(\d+) (\S+)$")


def operand(text: str) -> str | int:
    return text[1:] if text.startswith("%") else int(text)


def parse(ir: str, symbol: str) -> Function:
    """The function `symbol`, if it's one block of the instructions below, on one integer. Anything else
    raises."""
    lines = ir.splitlines()
    start = next(
        (i for i, line in enumerate(lines) if (m := DEFINE.match(line)) and m.group(2) == symbol), None
    )
    if start is None:
        raise ValueError(f"no single-argument integer function @{symbol}")
    m = DEFINE.match(lines[start])
    assert m is not None
    result, width, param = int(m.group(1)), int(m.group(3)), m.group(4)
    nodes: dict[str, Node] = {}
    for raw in lines[start + 1 :]:
        line = raw.strip()
        if not line or line.startswith(";") or line == "entry:":
            continue
        if b := BINARY.match(line):
            w = int(b.group(4))
            nodes[b.group(1)] = Node(b.group(1), b.group(2), w, (operand(b.group(5)), operand(b.group(6))))
        elif c := CAST.match(line):
            nodes[c.group(1)] = Node(
                c.group(1), c.group(2), int(c.group(6)), (operand(c.group(5)),), int(c.group(4))
            )
        elif p := CTPOP.match(line):
            nodes[p.group(1)] = Node(p.group(1), "ctpop", int(p.group(2)), (operand(p.group(3)),))
        elif r := RET.match(line):
            return Function(symbol, param, width, result, nodes, operand(r.group(2)))
        else:
            raise ValueError(f"@{symbol} has what this doesn't model: {line}")
    raise ValueError(f"@{symbol} doesn't return")


def apply(node: Node, values: dict[str, int]) -> int:
    def value(a: str | int, w: int) -> int:
        return values[a] if isinstance(a, str) else a % (1 << w)

    mask = (1 << node.width) - 1
    if node.op in ("trunc", "zext"):
        return value(node.args[0], node.source) & mask
    if node.op == "ctpop":
        return value(node.args[0], node.width).bit_count()
    x, y = (value(a, node.width) for a in node.args)
    if node.op in ("shl", "lshr", "ashr") and y >= node.width:
        raise ArithmeticError(f"%{node.name} shifts by {y}")
    if node.op == "ashr":
        signed = x - (1 << node.width) if x >> (node.width - 1) else x
        return (signed >> y) & mask
    return BINARY_OPS[node.op](x, y) & mask


BINARY_OPS: dict[str, Callable[[int, int], int]] = {
    "add": lambda x, y: x + y,
    "sub": lambda x, y: x - y,
    "mul": lambda x, y: x * y,
    "and": lambda x, y: x & y,
    "or": lambda x, y: x | y,
    "xor": lambda x, y: x ^ y,
    "shl": lambda x, y: x << y,
    "lshr": lambda x, y: x >> y,
}


def evaluate(fn: Function, a: int) -> dict[str, int]:
    values = {fn.param: a}
    for node in fn.nodes.values():
        values[node.name] = apply(node, values)
    return values


def run_segment(fn: Function, start: str, end: str, value: int) -> int:
    """What `end` is when `start` is `value`, running only what's between them."""
    order = fn.order()
    values = {start: value}
    for name in order[order.index(start) + 1 : order.index(end) + 1]:
        values[name] = apply(fn.nodes[name], values)
    return values[end]


LEAN_OPS = {
    "add": "{} + {}",
    "sub": "{} - {}",
    "mul": "{} * {}",
    "and": "{} &&& {}",
    "or": "{} ||| {}",
    "xor": "{} ^^^ {}",
    "shl": "{} <<< {}",
    "lshr": "{} >>> {}",
    "ashr": "{}.sshiftRight' {}",
}


ATOM = re.compile(r"[\w.']+|\d+#\d+")


def paren(term: str) -> str:
    """`term` as an operand: in parentheses, unless it's a name, a literal, or one parenthesized whole."""
    if ATOM.fullmatch(term):
        return term
    if term.startswith("("):
        depth = 0
        for i, c in enumerate(term):
            depth += {"(": 1, ")": -1}.get(c, 0)
            if depth == 0:
                return term if i == len(term) - 1 else f"({term})"
    return f"({term})"


def render(fn: Function, name: str | int, env: dict[str, str], width: int) -> str:
    """`name` as a Lean term, the way `llvm_exec` leaves it, with each value in `env` written as given."""
    if isinstance(name, int):
        return f"{name % (1 << width)}#{width}"
    if name in env:
        return env[name]
    node = fn.nodes[name]
    if node.op in ("trunc", "zext"):
        return f"BitVec.setWidth {node.width} {paren(render(fn, node.args[0], env, node.source))}"
    if node.op == "ctpop":
        return f"BitVec.cpop {paren(render(fn, node.args[0], env, node.width))}"
    x, y = (paren(render(fn, a, env, node.width)) for a in node.args)
    return LEAN_OPS[node.op].format(x, y)


# ------------------------------------------------------------------------------------------------------------
# Cut points, found by running the code. What's found here only says what to ask Lean.


def fields(value: int, k: int, n: int) -> list[int]:
    return [(value >> (k * i)) & ((1 << k) - 1) for i in range(n)]


def pack(values: list[int], k: int) -> int:
    return sum(v << (k * i) for i, v in enumerate(values))


def counts(a: int, k: int, n: int) -> int:
    """`a` with each `k`-bit field replaced by its number of set bits."""
    return pack([f.bit_count() for f in fields(a, k, n)], k)


def test_inputs(width: int) -> list[int]:
    mask = (1 << width) - 1
    rng = random.Random(width)
    edge = (
        {0, 1, mask, mask - 1, 1 << (width - 1)}
        | {1 << i for i in range(width)}
        | {(1 << i) - 1 for i in range(width)}
    )
    return sorted(edge | {rng.getrandbits(width) for _ in range(TESTS)})


def layer_cuts(fn: Function) -> list[tuple[str, int]]:
    """Values holding, in each `k`-bit field, that field's count of the input's set bits, at the widest
    `k`."""
    runs = [evaluate(fn, a) for a in test_inputs(fn.width)]
    cuts = []
    for node in fn.nodes.values():
        if node.width != fn.width:
            continue
        for k in sorted((k for k in FIELD_WIDTHS if fn.width % k == 0 and k < fn.width), reverse=True):
            if all(r[node.name] == counts(r[fn.param], k, fn.width // k) for r in runs):
                cuts.append((node.name, k))
                break
    return cuts


def articulation(fn: Function) -> list[str]:
    """Values that everything after them reaches only through them, so a proof can cut there and forget the
    rest."""
    order = fn.order()
    index = {name: i for i, name in enumerate(order)} | {fn.param: -1}
    last_use: dict[str, int] = {}
    for i, node in enumerate(fn.nodes.values()):
        for a in node.args:
            if isinstance(a, str):
                last_use[a] = i
    if isinstance(fn.ret, str):
        last_use[fn.ret] = len(order)
    return [
        name
        for i, name in enumerate(order)
        if {v for v, u in last_use.items() if u > i and index[v] <= i} == {name}
    ]


@dataclass
class Step:
    """A step from one cut to the next: each output field is the sum of some of the input's, while they're
    within `needed`, and `widest` is as large as simulation says still works."""

    start: str
    end: str
    k: int
    inputs: int
    outputs: int
    terms: list[list[int]]
    needed: int
    widest: int = 0


def holds(fn: Function, step: Step, bound: int, rng: random.Random) -> bool:
    def ok(xs: list[int]) -> bool:
        try:
            out = fields(run_segment(fn, step.start, step.end, pack(xs, step.k)), step.k, step.outputs)
        except ArithmeticError:
            return False
        return all(out[j] == sum(xs[i] for i in t) for j, t in enumerate(step.terms))

    vectors = [[bound] * step.inputs, [0] * step.inputs]
    vectors += [[bound * ((i + s) % 2) for i in range(step.inputs)] for s in (0, 1)]
    vectors += [[rng.randint(0, bound) for _ in range(step.inputs)] for _ in range(TESTS)]
    return all(ok(xs) for xs in vectors)


def characterize(fn: Function, start: str, end: str, k: int, needed: int) -> Step | None:
    """How each `k`-bit field of `end` depends on those of `start`, as a sum, found by setting one input field
    to 1 at a time, and then checked on inputs within `needed`."""
    inputs, outputs = fn.nodes[start].width // k, fn.nodes[end].width // k
    if fn.nodes[end].width % k:
        return None

    def run(xs: list[int]) -> list[int]:
        return fields(run_segment(fn, start, end, pack(xs, k)), k, outputs)

    if any(run([0] * inputs)):
        return None
    terms: list[list[int]] = [[] for _ in range(outputs)]
    for i in range(inputs):
        for j, v in enumerate(run([int(i == other) for other in range(inputs)])):
            if v not in (0, 1):
                return None
            if v:
                terms[j].append(i)
    step = Step(start, end, k, inputs, outputs, terms, needed)
    rng = random.Random(f"{fn.symbol} {start} {end}")
    if not holds(fn, step, needed, rng):
        return None
    lo, hi = needed, (1 << k) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        lo, hi = (mid, hi) if holds(fn, step, mid, rng) else (lo, mid - 1)
    step.widest = lo
    return step


@dataclass
class Plan:
    layers: list[tuple[str, int]]
    k: int
    steps: list[Step]
    spec: str


def plan(fn: Function, rewrite: Function) -> Plan:
    """Where to cut clang's code, and what the rewrite's side is. Raises if this can't cut it."""
    top = rewrite.nodes.get(str(rewrite.ret))
    count = top if top is None or top.op == "ctpop" else rewrite.nodes.get(str(top.args[0]))
    if (
        top is None
        or count is None
        or count.op != "ctpop"
        or count.args != (rewrite.param,)
        or (top is not count and top.op not in ("trunc", "zext"))
    ):
        raise ValueError(
            "the rewrite isn't a population count of its argument, which is all this knows to split"
        )
    if (rewrite.width, rewrite.result) != (fn.width, fn.result):
        raise ValueError("the rewrite's type isn't the function's")
    spec = "BitVec.cpop a" if top.op == "ctpop" else f"BitVec.setWidth {rewrite.result} (BitVec.cpop a)"
    layers = layer_cuts(fn)
    if not layers:
        raise ValueError("no value holds field-by-field counts of the input")
    cut, k = layers[-1]
    if fn.width >= 1 << k:
        # cpop_fieldSum adds the fields' counts in k bits, which has to hold the whole count.
        raise ValueError(f"%{cut}'s {k}-bit fields can't hold a count of {fn.width} bits")
    points = articulation(fn)
    if cut not in points:
        raise ValueError(f"%{cut} isn't a cut point")
    order = fn.order()
    later = [p for p in points if order.index(p) > order.index(cut)]
    # A truncation of a cut is cut with it, so the steps are the same whatever width they start from.
    later = [
        p
        for i, p in enumerate(later)
        if not (
            i + 1 < len(later)
            and fn.nodes[later[i + 1]].op in ("trunc", "zext")
            and fn.nodes[later[i + 1]].args[0] == p
        )
    ]
    if not later or later[-1] != fn.ret:
        raise ValueError("the return value isn't reached through cut points")
    steps, start, bound = [], cut, k
    for end in later:
        step = characterize(fn, start, end, k, bound)
        if step is None:
            raise ValueError(f"%{start} to %{end} isn't a sum of fields")
        steps.append(step)
        start, bound = end, max(sum(bound for _ in t) for t in step.terms)
    last = steps[-1]
    if any(last.terms[1:]) or sorted(last_terms(steps)) != list(range(fn.width // k)):
        raise ValueError("the result isn't one sum of every field")
    return Plan(layers, k, steps, spec)


def last_terms(steps: list[Step]) -> list[int]:
    """Which of the first cut's fields the result adds up, with repeats."""
    current = [[i] for i in range(steps[0].inputs)]
    for step in steps:
        current = [[c for i in t for c in current[i]] for t in step.terms]
    return current[0]


# ------------------------------------------------------------------------------------------------------------
# Lemmas: what they say, as Lean, and where they live.


def key(text: str) -> str:
    return hashlib.sha256(" ".join(text.split()).encode()).hexdigest()[:10]


@dataclass
class Lemma:
    kind: str
    statement: str  # the theorem's type, with `{name}` and, for a step, `{bound}` to fill in
    proof: str
    bound: int | None = None
    needed: int | None = None
    imports: tuple[str, ...] = ("Std.Tactic.BVDecide",)
    doc: str = ""
    opens: str = ""
    tool: str = "lemmas.py"
    key: str = field(init=False)

    def __post_init__(self) -> None:
        self.key = key(self.statement)

    @property
    def name(self) -> str:
        return f"{self.kind}_{self.key}"

    @property
    def module(self) -> str:
        return f"Lemma_{self.name}"

    @property
    def full(self) -> str:
        return f"LemmaReuse.Store.{self.name}"

    def source(self, bound: int | None = None) -> str:
        bound = self.bound if bound is None else bound
        body = self.statement.format(name=self.name, bound=bound)
        doc = self.doc.format(bound=bound)
        return (
            "".join(f"import {m}\n" for m in self.imports)
            + (f"\nopen {self.opens}\n" if self.opens else "")
            + f"\n/-! Saved by prototypes/lemma-reuse/{self.tool}. -/\n\nnamespace LemmaReuse.Store\n\n"
            + f"/-- {doc} -/\n{body} := by\n{self.proof}\n\nend LemmaReuse.Store\n"
        )


def concat(parts: list[str]) -> str:
    """Fields, highest first, as Lean's `++` wants them."""
    return " ++ ".join(parts)


def field_terms(k: int, n: int, var: str = "a") -> str:
    return concat([f"LemmaReuse.field {var} {k} {i}" for i in reversed(range(n))])


def layer_lemma(fn: Function, start: tuple[str, int] | None, end: tuple[str, int]) -> Lemma:
    """`end`'s fields are the input's counts, from the input itself, or from `start` once that's known."""
    env = {fn.param: "a"}
    if start is not None:
        env[start[0]] = f"({field_terms(start[1], fn.width // start[1])})"
    lhs = render(fn, end[0], env, fn.width)
    rhs = field_terms(end[1], fn.width // end[1])
    return Lemma(
        "layer",
        f"theorem {{name}} (a : BitVec {fn.width}) :\n    {lhs} =\n      {rhs}",
        "  simp only [LemmaReuse.field, Nat.reduceMul]\n"
        f"  bv_decide (config := {{ timeout := {LEMMA_SOLVER_SECONDS} }})",
        imports=("Count",),
        doc=f"At {fn.width} bits, each {end[1]}-bit field holds its count of set bits"
        + (f", given each {start[1]}-bit field does." if start else "."),
    )


def split_lemma(fn: Function, k: int, spec: str, result: int) -> Lemma:
    n = fn.width // k
    total = " + ".join(f"LemmaReuse.field a {k} {i}" for i in range(n))
    simp = "LemmaReuse.fieldSum, BitVec.ofNat_eq_ofNat, BitVec.zero_add"
    if result == fn.width and not spec.startswith("BitVec.setWidth"):
        simp += ", BitVec.setWidth_eq"
    return Lemma(
        "split",
        f"theorem {{name}} (a : BitVec {fn.width}) :\n    {spec} =\n      BitVec.setWidth {result} ({total})",
        f"  have h := LemmaReuse.cpop_fieldSum a {k} {n} {result} rfl (by decide)\n"
        f"  simp only [{simp}] at h\n  exact h",
        imports=("Count",),
        doc=f"A {fn.width}-bit population count is the sum of its {k}-bit fields' counts. "
        "An instance of `LemmaReuse.cpop_fieldSum`, which holds at every width.",
    )


def step_lemma(fn: Function, step: Step) -> Lemma:
    xs = [f"x{i}" for i in range(step.inputs)]
    lhs = render(fn, step.end, {step.start: f"({concat(list(reversed(xs)))})"}, fn.nodes[step.end].width)
    out = [
        f"({' + '.join(xs[i] for i in sorted(t, reverse=True))})"
        if len(t) > 1
        else xs[t[0]]
        if t
        else f"0#{step.k}"
        for t in step.terms
    ]
    width = fn.nodes[step.end].width
    if step.end == fn.ret and not any(step.terms[1:]):
        rhs = f"BitVec.setWidth {width} {out[0]}"
    else:
        rhs = concat(list(reversed(out)))
    # Named with `_`: at the widest bound, `x ≤ 255#8` holds of everything, and nothing reads it.
    hyps = " ".join(f"(_h{i} : x{i} ≤ {{bound}}#{step.k})" for i in range(step.inputs))
    return Lemma(
        "step",
        f"theorem {{name}} {{{{{' '.join(xs)} : BitVec {step.k}}}}} {hyps} :\n    {lhs} =\n      {rhs}",
        f"  bv_decide (config := {{ timeout := {LEMMA_SOLVER_SECONDS} }})",
        bound=step.widest,
        needed=step.needed,
        doc=f"{step.inputs} fields of {step.k} bits, each at most {{bound}}, added without carrying.",
    )


class Store:
    """Lemmas that checked, each a Lean module, with what each says and where it came from in `index.json`.

    The index only says where to look. What's imported from here is checked again by Lean, and by the
    kernel."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.index_path = path / "index.json"
        self.index: dict[str, Any] = (
            json.loads(self.index_path.read_text()) if self.index_path.exists() else {"lemmas": {}}
        )

    def find(self, lemma: Lemma) -> dict[str, Any] | None:
        """A lemma saying this, under hypotheses no stronger than `lemma.needed` asks for."""
        entry = self.index["lemmas"].get(lemma.key)
        if entry is None:
            return None
        if lemma.needed is not None and entry["bound"] < lemma.needed:
            return None
        return entry

    def add(self, lemma: Lemma, bound: int | None, seconds: float, goal: str) -> dict[str, Any]:
        """Saves a lemma that checked. One saying the same under stronger hypotheses, which a goal needing
        more has outgrown, is replaced, and whoever used it is kept, since this one says at least as much."""
        self.path.mkdir(parents=True, exist_ok=True)
        before = self.index["lemmas"].get(lemma.key, {})
        (self.path / f"{lemma.module}.lean").write_text(lemma.source(bound))
        entry = {
            "name": lemma.full,
            "module": lemma.module,
            "kind": lemma.kind,
            "statement": lemma.statement.format(name=lemma.name, bound=bound),
            "bound": bound,
            "needed": lemma.needed,
            "check_seconds": round(seconds, 2),
            "mined_by": before.get("mined_by", goal),
            "used_by": list(dict.fromkeys([*before.get("used_by", []), goal])),
        }
        self.index["lemmas"][lemma.key] = entry
        self.save()
        return entry

    def used(self, lemma_key: str, goal: str) -> None:
        users = self.index["lemmas"][lemma_key]["used_by"]
        if goal not in users:
            users.append(goal)
            self.save()

    def save(self) -> None:
        self.index_path.write_text(json.dumps(self.index, indent=2, ensure_ascii=False) + "\n")


# ------------------------------------------------------------------------------------------------------------
# Lean.


@dataclass
class Use:
    """What became of a lemma a goal needs: whether it's proved, whether it came from the store, and how long
    it took to check here."""

    lemma: "Lemma"
    status: str
    origin: str
    seconds: float
    note: str = ""


@dataclass
class Checked:
    ok: bool
    seconds: float
    status: str  # proved, timeout or failed
    output: str


class Lean:
    """Compiles modules into one directory, in parallel, skipping what compiled before from the same text."""

    def __init__(self, build: Path, repo: Path = ROOT) -> None:
        """`repo` is the checkout whose `IRLean` the modules import."""
        self.build = build
        self.repo = repo
        self.memory = os.environ.get("LEAN_MAX_MB") or "8000"
        self.env = {**os.environ, "LEAN_PATH": f"{build}:{repo}/.lake/build/lib/lean"}
        self.jobs = int(os.environ.get("LEAN_JOBS", "4"))

    def compile(
        self,
        module: str,
        text: str,
        fresh: bool = False,
        extra: str = "",
        strict: bool = True,
        timeout: int = PROCESS_SECONDS,
    ) -> Checked:
        source = self.build / f"{module}.lean"
        olean = self.build / f"{module}.olean"
        stamp = self.build / f"{module}.sha"
        digest = hashlib.sha256((text + extra).encode()).hexdigest()
        if not fresh and olean.exists() and stamp.exists() and stamp.read_text() == digest:
            return Checked(True, 0.0, "proved", "cached")
        source.write_text(text)
        stamp.unlink(missing_ok=True)
        started = time.monotonic()
        try:
            result = subprocess.run(
                [
                    "lean",
                    *(["-DwarningAsError=true"] if strict else []),
                    "-M",
                    self.memory,
                    "-s",
                    "65536",
                    "-R",
                    str(self.build),
                    "-o",
                    str(olean),
                    str(source),
                ],
                cwd=self.repo,
                env=self.env,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return Checked(False, time.monotonic() - started, "timeout", f"no answer in {timeout}s")
        seconds = time.monotonic() - started
        output = result.stdout + result.stderr
        if result.returncode == 0:
            stamp.write_text(digest)
            return Checked(True, seconds, "proved", output)
        first_error = next((line for line in output.splitlines() if ": error" in line), output[:300])
        return Checked(False, seconds, "timeout" if LIMIT.search(first_error) else "failed", output)

    def map(
        self,
        jobs: list[tuple[str, str]],
        extra: str = "",
        fresh: bool = False,
        strict: bool = True,
        workers: int | None = None,
    ) -> list[Checked]:
        with concurrent.futures.ThreadPoolExecutor(workers or self.jobs) as pool:
            return list(pool.map(lambda j: self.compile(j[0], j[1], fresh, extra, strict), jobs))


# ------------------------------------------------------------------------------------------------------------
# A goal, from start to finish.


@dataclass
class Goal:
    theorem: str
    target: str
    symbol: str
    rewrite: Path

    @property
    def rw(self) -> str:
        """The rewrite's module, named as tests/superopt.py names them."""
        return "Rw" + self.target.removeprefix("Crt")


def load_goals(path: Path) -> list[Goal]:
    config = tomllib.loads(path.read_text())
    return [
        Goal(g["theorem"], g["target"], g["symbol"], (path.parent / g["rewrite"]).resolve())
        for g in config["goal"]
    ]


def claim(goal: Goal, fn: Function, lean_name: str) -> str:
    return f"∀ (a : BitVec {fn.width}), {goal.rw}.{lean_name} (some a) = {goal.target}.{lean_name} (some a)"


def statement(goal: Goal, fn: Function, lean_name: str) -> str:
    return (
        f"theorem {goal.theorem} (a : BitVec {fn.width}) :\n"
        f"    {goal.rw}.{lean_name} (some a) = {goal.target}.{lean_name} (some a)"
    )


def head(goal: Goal, lean_name: str) -> list[str]:
    """How the original proof starts, which runs both functions to the values they return."""
    return [
        f"  llvm_exec {goal.rw}.{lean_name}",
        f"  llvm_exec {goal.target}.{lean_name}",
        "  apply IRLean.result_congr",
    ]


def goal_module(goal: Goal, fn: Function, lean_name: str, imports: list[str], tactics: list[str]) -> str:
    return (
        "".join(f"import {m}\n" for m in [goal.target, f"{goal.rw}", "Kit", *imports])
        + f"\nnamespace LemmaReuse\n\n{statement(goal, fn, lean_name)} := by\n"
        + "\n".join(head(goal, lean_name) + tactics)
        + "\n\nend LemmaReuse\n"
    )


def instantiate(lemma: Lemma, exprs: list[str]) -> str:
    """A step lemma at the fields the goal has there, with each bound left to `bv_decide`, from what's known
    of the first cut's fields."""
    named = " ".join(f"(x{i} := {e})" for i, e in enumerate(exprs))
    return f"{lemma.full} {named} {' '.join('(by bv_decide)' for _ in exprs)}"


def assemble(fn: Function, p: Plan, layers: list[Lemma], split: Lemma, steps: list[Lemma]) -> list[str]:
    """Continues the original proof where `bv_decide` gave up: the first cut's value becomes its fields'
    counts, so does the rewrite's population count, each count becomes a variable with what's known of it, and
    each step rewrites the next value until both sides are sums of the same variables."""
    n = fn.width // p.k
    tactics = [f"  rw [{lemma.full} a]" for lemma in layers]
    tactics.append(f"  rw [{split.full} a]")
    tactics += [f"  have h{i} := LemmaReuse.field_le a {p.k} {i}" for i in range(n)]
    tactics += [f"  generalize LemmaReuse.field a {p.k} {i} = c{i} at *" for i in range(n)]
    exprs = [f"c{i}" for i in range(n)]
    for step, lemma in zip(p.steps, steps, strict=True):
        tactics.append(f"  rw [{instantiate(lemma, exprs)}]")
        exprs = [
            f"({' + '.join(exprs[i] for i in sorted(t, reverse=True))})"
            if len(t) > 1
            else exprs[t[0]]
            if t
            else f"0#{p.k}"
            for t in step.terms
        ]
    tactics += ["  congr 1", "  ac_rfl"]
    return tactics


def ensure_support(lean: Lean) -> str:
    """Compiles the seeds every lemma and goal stands on. Returns their hash, which a lemma's cached olean
    depends on."""
    digest = hashlib.sha256()
    for path in SEEDS:
        text = path.read_text()
        # Each seed imports the ones before it, so its .olean depends on them too.
        checked = lean.compile(path.stem, text, extra=digest.hexdigest())
        if not checked.ok:
            raise RuntimeError(f"{path.name} didn't compile:\n{checked.output[:3000]}")
        digest.update(text.encode())
    return digest.hexdigest()


def generate(pipeline: Pipeline, goal: Goal, targets: dict[str, Any], work: Path) -> tuple[str, str, str]:
    """Compiles and translates clang's code for the goal, and the rewrite, into `work`. Returns both as IR,
    and the function's Lean name."""
    translated = pipeline.generate(targets[goal.target], work)
    ok, lean_name = translated.get(goal.symbol, (False, "not in the IR"))
    if not ok:
        raise RuntimeError(f"ir-lean left out {goal.symbol}: {lean_name}")
    module = f"{goal.rw}"
    subprocess.run(
        [
            str(pipeline.tool),
            str(goal.rewrite),
            "--namespace",
            module,
            "-o",
            str(work / f"{module}.lean"),
            "--no-code",
        ],
        check=True,
        capture_output=True,
    )
    pipeline.lean(work, "-R", str(work), "-o", str(work / f"{module}.olean"), str(work / f"{module}.lean"))
    return (work / f"{goal.target}.ll").read_text(), goal.rewrite.read_text(), lean_name


def alive(goal: Goal, work: Path, smt_ms: int) -> dict[str, Any]:
    import alive as alive2

    started = time.monotonic()
    result = subprocess.run(
        [
            "alive-tv",
            "--disable-undef-input",
            f"--smt-to={smt_ms}",
            str(work / f"{goal.target}.ll"),
            str(goal.rewrite),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    return {
        "smt_timeout_ms": smt_ms,
        "verdict": alive2.verdict(result.stdout),
        "seconds": round(time.monotonic() - started, 1),
    }


def prove(
    goal: Goal, store: Store, lean: Lean, pipeline: Pipeline, targets: dict[str, Any], args: Any
) -> dict:
    started = time.monotonic()
    report: dict[str, Any] = {
        "goal": goal.theorem,
        "gaps": [],
        "notes": [],
        "timings": {},
        "assumptions": ASSUMPTIONS,
    }
    work = lean.build
    ir, rewrite_ir, lean_name = generate(pipeline, goal, targets, work)
    report["timings"]["generate"] = round(time.monotonic() - started, 1)
    try:
        fn = parse(ir, goal.symbol)
    except ValueError as error:
        report["gaps"].append(f"not split: {error}")
        report["seconds"] = round(time.monotonic() - started, 1)
        return report
    report["statement"] = claim(goal, fn, lean_name)
    if args.alive:
        report["alive"] = alive(goal, work, args.alive)

    if args.baseline:
        tactics = [f"  bv_decide (config := {{ timeout := {args.baseline} }})"]
        checked = lean.compile(
            f"Mono_{goal.theorem}",
            goal_module(goal, fn, lean_name, [], tactics),
            fresh=True,
            # The solver gets what was asked for, and the rest of Lean its usual limit on top.
            timeout=args.baseline + PROCESS_SECONDS,
        )
        report["baseline"] = {
            "solver_seconds": args.baseline,
            "status": checked.status,
            "seconds": round(checked.seconds, 1),
        }

    try:
        p = plan(fn, parse(rewrite_ir, goal.symbol))
    except ValueError as error:
        report["gaps"].append(f"not split: {error}")
        report["seconds"] = round(time.monotonic() - started, 1)
        return report
    report["cuts"] = {
        "layers": [f"%{n} ({k}-bit fields)" for n, k in p.layers],
        "steps": [f"%{s.start} -> %{s.end}" for s in p.steps],
    }
    seeds = hashlib.sha256("".join(path.read_text() for path in SEEDS).encode()).hexdigest()
    used: list[dict[str, Any]] = []
    lemmas_started = time.monotonic()

    def check_all(lemmas: list[Lemma]) -> list[Use]:
        """Each lemma from the store if it's there, and otherwise checked here, as general as it holds."""
        results: list[Use | None] = [None] * len(lemmas)
        found = [(i, entry) for i, lemma in enumerate(lemmas) if (entry := store.find(lemma)) is not None]
        stored = lean.map(
            [(e["module"], (store.path / f"{e['module']}.lean").read_text()) for _, e in found], seeds
        )
        for (i, entry), checked in zip(found, stored, strict=True):
            lemma = lemmas[i]
            if checked.ok:
                general = lemma.needed is not None and entry["bound"] > lemma.needed
                lemma.bound = entry["bound"]
                origin = "store, under weaker hypotheses" if general else "store"
                results[i] = Use(lemma, "proved", origin, checked.seconds)
            else:
                # A stale entry, say from another Lean. It's found and checked again, as if it weren't there.
                report["notes"].append(
                    f"{entry['module']} is in the store but didn't check: {checked.status}"
                )
        jobs, where = [], []
        for i, lemma in enumerate(lemmas):
            if results[i] is None:
                jobs.append((lemma.module, lemma.source()))
                where.append(i)
        for i, checked in zip(where, lean.map(jobs, extra=seeds), strict=True):
            lemma, note = lemmas[i], ""
            if not checked.ok and lemma.needed is not None and lemma.bound != lemma.needed:
                # Simulation said it holds this generally, and Lean didn't agree. Ask for what's needed.
                note = f"Lean rejected it for fields up to {lemma.bound}: {first_error(checked.output)}"
                lemma.bound = lemma.needed
                retry = lean.compile(lemma.module, lemma.source(), extra=seeds)
                retry = Checked(retry.ok, checked.seconds + retry.seconds, retry.status, retry.output)
                checked = retry  # noqa: PLW2901
            if checked.ok:
                store.add(lemma, lemma.bound, checked.seconds, goal.theorem)
            elif not note:
                note = first_error(checked.output)
            results[i] = Use(lemma, checked.status, "mined", checked.seconds, note)
        return [r for r in results if r is not None]

    def record(use: Use, gap: bool = True) -> None:
        lemma = use.lemma
        used.append(
            {
                "lemma": lemma.full,
                "kind": lemma.kind,
                "source": use.origin,
                "status": use.status,
                "check_seconds": round(use.seconds, 2),
                **({"bound": lemma.bound, "needed": lemma.needed} if lemma.needed is not None else {}),
                **({"note": use.note} if use.note else {}),
            }
        )
        if use.status == "proved" and use.origin.startswith("store"):
            store.used(lemma.key, goal.theorem)
        if use.status != "proved" and gap:
            report["gaps"].append(f"{lemma.full}: {use.status}: {use.note}")

    # The first cut, from the input, in one lemma. If that runs out of time, or with --finest, a lemma for
    # each cut on the way, each from the one before.
    layers: list[Lemma] | None = None
    if not args.finest:
        whole = layer_lemma(fn, None, p.layers[-1])
        (use,) = check_all([whole])
        if use.status == "proved" or use.status != "timeout" or len(p.layers) == 1:
            record(use)
            layers = [whole] if use.status == "proved" else []
        else:
            use.note = f"split at {', '.join('%' + n for n, _ in p.layers[:-1])}"
            record(use, gap=False)
    if layers is None:
        chain = [layer_lemma(fn, p.layers[i - 1] if i else None, p.layers[i]) for i in range(len(p.layers))]
        uses = check_all(chain)
        for use in uses:
            record(use)
        layers = chain
    split = split_lemma(fn, p.k, p.spec, fn.result)
    steps = [step_lemma(fn, s) for s in p.steps]
    for use in check_all([split, *steps]):
        record(use)
    report["lemmas"] = used
    report["timings"]["lemmas"] = round(time.monotonic() - lemmas_started, 1)
    mined = [u for u in used if u["source"] == "mined" and u["status"] == "proved"]
    report["reuse"] = {
        "lemmas": len(used),
        "from_store": sum(u["source"].startswith("store") for u in used),
        "mined": len(mined),
        "mined_check_seconds": round(sum(u["check_seconds"] for u in mined), 2),
    }
    if report["gaps"]:
        report["seconds"] = round(time.monotonic() - started, 1)
        return report

    # The used layer lemmas, and not ones a split replaced.
    used = [u for u in used if u["status"] == "proved"]
    imports = ["Count", *dict.fromkeys(lemma.module for lemma in [*layers, split, *steps])]
    tactics = assemble(fn, p, layers, split, steps)
    module = f"Goal_{goal.theorem}"
    checked = lean.compile(module, goal_module(goal, fn, lean_name, imports, tactics), fresh=True)
    report["proof"] = {"status": checked.status, "seconds": round(checked.seconds, 1)}
    if not checked.ok:
        report["gaps"].append(f"the assembled proof didn't check: {first_error(checked.output)}")
        report["seconds"] = round(time.monotonic() - started, 1)
        return report
    args.proofs.mkdir(parents=True, exist_ok=True)
    shutil.copy(work / f"{module}.lean", args.proofs / f"{module}.lean")

    audit_started = time.monotonic()
    theorems = "\n".join(f"LemmaReuse.{goal.theorem} {m}.{lean_name}" for m in (goal.target, f"{goal.rw}"))
    try:
        axioms = pipeline.axioms(work, module, f"{goal.target} {goal.rw}", theorems)
        replayed = [module, *imports[1:], "Count", "Bits", "Kit"]
        with concurrent.futures.ThreadPoolExecutor(lean.jobs) as pool:
            list(pool.map(lambda m: pipeline.replay(work, m), replayed))
        report["audit"] = {
            "axioms": axioms,
            "replayed": replayed,
            "seconds": round(time.monotonic() - audit_started, 1),
        }
    except RuntimeError as error:
        report["gaps"].append(f"the audit failed: {str(error)[:1000]}")
    report["seconds"] = round(time.monotonic() - started, 1)
    return report


def first_error(output: str) -> str:
    return next((line for line in output.splitlines() if ": error" in line), output[:500])[:500]


def summary(reports: list[dict[str, Any]]) -> str:
    lines = []
    for r in reports:
        lines.append(f"{r['goal']}: {r.get('proof', {}).get('status', 'not proved')}, {r['seconds']}s in all")
        if "statement" in r:
            lines.append(f"  {r['statement']}")
        if "alive" in r:
            a = r["alive"]
            lines.append(f"  alive2 at {a['smt_timeout_ms']} ms: {a['verdict']} in {a['seconds']}s")
        if "baseline" in r:
            b = r["baseline"]
            lines.append(
                f"  one bv_decide call, {b['solver_seconds']}s for the solver: "
                f"{b['status']} in {b['seconds']}s"
            )
        for u in r.get("lemmas", []):
            bound = f", fields <= {u['bound']} (needed {u['needed']})" if "bound" in u else ""
            source = u["source"] if u["status"] == "proved" else f"{u['source']}, {u['status']}"
            note = f"  [{u['note']}]" if "note" in u else ""
            lines.append(f"  {source:>30}  {u['check_seconds']:>5}s  {u['lemma']}{bound}{note}")
        if "reuse" in r:
            u = r["reuse"]
            lines.append(
                f"  {u['from_store']} of {u['lemmas']} lemmas from the store, {u['mined']} mined, "
                f"{u['mined_check_seconds']}s checking those, {r['timings']['lemmas']}s for this step"
            )
        if "proof" in r:
            lines.append(f"  continued proof: {r['proof']['status']} in {r['proof']['seconds']}s")
        if "audit" in r:
            lines.append(f"  axioms: {r['audit']['axioms']}")
        lines += [f"  note: {n}" for n in r.get("notes", [])]
        lines += [f"  gap: {g}" for g in r["gaps"]]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--goals", type=Path, default=GOALS, help="a goals file like goals.toml")
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prove")
    p.add_argument("theorems", nargs="*", help="goals from goals.toml, in this order. All of them by default")
    p.add_argument("--store", type=Path, default=STORE)
    p.add_argument("--report", type=Path)
    p.add_argument("--proofs", type=Path, default=HERE / "proofs", help="where to write each finished proof")
    p.add_argument("--tool", type=Path, default=ROOT / "build" / "ir-lean")
    p.add_argument(
        "--baseline",
        type=int,
        nargs="?",
        const=10,
        default=0,
        help="first try one bv_decide call, giving its solver this many seconds (10, its default)",
    )
    p.add_argument("--alive", type=int, default=0, help="also ask Alive2, with this SMT timeout in ms")
    p.add_argument("--finest", action="store_true", help="cut the first step at every cut point")
    p.add_argument(
        "--fresh", action="store_true", help="check the store's lemmas again, as a new checkout would"
    )
    r = sub.add_parser("rewrite", help="what the search finds, compared with the goal's rewrite")
    r.add_argument("theorem")
    r.add_argument("--write", action="store_true", help="write it to the goal's rewrite instead")
    r.add_argument("--tool", type=Path, default=ROOT / "build" / "ir-lean")
    args = parser.parse_args()

    goals = {g.theorem: g for g in load_goals(args.goals)}
    config = tomllib.loads((PROOFS / "targets.toml").read_text())
    targets = {t["module"]: t for t in config["target"]}
    BUILD.mkdir(parents=True, exist_ok=True)
    pipeline = Pipeline(args.tool.resolve(), BUILD, config)

    if args.command == "rewrite":
        goal = goals[args.theorem]
        pipeline.generate(targets[goal.target], BUILD)
        found = find_rewrite(parse((BUILD / f"{goal.target}.ll").read_text(), goal.symbol))
        if args.write:
            goal.rewrite.write_text(found)
        elif not goal.rewrite.exists() or goal.rewrite.read_text() != found:
            print(f"FAIL  the search now finds something else for {goal.symbol}:\n{found}")
            return 1
        print(f"ok    the search finds {goal.rewrite.relative_to(ROOT)} for {goal.symbol}")
        return 0

    chosen = [goals[t] for t in args.theorems] if args.theorems else list(goals.values())
    store = Store(args.store.resolve())
    lean = Lean(BUILD)
    if args.fresh:
        # Everything's checked again, including what's in the store, as in a new checkout.
        for stale in BUILD.glob("Lemma_*"):
            stale.unlink()
    ensure_support(lean)
    reports = [prove(goal, store, lean, pipeline, targets, args) for goal in chosen]
    print(summary(reports))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(reports, indent=2, ensure_ascii=False) + "\n")
    return 0 if all(r.get("proof", {}).get("status") == "proved" and not r["gaps"] for r in reports) else 1


def find_rewrite(fn: Function) -> str:
    """What tests/superopt.py's search finds for `fn`, run on its IR here rather than natively, since ctypes
    has no 128-bit integers. A result narrower than the argument is truncated, which the search can't say."""
    from superopt import inputs, search

    values = inputs(fn.width)
    goal = tuple(evaluate(fn, v)[fn.ret] if isinstance(fn.ret, str) else fn.ret for v in values)
    found = search(goal, values, fn.width)
    if found is None:
        raise SystemExit(f"nothing that small agrees with @{fn.symbol}")
    body = "\n".join(found.ir)
    value = found.value
    for i, name in enumerate(re.findall(r"^%v\d+", body, re.M)):
        body = re.sub(rf"{name}\b", f"%r{i}", body)
        value = re.sub(rf"{name}\b", f"%r{i}", value)
    lines = [f"  {line}" for line in body.splitlines()]
    if fn.result != fn.width:
        lines.append(f"  %t = trunc i{fn.width} {value} to i{fn.result}")
        value = "%t"
    w = fn.width
    declares = sorted(
        {
            f"declare i{w} @llvm.{m}.i{w}(i{w}{', i1' if m in ('ctlz', 'cttz') else ''})"
            for m in re.findall(r"@llvm\.(\w+)\.", body)
        }
    )
    return (
        f"; What tests/superopt.py's search finds for {fn.symbol}, with a truncation to the\n"
        "; result's width. prototypes/lemma-reuse/lemmas.py proves it does what clang left.\n"
        'target triple = "x86_64-unknown-linux-gnu"\n\n'
        + "".join(f"{d}\n" for d in declares)
        + f"\ndefine i{fn.result} @{fn.symbol}(i{w} noundef %a) {{\nentry:\n"
        + "\n".join(lines)
        + f"\n  ret i{fn.result} {value}\n}}\n"
    )


if __name__ == "__main__":
    sys.exit(main())
