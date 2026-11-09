#!/usr/bin/env python3
"""Chunk 1's G2: the peephole folds' models against the pinned `opt`, E3's measure, the scoreboard, and the
lemma store's admissions. docs/rewrite-proofs.md says what each shows and what it rests on.

- compare: each registered fold's model, run in Lean with `Oracle.none`, against the pinned `opt` on the
  instructions LLVM's own regression tests hold, and on generated ones. A model that fires where `opt`
  doesn't, or answers otherwise, is a mismatch and fails the command. `--write` records the result in
  tests/passes-proofs/peephole/compared/, keyed by a hash of the model's sources, for `score`.
- measure: E3's numbers for each site's theorem: its time, each module's wall time and peak memory through
  tools/measure.py's pool of heavy jobs, the stored lemmas each proof uses, and the kernel's time with and
  without a stored lemma's proof inlined.
- score: chunk 1's G2 per pass, rewrites proved for every input out of those inventoried. A rewrite counts
  only if its theorem exists, rests on the standard three axioms, is used by its fold's `sound` theorem, and
  its model's comparison is recorded for the sources it has now. `--check` fails if a registry lists a site
  that doesn't count.
- store: a family's value lemmas offered to the lemma store with tools/store/store.py, one family at a time.

Needs `nix develop` and `lake build`. `compare` reads LLVM_PROJECT_SRC's regression tests and runs `opt`.
Writes only to build/peephole, apart from what `--write` and `store` are for.

usage: tests/peephole.py compare [--family F] [--write] [--strict] [--out FILE] [--keep]
       tests/peephole.py measure [--family F] [--reps N] [--out FILE] [--keep]
       tests/peephole.py score [--check] [--out FILE]
       tests/peephole.py store --family F [--dry-run]
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import datetime
import fcntl
import json
import os
import re
import shutil
import sys
import tempfile
import time
from collections import Counter, defaultdict
from collections.abc import Generator, Iterator, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, proc, schemas  # noqa: E402
from irlean import lean as leanlib  # noqa: E402
from irlean import verdict as core  # noqa: E402

PEEPHOLE = ROOT / "tests" / "passes-proofs" / "peephole"
FOLDS = PEEPHOLE / "folds"
COMPARED = PEEPHOLE / "compared"
HARNESS = ROOT / "tests" / "peephole" / "Harness.lean"
INVENTORY = ROOT / "tests" / "llvm_scope" / "rewrites"
INDEX = ROOT / "store" / "index.json"
STORE = ROOT / "tools" / "store" / "store.py"
MEASURE = ROOT / "tools" / "measure.py"
WORK = ROOT / "build" / "peephole"
LEAN_MB = int(os.environ.get("PEEPHOLE_LEAN_MB", "4096"))
TIMEOUT = int(os.environ.get("PEEPHOLE_TIMEOUT", "1200"))
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
JSON_LINE = "HARNESS-JSON "
# Each pass: its inventory file, and the directory of its regression tests under llvm/test/Transforms.
PASSES = {
    "instsimplify": ("instsimplify.json", "InstSimplify"),
    "instcombine": ("instcombine.json", "InstCombine"),
    "aggressive-instcombine": ("aggressive-instcombine.json", "AggressiveInstCombine"),
    "reassociate": ("reassociate.json", "Reassociate"),
}
# What a rewrite that needs each waits for. docs/rewrite-inventory.md.
WAITS_FOR = {"fp": "SEM-05", "memory": "F4", "calls": "the external-calls lane"}
# The lemma store's families whose lemmas are rewrites, rather than refinement's laws or LangRef's contracts.
REWRITE_FAMILIES = ("generic-rewrites", "peephole-")


class HarnessError(Exception):
    """Something kept a step from deciding anything."""


class Unknown(HarnessError):
    """A time or memory limit stopped a step, so its result is unknown: never a pass."""


def today() -> str:
    return datetime.date.today().isoformat()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)


# ------------------------------------------------------------------------------------------------------------
# Registries, modules and the inventory

BINOPS = "add sub mul udiv sdiv urem srem shl lshr ashr and or xor".split()
PREDS = "eq ne ugt uge ult ule sgt sge slt sle".split()
UNARY = "ctpop bitreverse bswap ctlz cttz abs".split()
FLAGGED = {"ctlz", "cttz", "abs"}
BINARY = "umin umax smin smax uadd.sat usub.sat sadd.sat ssub.sat".split()
FUNNEL = ["fshl", "fshr"]
CASTS = ["zext", "sext", "trunc"]
# Every opcode `Term` can hold, as a registry names it: an instruction's opcode, or an intrinsic's name
# without `llvm.`.
OPCODES = [*BINOPS, "icmp", "select", *CASTS, "freeze", *UNARY, *BINARY, *FUNNEL]


def opcode_name(name: str) -> str:
    """An opcode as a registry may write it, `llvm.uadd.sat` or `uadd_sat`, as OPCODES has it."""
    n = name.lower().removeprefix("llvm.").replace("_", ".")
    return {f"{s}sat": f"{s}.sat" for s in ("uadd", "usub", "sadd", "ssub")}.get(n, n)


@dataclass
class Registry:
    path: Path
    data: dict[str, Any]

    @property
    def family(self) -> str:
        return self.data["family"]

    @property
    def pass_(self) -> str:
        return self.data["pass"]

    @property
    def modules(self) -> list[str]:
        return self.data["modules"]

    @property
    def entries(self) -> list[dict[str, Any]]:
        return self.data["entries"]

    @property
    def folds(self) -> dict[str, dict[str, Any]]:
        return self.data["folds"]

    def sites(self) -> dict[str, tuple[str, str]]:
        """Each site the registry lists as proved, with its fold and the fold's `sound` theorem."""
        return {s: (fold, f["sound"]) for fold, f in self.folds.items() for s in f["sites"]}


def registry_problems(path: Path, data: dict[str, Any]) -> list[str]:
    """What's wrong with a registry's shape, by tests/passes-proofs/peephole/README.md."""
    problems = []
    if data.get("family") != path.stem:
        problems.append(f"its family is {data.get('family')!r}, not its file's name, {path.stem!r}")
    if data.get("pass") not in PASSES:
        problems.append(f"pass {data.get('pass')!r} isn't one of {', '.join(PASSES)}")
    if not isinstance(data.get("modules"), list) or not data["modules"]:
        problems.append("no modules")
    for e in data.get("entries", []):
        if not re.fullmatch(r"Peephole(\.[A-Za-z_][A-Za-z0-9_']*)+", str(e.get("fold", ""))):
            problems.append(f"entry {e.get('fold')!r} isn't a name in Peephole")
        for op in e.get("opcodes", []):
            if opcode_name(op) not in OPCODES:
                problems.append(f"{e.get('fold')}: opcode {op!r} isn't one Term holds: {', '.join(OPCODES)}")
        if e.get("opt", data.get("pass")) not in PASSES:
            problems.append(f"{e.get('fold')}: opt pass {e.get('opt')!r} isn't one of {', '.join(PASSES)}")
    for fold, f in data.get("folds", {}).items():
        if not isinstance(f.get("sound"), str) or not isinstance(f.get("sites"), list):
            problems.append(f"fold {fold} needs a `sound` theorem and a list of `sites`")
    for key in ("unproved", "rests_on", "covers"):
        if not isinstance(data.get(key, {}), dict):
            problems.append(f"`{key}` isn't an object")
    # `covers`: for a site the inventory says needs more than integers, the types its proof covers too.
    for site, types in data.get("covers", {}).items() if isinstance(data.get("covers", {}), dict) else []:
        if not isinstance(types, list) or not set(types) <= {"int", *WAITS_FOR}:
            problems.append(f"covers: {site}: {types!r} isn't a list of {', '.join(['int', *WAITS_FOR])}")
    if not isinstance(data.get("lemmas", []), list):
        problems.append("`lemmas` isn't a list")
    return problems


def registries(family: str | None = None) -> list[Registry]:
    out = []
    for path in sorted(FOLDS.glob("*.json")):
        data = schemas.read(path, schemas.PEEPHOLE_FOLDS)
        if problems := registry_problems(path, data):
            raise HarnessError(f"{rel(path)}: " + "; ".join(problems))
        if family is None or data["family"] == family:
            out.append(Registry(path, data))
    if family is not None and not out:
        raise HarnessError(f"no registry for family {family} in {rel(FOLDS)}")
    return out


def module_file(module: str) -> Path:
    return PEEPHOLE.joinpath(*module.split(".")).with_suffix(".lean")


def library_modules() -> list[str]:
    """Every module of the `Peephole` library, which `lake build Peephole` builds."""
    return sorted(
        ".".join(p.relative_to(PEEPHOLE).with_suffix("").parts)
        for p in (PEEPHOLE / "Peephole").rglob("*.lean")
    )


def imports_of(path: Path) -> list[str]:
    return re.findall(r"^import\s+(\S+)", path.read_text(), re.M)


def model_sources(modules: list[str]) -> list[Path]:
    """The source of each module of `Peephole` that `modules` import, themselves included."""
    seen: set[str] = set()
    todo = list(modules)
    while todo:
        m = todo.pop()
        if m in seen or not m.startswith("Peephole.") or not module_file(m).is_file():
            continue
        seen.add(m)
        todo += imports_of(module_file(m))
    return sorted(module_file(m) for m in seen)


def model_hash(reg: Registry) -> str:
    """What a comparison is keyed by: the registry and the source of every module of the library its model
    imports, so a change to any of them needs the model compared again."""
    return hashing.files_hash(ROOT, [reg.path, *model_sources(reg.modules)])


def inventory() -> dict[str, list[dict[str, Any]]]:
    """Each pass's rewrites, from tests/llvm_scope/rewrites."""
    return {p: schemas.read(INVENTORY / f, schemas.REWRITES)["rewrites"] for p, (f, _) in PASSES.items()}


# ------------------------------------------------------------------------------------------------------------
# Running Lean, opt and lake


def lean_env(*dirs: Path, **extra: str) -> dict[str, str]:
    """The environment for a Lean process reading modules from `dirs`, then from the directories
    PEEPHOLE_OVERLAY lists, then from the library lake built. A test puts a changed module in an overlay to
    see that each command notices."""
    overlay = [Path(p) for p in os.environ.get("PEEPHOLE_OVERLAY", "").split(os.pathsep) if p]
    return {**leanlib.env(*dirs, *overlay), **extra}


def run(argv: Sequence[str | Path], env: dict[str, str] | None = None, timeout: float = TIMEOUT) -> proc.Ran:
    """Runs a command from the repo's root. A limit is Unknown, never a result."""
    try:
        r = proc.run([str(a) for a in argv], cwd=ROOT, env=env, timeout=timeout)
    except FileNotFoundError as e:
        raise HarnessError(f"{argv[0]} isn't on PATH: run inside nix develop") from e
    if r.limit is not None:
        raise Unknown(f"{Path(str(argv[0])).name} stopped at {r.limit}")
    if r.exit != 0 and (r.exit < 0 or leanlib.is_limit(r.output)):
        raise Unknown(f"{Path(str(argv[0])).name} hit a limit: {r.output[-600:]}")
    return r


def harness_json(out: str) -> Any:
    for line in out.splitlines():
        if line.startswith(JSON_LINE):
            return json.loads(line[len(JSON_LINE) :])
    raise HarnessError(f"the harness printed no result:\n{out[-3000:]}")


def lake_built(targets: list[str]) -> core.Step:
    """That lake has nothing left to build for `targets`, so what's read is what the sources say."""
    r = run(["lake", "build", "--no-build", *targets])
    if r.exit != 0:
        raise HarnessError(f"run `lake build {' '.join(targets)}` first:\n{r.output[-2000:]}")
    return core.Step.of("lake build --no-build", r)


@contextlib.contextmanager
def workdir(keep: bool) -> Generator[Path]:
    WORK.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(dir=WORK, prefix="run-"))
    try:
        yield work
    finally:
        if keep:
            print(f"kept {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)


def build_harness(work: Path) -> None:
    """tests/peephole/Harness.lean, compiled into `work` as `PeepholeHarness`."""
    shutil.copy(HARNESS, work / "PeepholeHarness.lean")
    r = run(
        leanlib.argv(
            LEAN_MB, "-R", work, "-o", work / "PeepholeHarness.olean", work / "PeepholeHarness.lean"
        ),
        lean_env(work),
    )
    if r.exit != 0:
        raise HarnessError(f"tests/peephole/Harness.lean doesn't compile:\n{r.output[-3000:]}")


def facts(work: Path, request: dict[str, Any], modules: list[str], pool: str | None = None) -> dict[str, Any]:
    """What PeepholeHarness.facts says, in one Lean process importing `modules`, through the pool of heavy
    jobs if `pool` names it."""
    (work / "request.json").write_text(json.dumps(request))
    driver = work / "Facts.lean"
    driver.write_text(
        "".join(f"import {m}\n" for m in ["PeepholeHarness", *modules]) + "\nrun_meta PeepholeHarness.facts\n"
    )
    argv, env = leanlib.argv(LEAN_MB, driver), lean_env(work, PEEPHOLE_REQUEST=str(work / "request.json"))
    if pool is not None:
        record, said = pooled(pool, argv, env, LEAN_MB + 1000, TIMEOUT)
        if record["exit"] != 0:
            raise HarnessError(f"the facts query failed:\n{said[-3000:]}")
        return harness_json(said)
    r = run(argv, env)
    if r.exit != 0:
        raise HarnessError(f"the facts query failed:\n{r.output[-3000:]}")
    return harness_json(r.out)


def pooled(
    label: str, argv: Sequence[str | Path], env: dict[str, str], mb: int, timeout: int
) -> tuple[dict, str]:
    """Runs `argv` through tools/measure.py, holding a slot in the machine's pool of heavy jobs, and returns
    its measurement record and what it printed."""
    with tempfile.TemporaryDirectory(dir=WORK) as tmp:
        out, log = Path(tmp) / "record.jsonl", Path(tmp) / "log"
        cmd = [sys.executable, MEASURE, "run", "--label", label, "--heavy", "--max-tree-rss-mb", str(mb)]
        cmd += ["--timeout", str(timeout), "--out", out, "--log", log, "--", *argv]
        r = run(cmd, env, timeout=timeout + 3700)
        if not out.is_file():
            raise HarnessError(f"tools/measure.py recorded nothing for {label}: {r.output[-2000:]}")
        record = json.loads(out.read_text().splitlines()[-1])
        said = log.read_text(errors="replace") if log.is_file() else ""
    if record["outcome"] in ("time_limit", "resource_limit") or (
        record["exit"] != 0 and leanlib.is_limit(said)
    ):
        raise Unknown(f"{label}: {record['outcome']}, {said[-400:]}")
    return record, said


# ------------------------------------------------------------------------------------------------------------
# compare: operands from LLVM's tests and generated ones


VALUE = r'(%[-\w$.]+|%"[^"]*"|-?\d+|true|false|poison|undef)'
RE_DEF = re.compile(r'^\s+(%[-\w$.]+|%"[^"]*") = (.*)$')
RE_BIN = re.compile(rf"^({'|'.join(BINOPS)})((?: (?:nuw|nsw|exact|disjoint))*) i(\d+) {VALUE}, {VALUE}$")
RE_ICMP = re.compile(rf"^icmp( samesign)? ({'|'.join(PREDS)}) i(\d+) {VALUE}, {VALUE}$")
RE_SELECT = re.compile(rf"^select i1 {VALUE}, i(\d+) {VALUE}, i(\d+) {VALUE}$")
RE_CAST = re.compile(rf"^(zext|sext|trunc)((?: (?:nneg|nuw|nsw))*) i(\d+) {VALUE} to i(\d+)$")
RE_FREEZE = re.compile(rf"^freeze i(\d+) {VALUE}$")
RE_CALL = re.compile(r"^(?:(?:tail|musttail|notail) )?call (?:.*? )?i(\d+) @llvm\.([a-z.]+?)\.i\d+\((.*)\)$")
RE_ARG = re.compile(rf"^i(\d+)(?: [a-z_]+(?:\([^)]*\))?)* {VALUE}$")
RE_DEFINE = re.compile(r'^define [^@]*@("[^"]*"|[-\w$.]+)\(')
# How deep into an operand a case looks. Below that an instruction is an argument, to the model and to `opt`.
MAX_DEPTH = 5
# The most generated cases for one opcode of one entry point, taken evenly from all of them.
GENERATED_CAP = 12000

# Each kind of operand, and the keys of its operands, in order.
OPERANDS = {
    "bin": ("a", "b"),
    "icmp": ("a", "b"),
    "select": ("c", "t", "e"),
    "zext": ("a",),
    "sext": ("a",),
    "trunc": ("a",),
    "freeze": ("a",),
    "un": ("a",),
    "bi": ("a", "b"),
    "fsh": ("a", "b", "c"),
}


def split_args(text: str) -> list[str]:
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
            continue
        depth += ch in "([{<"
        depth -= ch in ")]}>"
        cur += ch
    return [*out, cur.strip()] if cur.strip() else out


def parse_instruction(rhs: str) -> tuple[str, int, dict[str, Any], list[tuple[int, str]]] | None:
    """An instruction `opt -S` printed, as (kind, width, attributes, [(width, operand)]), if `Term` can hold
    it: a scalar integer one."""
    rhs = re.split(r",\s*!", rhs, maxsplit=1)[0]
    rhs = re.sub(r"\s+#\d+$", "", rhs).strip()
    if m := RE_BIN.match(rhs):
        w = int(m[3])
        return "bin", w, {"op": m[1], **dict.fromkeys(m[2].split(), True)}, [(w, m[4]), (w, m[5])]
    if m := RE_ICMP.match(rhs):
        v = int(m[3])
        return "icmp", 1, {"p": m[2], "samesign": bool(m[1])}, [(v, m[4]), (v, m[5])]
    if m := RE_SELECT.match(rhs):
        w = int(m[2])
        return ("select", w, {}, [(1, m[1]), (w, m[3]), (w, m[5])]) if m[4] == m[2] else None
    if m := RE_CAST.match(rhs):
        return m[1], int(m[5]), dict.fromkeys(m[2].split(), True), [(int(m[3]), m[4])]
    if m := RE_FREEZE.match(rhs):
        return "freeze", int(m[1]), {}, [(int(m[1]), m[2])]
    if m := RE_CALL.match(rhs):
        w, name = int(m[1]), m[2]
        args = [RE_ARG.match(a) for a in split_args(m[3])]
        if not all(args):
            return None
        ops = [(int(a[1]), a[2]) for a in args if a]
        if name in FLAGGED and len(ops) == 2 and ops[1] in ((1, "true"), (1, "false")):
            return "un", w, {"f": name, "flag": ops[1][1] == "true"}, ops[:1]
        if name in UNARY and name not in FLAGGED and len(ops) == 1:
            return "un", w, {"f": name}, ops
        if name in BINARY and len(ops) == 2:
            return "bi", w, {"f": name}, ops
        if name in FUNNEL and len(ops) == 3:
            return "fsh", w, {"left": name == "fshl"}, ops
    return None


def opcode_of(kind: str, attrs: dict[str, Any]) -> str:
    if kind == "bin":
        return attrs["op"]
    if kind in ("un", "bi"):
        return attrs["f"]
    if kind == "fsh":
        return "fshl" if attrs["left"] else "fshr"
    return kind


class Builder:
    """Turns one instruction of a function `opt -S` printed into an operand tree. An argument, an instruction
    `Term` can't hold, and one deeper than MAX_DEPTH become `var`s, so the case's own function has an argument
    there, and the model and `opt` see the same thing."""

    def __init__(self, defs: dict[str, str]) -> None:
        self.defs = defs
        self.ids: dict[str, int] = {}

    def ident(self, name: str) -> int:
        return self.ids.setdefault(name, len(self.ids))

    def operand(self, w: int, text: str, depth: int, stack: frozenset[str]) -> dict[str, Any]:
        if text in ("poison", "undef"):
            return {"k": text, "w": w}
        if text in ("true", "false") and w == 1:
            return {"k": "const", "w": 1, "c": "1" if text == "true" else "0"}
        if re.fullmatch(r"-?\d+", text):
            return {"k": "const", "w": w, "c": str(int(text) % (1 << w))}
        inst = parse_instruction(self.defs[text]) if text in self.defs else None
        if inst is None:
            return {"k": "var", "w": w, "id": self.ident(text)}
        if inst[1] != w or depth >= MAX_DEPTH or text in stack:
            # An instruction cut off here may be a node of the tree elsewhere, nearer the root, so as an
            # argument it's another value, with an identity of its own.
            return {"k": "var", "w": w, "id": self.ident(f"{text}#cut")}
        return self.node(text, inst, depth, stack)

    def node(self, name: str, inst: tuple, depth: int, stack: frozenset[str]) -> dict[str, Any]:
        kind, w, attrs, ops = inst
        out = {"k": kind, "w": w, "id": self.ident(name), **attrs}
        for key, (ow, text) in zip(OPERANDS[kind], ops, strict=True):
            out[key] = self.operand(ow, text, depth + 1, stack | {name})
        return out


def functions(ir: str) -> Iterator[tuple[str, list[str]]]:
    name, body = None, []
    for line in ir.split("\n"):
        if m := RE_DEFINE.match(line):
            name, body = m[1], []
        elif line == "}" and name is not None:
            yield name, body
            name = None
        elif name is not None:
            body.append(line)


def harvest_file(path: Path, opcodes: set[str]) -> tuple[list[tuple[str, dict[str, Any]]], str | None]:
    """Every instruction in a regression test whose opcode is one of `opcodes`, as an operand tree, with where
    it is. The test is read as `opt -S` prints it, so each instruction has one form."""
    r = run(["opt", "-S", "-passes=verify", str(path)], timeout=300)
    if r.exit != 0:
        return [], (r.err.strip().splitlines() or ["opt can't read it"])[0][:200]
    out = []
    for fname, body in functions(r.out):
        defs = {m[1]: m[2] for line in body if (m := RE_DEF.match(line))}
        for name, rhs in defs.items():
            inst = parse_instruction(rhs)
            if inst is not None and opcode_of(inst[0], inst[2]) in opcodes:
                out.append((f"{path.name}:@{fname}:{name}", Builder(defs).node(name, inst, 0, frozenset())))
    return out, None


def canonical(term: dict[str, Any]) -> dict[str, Any]:
    """The tree with its identities numbered in the order they're first met, so two instructions that are the
    same shape, with the same sharing, are the same case."""
    ids: dict[int, int] = {}

    def walk(t: dict[str, Any]) -> dict[str, Any]:
        out = {k: v for k, v in t.items() if k not in OPERANDS.get(t["k"], ())}
        if "id" in t:
            out["id"] = ids.setdefault(t["id"], len(ids))
        for key in OPERANDS.get(t["k"], ()):
            out[key] = walk(t[key])
        return out

    return walk(term)


@dataclass
class Case:
    name: str
    entry: str
    pass_: str
    opcode: str
    term: dict[str, Any]
    # The regression tests it was found in, or none if it's generated.
    files: list[str] = field(default_factory=list)
    where: str = ""
    # Whether its function passes the root's operands to a call too, so each has more than one use. InstCombine's
    # cases come both ways, since its folds ask whether an operand has one use. docs/rewrite-proofs.md.
    keep: bool = True


def harvest(entries: list[tuple[str, str, set[str]]], src: Path) -> tuple[list[Case], dict[str, Any]]:
    """Cases from each pass's regression tests, for each entry point `(fold, pass, opcodes)`."""
    by_pass: dict[str, set[str]] = defaultdict(set)
    for _, pass_, ops in entries:
        by_pass[pass_] |= ops
    found: dict[str, list[tuple[str, str, dict[str, Any]]]] = defaultdict(list)
    stats: dict[str, Any] = {"files": 0, "unread": {}, "instructions": 0}
    for pass_, ops in sorted(by_pass.items()):
        files = sorted((src / "llvm" / "test" / "Transforms" / PASSES[pass_][1]).glob("*.ll"))
        stats["files"] += len(files)
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, os.cpu_count() or 1)) as pool:
            found_in = pool.map(harvest_file, files, [ops] * len(files))
            for path, (roots, problem) in zip(files, found_in, strict=True):
                if problem:
                    stats["unread"][path.name] = problem
                for where, term in roots:
                    found[pass_].append((path.name, where, term))
    cases = []
    for fold, pass_, ops in entries:
        unique: dict[str, Case] = {}
        for fname, where, term in found[pass_]:
            op = opcode_of(term["k"], term)
            if op not in ops:
                continue
            stats["instructions"] += 1
            key = json.dumps(canonical(term), sort_keys=True)
            if key not in unique:
                unique[key] = Case(f"h{len(unique)}", fold, pass_, op, canonical(term), [], where)
            if fname not in unique[key].files:
                unique[key].files.append(fname)
        cases += unique.values()
    return cases, stats


class Gen:
    """Operands built to match each fold's patterns against each other, at several widths, as #47's
    comparison of `simplifyAddInst` had for `add`."""

    def __init__(self) -> None:
        self.n = 100

    def fresh(self) -> int:
        self.n += 1
        return self.n

    @staticmethod
    def var(i: int, w: int) -> dict[str, Any]:
        return {"k": "var", "w": w, "id": i}

    @staticmethod
    def c(v: int, w: int) -> dict[str, Any]:
        return {"k": "const", "w": w, "c": str(v % (1 << w))}

    def bin(self, op: str, a: dict[str, Any], b: dict[str, Any], **flags: bool) -> dict[str, Any]:
        return {"k": "bin", "w": a["w"], "id": self.fresh(), "op": op, **flags, "a": a, "b": b}

    def copy(self, t: dict[str, Any]) -> dict[str, Any]:
        return {**t, "id": self.fresh()}

    def leaves(self, w: int) -> list[dict[str, Any]]:
        consts = {v % (1 << w): None for v in (0, 1, -1, 1 << (w - 1), (1 << (w - 1)) - 1, 2)}
        return [
            self.var(0, w),
            self.var(1, w),
            *(self.c(v, w) for v in consts),
            {"k": "poison", "w": w},
            {"k": "undef", "w": w},
        ]

    def instructions(self, w: int) -> list[dict[str, Any]]:
        v0, v1, c = self.var(0, w), self.var(1, w), self.c
        out = [self.bin("sub", c(0, w), v0), self.bin("xor", v0, c(-1, w)), self.bin("xor", c(-1, w), v0)]
        out += [
            self.bin(op, v0, v1) for op in ("sub", "and", "or", "xor", "add", "mul", "shl", "lshr", "ashr")
        ]
        out += [
            self.bin("sub", v1, v0),
            self.bin("xor", v0, c(1 << (w - 1), w)),
            self.bin("and", v0, c(1, w)),
        ]
        return out

    def derived(self, p: dict[str, Any], q: dict[str, Any]) -> list[dict[str, Any]]:
        """Operands the folds look for next to `p`: `~p`, `-p`, `q - p`, `p & q` and the like, and an
        instruction like `p` that isn't `p`."""
        w, c = p["w"], self.c
        out = [
            self.bin("sub", q, p),
            self.bin("sub", p, q),
            self.bin("xor", p, c(-1, w)),
            self.bin("xor", c(-1, w), p),
        ]
        out += [self.bin("sub", c(0, w), p), self.bin("sub", c(0, w), p, nsw=True)]
        out += [self.bin(op, x, y) for op in ("and", "or", "xor", "add") for x, y in ((p, q), (q, p))]
        if p["k"] == "bin":
            out += [self.copy(p), self.bin("sub", q, self.copy(p))]
            if p["op"] == "sub":
                out.append(self.bin("sub", p["b"], p["a"]))
        return out

    def pairs(self, w: int, small: bool = False) -> list[tuple[dict[str, Any], dict[str, Any]]]:
        insts = self.instructions(w)
        base = self.leaves(w) + (insts[:6] if small else insts)
        out = [(a, b) for a in base for b in base]
        v0, v1 = self.var(0, w), self.var(1, w)
        for p in [v0, v1, *insts[:3], *insts[3:6]]:
            for d in self.derived(p, v1 if p is not v1 else v0):
                out += [(p, d), (d, p)]
        return out


# The flags each binary operator takes, each set of them a case.
WRAPS = ({}, {"nsw": True}, {"nuw": True}, {"nuw": True, "nsw": True})
FLAGS: dict[str, tuple[dict[str, bool], ...]] = {
    **dict.fromkeys(("add", "sub", "mul", "shl"), WRAPS),
    **dict.fromkeys(("udiv", "sdiv", "lshr", "ashr"), ({}, {"exact": True})),
    "or": ({}, {"disjoint": True}),
}


def generated_terms(op: str) -> list[dict[str, Any]]:
    """The generated roots for one opcode."""
    g = Gen()
    out: list[dict[str, Any]] = []
    if op in BINOPS:
        for w in (1, 8, 32):
            for a, b in g.pairs(w):
                out += [
                    {"k": "bin", "w": w, "id": g.fresh(), "op": op, **f, "a": a, "b": b}
                    for f in FLAGS.get(op, ({},))
                ]
    elif op == "icmp":
        for w in (1, 8):
            for a, b in g.pairs(w, small=True):
                for p in PREDS:
                    out += [
                        {"k": "icmp", "w": 1, "id": g.fresh(), "p": p, "samesign": s, "a": a, "b": b}
                        for s in (False, True)
                    ]
    elif op == "select":
        conds = [g.c(1, 1), g.c(0, 1), {"k": "poison", "w": 1}, {"k": "undef", "w": 1}, g.var(2, 1)]
        conds += [
            g.bin("xor", g.var(2, 1), g.c(1, 1)),
            {"k": "freeze", "w": 1, "id": g.fresh(), "a": g.var(2, 1)},
        ]
        for v in (8,):
            conds += [
                {"k": "icmp", "w": 1, "id": g.fresh(), "p": p, "samesign": False, "a": g.var(3, v), "b": b}
                for p in ("eq", "ne", "ult", "slt")
                for b in (g.var(4, v), g.c(0, v))
            ]
        for w in (1, 8, 32):
            vals = g.leaves(w) + g.instructions(w)[:4]
            out += [
                {"k": "select", "w": w, "id": g.fresh(), "c": c, "t": t, "e": e}
                for c in conds
                for t in vals
                for e in vals
            ]
    elif op in CASTS:
        shapes = [(1, 8), (8, 32), (1, 32)] if op != "trunc" else [(8, 1), (32, 8), (32, 1)]
        for src, dst in shapes:
            ops = g.leaves(src) + g.instructions(src)[:6]
            for other in (dst, 16):
                if other != src:
                    kind = "trunc" if other > src else "zext"
                    ops += [{"k": kind, "w": src, "id": g.fresh(), "a": g.var(3, other)}]
                    if other < src:
                        ops += [{"k": "sext", "w": src, "id": g.fresh(), "a": g.var(3, other)}]
            flags = {
                "zext": [{}, {"nneg": True}],
                "sext": [{}],
                "trunc": [{}, {"nuw": True}, {"nsw": True}, {"nuw": True, "nsw": True}],
            }[op]
            out += [{"k": op, "w": dst, "id": g.fresh(), **f, "a": a} for a in ops for f in flags]
    elif op == "freeze":
        for w in (1, 8, 32):
            ops = g.leaves(w) + g.instructions(w)
            ops += [{"k": "freeze", "w": w, "id": g.fresh(), "a": a} for a in g.leaves(w)]
            out += [{"k": "freeze", "w": w, "id": g.fresh(), "a": a} for a in ops]
    elif op in UNARY:
        for w in (16, 32) if op == "bswap" else (1, 8, 32):
            ops = g.leaves(w) + g.instructions(w)
            ops += [
                {"k": "un", "w": w, "id": g.fresh(), "f": op, "flag": False, "a": a} for a in g.leaves(w)[:2]
            ]
            for flag in (False, True) if op in FLAGGED else (False,):
                out += [{"k": "un", "w": w, "id": g.fresh(), "f": op, "flag": flag, "a": a} for a in ops]
    elif op in BINARY:
        for w in (1, 8, 32):
            for a, b in g.pairs(w, small=True):
                out.append({"k": "bi", "w": w, "id": g.fresh(), "f": op, "a": a, "b": b})
    elif op in FUNNEL:
        for w in (8, 32):
            vals = [
                g.var(0, w),
                g.var(1, w),
                g.var(2, w),
                g.c(0, w),
                g.c(1, w),
                g.c(-1, w),
                g.c(w, w),
                {"k": "poison", "w": w},
                {"k": "undef", "w": w},
            ]
            out += [
                {"k": "fsh", "w": w, "id": g.fresh(), "left": op == "fshl", "a": a, "b": b, "c": c}
                for a in vals
                for b in vals
                for c in vals
            ]
    if len(out) > GENERATED_CAP:
        step = len(out) / GENERATED_CAP
        out = [out[int(i * step)] for i in range(GENERATED_CAP)]
    return out


# ------------------------------------------------------------------------------------------------------------
# compare: each case as a function of its own, through opt


def const_text(c: int, w: int) -> str:
    c %= 1 << w
    if w == 1:
        return "true" if c else "false"
    return str(c - (1 << w) if c >> (w - 1) else c)


INTRINSIC_ARITY = {**dict.fromkeys(UNARY, 1), **dict.fromkeys(BINARY, 2), **dict.fromkeys(FUNNEL, 3)}


class Emitter:
    """One case as a function: its arguments are the `var`s, each instruction is emitted once, operands first,
    a call keeps the root's operands alive whatever happens to the root, and the root, `%r`, is returned. So
    every line but the root and the `ret` has to come out of `opt` as it went in.

    With `keep` false there's no such call, so each operand has the uses the tree gives it, and InstCombine's
    folds that need an operand with one use can fire. With `probe` the root is a call to an opaque function of
    the same operands, which no pass folds: what `opt` does to the operands before it reaches the root."""

    def __init__(self) -> None:
        self.declares: set[str] = set()

    def function(
        self, n: int, term: dict[str, Any], keep: bool = True, probe: bool = False
    ) -> tuple[str, dict[int, str]]:
        args: dict[int, int] = {}
        names: dict[int, str] = {}
        body: list[str] = []

        def value(t: dict[str, Any]) -> str:
            k = t["k"]
            if k == "const":
                return const_text(int(t["c"]), t["w"])
            if k in ("poison", "undef"):
                return k
            if k == "var":
                # One identity is one value, of one type: two would be one `Value *` to the model.
                if args.setdefault(t["id"], t["w"]) != t["w"]:
                    raise HarnessError(f"case {n}: argument {t['id']} at widths {args[t['id']]} and {t['w']}")
                names[t["id"]] = f"%v{t['id']}"
                return f"%v{t['id']}"
            if t["id"] not in names:
                text = self.instruction(t, value)
                names[t["id"]] = f"%n{t['id']}"
                body.append(f"  %n{t['id']} = {text}")
            return f"%n{t['id']}"

        operands = [(t["w"], value(t)) for t in (term[key] for key in OPERANDS[term["k"]])]
        uses = ", ".join(f"i{w} {v}" for w, v in operands)
        if probe:
            self.declares.add(f"declare i{term['w']} @probe.i{term['w']}(...)")
            root = f"call i{term['w']} (...) @probe.i{term['w']}({uses})"
        else:
            root = self.instruction(term, value)
        names[term["id"]] = "%r"
        params = ", ".join(f"i{w} %v{i}" for i, w in sorted(args.items()))
        lines = [f"define i{term['w']} @c{n}({params}) {{", *body]
        lines += [f"  call void (...) @use({uses})"] if keep else []
        lines += [f"  %r = {root}", f"  ret i{term['w']} %r", "}"]
        return "\n".join(lines), names

    def instruction(self, t: dict[str, Any], value: Any) -> str:
        k, w = t["k"], t["w"]
        ops = [value(t[key]) for key in OPERANDS[k]]
        if k == "bin":
            flags = "".join(f" {f}" for f in ("nuw", "nsw", "exact", "disjoint") if t.get(f))
            return f"{t['op']}{flags} i{w} {ops[0]}, {ops[1]}"
        if k == "icmp":
            return (
                f"icmp{' samesign' if t.get('samesign') else ''} {t['p']} i{t['a']['w']} {ops[0]}, {ops[1]}"
            )
        if k == "select":
            return f"select i1 {ops[0]}, i{w} {ops[1]}, i{w} {ops[2]}"
        if k in CASTS:
            flags = "".join(f" {f}" for f in ("nneg", "nuw", "nsw") if t.get(f))
            return f"{k}{flags} i{t['a']['w']} {ops[0]} to i{w}"
        if k == "freeze":
            return f"freeze i{w} {ops[0]}"
        name = opcode_of(k, t)
        args = [f"i{w} {o}" for o in ops]
        types = [f"i{w}"] * len(ops)
        if name in FLAGGED:
            args.append(f"i1 {'true' if t.get('flag') else 'false'}")
            types.append("i1")
        self.declares.add(f"declare i{w} @llvm.{name}.i{w}({', '.join(types)})")
        return f"call i{w} @llvm.{name}.i{w}({', '.join(args)})"

    def module(self, functions: list[str]) -> str:
        return "\n".join([*functions, "declare void @use(...)", *sorted(self.declares)]) + "\n"


def opt_functions(ir: str) -> dict[str, list[str]]:
    return dict(functions(ir))


def expected_text(answer: dict[str, Any], names: dict[int, str]) -> str | None:
    """What the root's uses should name after the model's answer, or None if it builds new instructions,
    which this comparison doesn't read."""
    k, w = answer["k"], answer["w"]
    if k == "const":
        return const_text(int(answer["c"]), w)
    if k == "poison":
        return "poison"
    if k != "old":
        return None
    t = answer["t"]
    if t in ("poison", "undef"):
        return t
    if "const" in t:
        return const_text(int(t["const"]), w)
    return names.get(t["node"], f"<no value with id {t['node']}>")


# The flags each opcode can carry, as LangRef has them: a model's `Flags` may set others, which mean nothing.
FLAGS_OF = {
    **dict.fromkeys(("add", "sub", "mul", "shl"), ("nuw", "nsw")),
    **dict.fromkeys(("udiv", "sdiv", "lshr", "ashr"), ("exact",)),
    "or": ("disjoint",),
}
RE_LOCAL = re.compile(r'%[-\w$.]+|%"[^"]*"')
RE_ID = re.compile(r"%([vn])(\d+)\b")


def one_use(text: str) -> list[int]:
    """The identities of the arguments and instructions of a case's function, as Emitter names them, that have
    exactly one use in it: what `V->hasOneUse()` answers for each."""
    count: Counter[int] = Counter()
    for line in text.splitlines()[1:]:
        m = RE_DEF.match(line)
        count.update(int(x[2]) for x in RE_ID.finditer(m[2] if m else line))
    return sorted(i for i, k in count.items() if k == 1)


def new_ir_function(text: str, answer: dict[str, Any], names: dict[int, str], em: Emitter) -> str:
    """A case's function with the root replaced by what the model answered: its new instructions, in order,
    operands first, where the root was, and the `ret` naming the answer."""
    lines: list[str] = []

    def value(r: dict[str, Any]) -> str:
        k, w = r["k"], r["w"]
        if k in ("old", "const", "poison"):
            said = expected_text(r, names)
            assert said is not None
            return said
        if k == "bin":
            r = {**r, **{f: bool(r.get(f)) and f in FLAGS_OF.get(r["op"], ()) for f in ("nuw", "nsw", "exact", "disjoint")}}
        text = em.instruction(r, value)
        lines.append(f"  %m{len(lines)} = {text}")
        return f"%m{len(lines) - 1}"

    top = value(answer)
    body = text.splitlines()
    root = [i for i, x in enumerate(body) if x.startswith("  %r = ")]
    if len(root) != 1:
        raise HarnessError(f"no root in {body[0]}")
    w = answer["w"]
    return "\n".join([*body[: root[0]], *lines, f"  ret i{w} {top}", "}"])


def expansion(lines: list[str]) -> str | None:
    """What a function returns, as one expression: each value an instruction of it defines written out as that
    instruction, its operands written out the same way, down to arguments and constants. Two functions that
    compute the same tree of instructions, whatever they name them and whatever order they're in, have the same
    expansion."""
    defs: dict[str, str] = {}
    for line in lines:
        if m := RE_DEF.match(line):
            rhs = re.split(r",\s*!", m[2], maxsplit=1)[0]
            defs[m[1]] = re.sub(r"\s+#\d+$", "", rhs).strip()
    rets = [x.split()[-1] for x in lines if x.startswith("  ret ")]
    if len(rets) != 1:
        return None
    memo: dict[str, str] = {}

    def go(v: str) -> str:
        if v not in defs:
            return v
        if v not in memo:
            memo[v] = "(" + RE_LOCAL.sub(lambda m: go(m[0]), defs[v]) + ")"
        return memo[v]

    return go(rets[0])


def compare_new_ir(
    case: Case, answer: dict[str, Any], after: list[str], normalized: list[str] | None = None
) -> bool | None:
    """Whether a model's answer that's new IR, as InstCombine's are, is what `opt` answers: the function with
    the root replaced by the answer's instructions, `normalized` after `opt -passes=instcombine`, returns the
    same expression as the case's function after `opt` does, `after`. None if the answer wasn't run through
    `opt`, which leaves the case uncompared. docs/rewrite-proofs.md says what this can and can't tell apart."""
    if normalized is None:
        return None
    want, got = expansion(after), expansion(normalized)
    return want is not None and want == got


@dataclass
class Tally:
    cases: int = 0
    harvested: int = 0
    generated: int = 0
    compared: int = 0
    matched: int = 0
    agreed_no_fold: int = 0
    fired_new_ir: int = 0
    mismatched: int = 0
    delegated: int = 0
    analysis: int = 0
    unexplained: int = 0
    operand_changed: int = 0
    sites: dict[str, dict[str, Any]] = field(default_factory=dict)
    delegated_to: Counter[str] = field(default_factory=Counter)
    mismatches: list[dict[str, Any]] = field(default_factory=list)
    unexplained_cases: list[dict[str, Any]] = field(default_factory=list)
    untagged: list[str] = field(default_factory=list)
    # Each registered fold a compared case's run reached, with the first such case.
    folds_run: dict[str, str] = field(default_factory=dict)

    def site(self, s: str) -> dict[str, Any]:
        return self.sites.setdefault(
            s,
            {
                "fired": 0,
                "matched": 0,
                "mismatched": 0,
                "analysis": 0,
                # The same, in cases with no `undef` anywhere, which is all a proof covers.
                "fired_without_undef": 0,
                "matched_without_undef": 0,
                "files": set(),
            },
        )


def has_undef(t: dict[str, Any]) -> bool:
    """Whether an `undef` is anywhere in the operand."""
    return t["k"] == "undef" or any(has_undef(t[key]) for key in OPERANDS.get(t["k"], ()))


def folded(before: list[str], after: list[str]) -> bool:
    """Whether `opt` replaced the root or changed it in place."""
    root = [x for x in before if x.startswith("  %r = ")]
    rets = [x.split()[-1] for x in after if x.startswith("  ret ")]
    return rets != ["%r"] or [x for x in after if x.startswith("  %r = ")] != root


def unchanged(before: list[str], after: list[str]) -> bool:
    """Whether `opt` left every line of a case's function but the root and the `ret` as it was, so the fold
    saw the operands the model did."""
    keep = [x for x in before if not x.startswith(("  %r = ", "  ret "))]
    return keep == [x for x in after if not x.startswith(("  %r = ", "  ret "))]


def classify(
    case: Case,
    answer: dict[str, Any],
    before: list[str],
    after: list[str],
    names: dict[int, str],
    t: Tally,
    same_operands: bool | None = None,
    normalized: dict[str, list[str]] | None = None,
) -> None:
    """Puts one case's comparison into `t`. `same_operands` says whether `opt` left the root's operands as
    they were when it reached the root, if the caller worked it out, as for InstCombine's cases; otherwise it's
    every line of the function but the root and the `ret` coming out as it went in. `normalized` has the
    function with the root replaced by the model's new IR, after `opt`, for its `"result"` and its
    `"analysis"`."""
    t.cases += 1
    t.harvested += bool(case.files)
    t.generated += not case.files
    rets = [x.split()[-1] for x in after if x.startswith("  ret ")]
    root_after = [x for x in after if x.startswith("  %r = ")]
    root_before = [x for x in before if x.startswith("  %r = ")]
    result = answer["result"]
    normalized = normalized or {}
    if not (unchanged(before, after) if same_operands is None else same_operands):
        t.operand_changed += 1
        return

    def ran() -> None:
        # A fold ran only where the case was compared and agreed: a delegated case says nothing about it.
        for f in answer.get("ran", []):
            t.folds_run.setdefault(f, case.name)

    opt_changed = rets != ["%r"] or root_after != root_before
    ir = "\n".join(before)
    if "delegated" in result:
        t.delegated += 1
        t.delegated_to[result["delegated"]] += 1
        return
    if "null" in result:
        if not opt_changed:
            t.compared += 1
            t.agreed_no_fold += 1
            ran()
            return
        # An analysis explains it only if the model, with the oracle that made it fire, answers what opt does.
        said = None
        if "analysis" in answer:
            value = answer["analysis"]["value"]
            said = expected_text(value, names)
            explained = (
                rets == [said]
                if said is not None
                else compare_new_ir(case, value, after, normalized.get("analysis")) is True
            )
            if explained:
                t.analysis += 1
                t.site(answer["analysis"].get("site") or "unknown")["analysis"] += 1
                return
        t.unexplained += 1
        t.unexplained_cases.append(
            {"case": case.name, "where": case.where, "opt": rets, "model_with_an_analysis": said, "ir": ir}
        )
        return
    site = answer.get("site") or "unknown"
    s = t.site(site)
    s["fired"] += 1
    clean = not has_undef(case.term)
    s["fired_without_undef"] += clean
    s["files"].update(case.files)
    t.compared += 1
    expect = expected_text(result["value"], names)
    ok: bool | None
    if expect is None:
        ok = compare_new_ir(case, result["value"], after, normalized.get("result")) if opt_changed else False
        if ok is None:
            t.fired_new_ir += 1
            return
    else:
        ok = opt_changed and rets == [expect]
    if ok:
        t.matched += 1
        s["matched"] += 1
        s["matched_without_undef"] += clean
        ran()
    else:
        t.mismatched += 1
        s["mismatched"] += 1
        said = expect if expect is not None else json.dumps(result["value"])
        t.mismatches.append(
            {"case": case.name, "where": case.where, "site": site, "model": said, "opt": rets, "ir": ir}
        )


def run_models(
    work: Path, regs: list[Registry], cases: list[Case], watch: dict[str, dict[str, bool]]
) -> tuple[dict[str, dict[str, Any]], list[str], set[str]]:
    """Each case's answer from its entry point, in one Lean process, and the entry points whose sites can't be
    told apart. Each answer also names the registered folds, of every registry, that its run reached."""
    entries = sorted({e["fold"] for r in regs for e in r.entries})
    modules = sorted({m for r in regs for m in r.modules})
    folds = sorted({f for r in registries() for f in r.folds})
    # Entry points have to exist. A registered fold that isn't a constant here is only never seen to run.
    names = lambda xs, q="``": ", ".join(f"{q}{x}" for x in xs)  # noqa: E731
    (work / "Driver.lean").write_text(
        "".join(f"import {m}\n" for m in ["PeepholeHarness", *modules])
        + f"\nrun_meta PeepholeHarness.prepare #[{names(entries)}] #[{names(folds, '`')}]\n\n"
        + "def main (args : List String) : IO UInt32 :=\n"
        + "  PeepholeHarness.runCases PeepholeHarness.Driver.table args\n"
    )
    with (work / "cases.jsonl").open("w") as f:
        for c in cases:
            f.write(json.dumps({"name": c.name, "entry": c.entry, "term": c.term, **watch[c.name]}) + "\n")
    r = run(leanlib.argv(LEAN_MB, "--run", work / "Driver.lean", work / "cases.jsonl"), lean_env(work))
    if r.exit != 0:
        raise HarnessError(f"the models' driver failed:\n{r.output[-4000:]}")
    untagged = [
        line.split(" ", 1)[1] for line in r.output.splitlines() if line.startswith("HARNESS-UNTAGGED ")
    ]
    missing = {
        line.split(" ", 1)[1] for line in r.output.splitlines() if line.startswith("HARNESS-UNWATCHABLE ")
    }
    # Lean prints its messages about the driver on the same stream, before the answers.
    said = [line for line in r.out.splitlines() if line.strip() and not line.startswith(("{", "HARNESS-"))]
    if said:
        print("the driver said:\n  " + "\n  ".join(said[:20]), file=sys.stderr)
    answers = [json.loads(line) for line in r.out.splitlines() if line.startswith("{")]
    return {j["name"]: j for j in answers}, untagged, missing


def comparison_cases(regs: list[Registry], src: Path) -> tuple[list[Case], dict[str, Any]]:
    entries = []
    for r in regs:
        for e in r.entries:
            entries.append((e["fold"], e.get("opt", r.pass_), {opcode_name(o) for o in e["opcodes"]}))
    cases, stats = harvest(entries, src)
    for fold, pass_, ops in entries:
        for op in sorted(ops):
            cases += [
                Case(f"g.{op}.{i}", fold, pass_, op, term) for i, term in enumerate(generated_terms(op))
            ]
    # InstCombine's folds ask whether an operand has one use, so each of its cases comes a second time with no
    # call keeping the root's operands, where they have the uses the tree gives them.
    cases += [
        Case(f"{c.name}.u", c.entry, c.pass_, c.opcode, c.term, c.files, c.where, keep=False)
        for c in cases
        if c.pass_ == "instcombine"
    ]
    return cases, stats


def unchanged_prefix(before: list[str], after: list[str]) -> bool:
    """For a case with the call that keeps the root's operands alive: whether `opt` left every line up to and
    including that call as it was. InstCombine puts what it builds where the root was, after the call, so this
    holds whatever it replaced the root with, where `unchanged` needs the root replaced by one value."""

    def upto(lines: list[str]) -> list[str] | None:
        calls = [i for i, x in enumerate(lines) if x.startswith("  call void (...) @use(")]
        return lines[: calls[0] + 1] if calls else None

    head = upto(before)
    return head is not None and head == upto(after)


def opt_module(path: Path, em: Emitter, functions: list[str], pass_: str) -> tuple[dict, dict]:
    """Each function, as `opt -S` prints it, before and after `-passes=<pass_>`."""
    path.write_text(em.module(functions))
    verified = run(["opt", "-S", "-passes=verify", path])
    optimized = run(["opt", "-S", f"-passes={pass_}", path])
    if verified.exit != 0 or optimized.exit != 0:
        raise HarnessError(
            f"opt refused {path.name} for {pass_}: {verified.err[-2000:]}{optimized.err[-2000:]}"
        )
    return opt_functions(verified.out), opt_functions(optimized.out)


def normalize_new_ir(
    work: Path,
    by_pass: dict[str, list[tuple[int, Case]]],
    answers: dict[str, dict[str, Any]],
    texts: dict[str, str],
    names: dict[str, dict[int, str]],
    declares: dict[str, set[str]],
) -> dict[str, dict[str, list[str]]]:
    """For each case whose model answered new IR, with `Oracle.none` or with an oracle that says yes: its
    function with the root replaced by that IR, after `opt` runs the case's pass on it, by case and by
    `"result"` or `"analysis"`."""
    out: dict[str, dict[str, list[str]]] = defaultdict(dict)
    for pass_, items in by_pass.items():
        em = Emitter()
        em.declares |= declares[pass_]
        fns, keys = [], []
        for n, c in items:
            a = answers[c.name]
            for kind, value in (
                ("result", a["result"].get("value")),
                ("analysis", a.get("analysis", {}).get("value")),
            ):
                if value is None or expected_text(value, names[c.name]) is not None:
                    continue
                fn = new_ir_function(texts[c.name], value, names[c.name], em)
                fns.append(fn.replace(f"@c{n}(", f"@{kind[0]}{n}(", 1))
                keys.append((c.name, kind, f"{kind[0]}{n}"))
        if fns:
            _, post = opt_module(work / f"new-ir-{pass_}.ll", em, fns, pass_)
            for name, kind, fname in keys:
                out[name][kind] = post[fname]
    return out


def compare(args: argparse.Namespace) -> int:
    src = os.environ.get("LLVM_PROJECT_SRC")
    if not src:
        raise HarnessError("LLVM_PROJECT_SRC isn't set: run inside nix develop")
    regs = registries(args.family)
    started = time.monotonic()
    lake_built(sorted({m for r in regs for m in r.modules}))
    version = run(["opt", "--version"]).out
    with workdir(args.keep) as work:
        build_harness(work)
        cases, stats = comparison_cases(regs, Path(src))
        # Each case gets a fresh name for its pass, as the function @c<n> in that pass's module.
        by_pass: dict[str, list[tuple[int, Case]]] = defaultdict(list)
        for n, c in enumerate(cases):
            c.name = f"{c.name}.{n}"
            by_pass[c.pass_].append((n, c))
        before: dict[str, list[str]] = {}
        after: dict[str, list[str]] = {}
        names: dict[str, dict[int, str]] = {}
        texts: dict[str, str] = {}
        declares: dict[str, set[str]] = {}
        # Whether opt left the root's operands as they were when it reached the root, where that isn't every
        # line but the root and the `ret` coming out as it went in: InstCombine's cases.
        same: dict[str, bool] = {}
        for pass_, items in by_pass.items():
            em = Emitter()
            for n, c in items:
                texts[c.name], names[c.name] = em.function(n, c.term, keep=c.keep)
            pre, post = opt_module(work / f"cases-{pass_}.ll", em, [texts[c.name] for _, c in items], pass_)
            declares[pass_] = em.declares
            for n, c in items:
                before[c.name], after[c.name] = pre[f"c{n}"], post[f"c{n}"]
                if c.pass_ == "instcombine" and c.keep:
                    same[c.name] = unchanged_prefix(before[c.name], after[c.name])
            # With no call keeping them, the operands of a case InstCombine folds may be deleted after, so
            # what it does to them first is read from the same function with an opaque call for the root.
            probes = [(n, c) for n, c in items if c.pass_ == "instcombine" and not c.keep]
            if probes:
                pem = Emitter()
                fns = [pem.function(n, c.term, keep=False, probe=True)[0] for n, c in probes]
                ppre, ppost = opt_module(work / f"probes-{pass_}.ll", pem, fns, pass_)
                for n, c in probes:
                    same[c.name] = unchanged(ppre[f"c{n}"], ppost[f"c{n}"])
        # Which folds a run reaches is only looked for in cases whose operands opt left as they were, and the
        # driver needs to know where opt folded the root, to tell which of those are compared. An InstCombine
        # case gives its fold the arguments and instructions with one use in its function.
        watch = {
            c.name: {
                "watch": same.get(c.name, unchanged(before[c.name], after[c.name])),
                "opt_folded": folded(before[c.name], after[c.name]),
                **({"one_use": one_use(texts[c.name])} if c.pass_ == "instcombine" else {}),
            }
            for c in cases
        }
        answers, untagged, missing = run_models(work, regs, cases, watch)
        normalized = normalize_new_ir(work, by_pass, answers, texts, names, declares)
    seconds = time.monotonic() - started
    failed = False
    reports = []
    for reg in regs:
        folds = {e["fold"] for e in reg.entries}
        t = Tally(untagged=[u for u in untagged if u.split(":")[0] in folds])
        for c in cases:
            if c.entry in folds:
                classify(
                    c,
                    answers[c.name],
                    before[c.name],
                    after[c.name],
                    names[c.name],
                    t,
                    same.get(c.name),
                    normalized.get(c.name),
                )
        report = comparison_record(reg, t, stats, version, seconds)
        report["folds_unwatchable"] = sorted(set(reg.folds) & missing)
        reports.append(report)
        print_comparison(report)
        failed |= report["status"] not in ("ok", "no entry points") or (args.strict and t.unexplained > 0)
        if args.write:
            schemas.write(COMPARED / f"{reg.family}.json", report, schemas.PEEPHOLE_COMPARISON, indent=2)
            print(f"      recorded in {rel(COMPARED / f'{reg.family}.json')}")
    if args.out:
        args.out.write_text(json.dumps(reports, indent=2) + "\n")
    print(f"{'FAIL' if failed else 'ok  '}  compare, in {seconds:.1f} s")
    return 1 if failed else 0


def comparison_record(
    reg: Registry, t: Tally, stats: dict[str, Any], version: str, seconds: float
) -> dict[str, Any]:
    listed = reg.sites()
    sites = {
        s: {**v, "files": sorted(v["files"]), "registered": s in listed} for s, v in sorted(t.sites.items())
    }
    # A fold ran if a compared case's run reached it, or one of its steps fired and matched opt.
    fold_of = {s: f for r in registries() for s, (f, _) in r.sites().items()}
    ran = dict(t.folds_run)
    for s, v in sorted(t.sites.items()):
        if v["matched"] and s in fold_of:
            ran.setdefault(fold_of[s], f"a case where {s} fired")
    if not reg.entries:
        status = "no entry points"
    elif t.mismatched:
        status = "mismatch"
    else:
        status = "ok" if t.compared > 0 else "nothing compared"
    return {
        "schema": schemas.PEEPHOLE_COMPARISON,
        "family": reg.family,
        "registry": rel(reg.path),
        "sources": model_hash(reg),
        "opt": (re.search(r"LLVM version (\S+)", version) or [None, "unknown"])[1],
        "date": today(),
        "status": status,
        "cases": {
            k: getattr(t, k)
            for k in (
                "cases",
                "harvested",
                "generated",
                "compared",
                "matched",
                "agreed_no_fold",
                "fired_new_ir",
                "mismatched",
                "delegated",
                "analysis",
                "unexplained",
                "operand_changed",
            )
        },
        "delegated_to": dict(sorted(t.delegated_to.items())),
        "regression_tests": {"read": stats["files"] - len(stats["unread"]), "unread": len(stats["unread"])},
        "sites": sites,
        "not_exercised": sorted(set(listed) - {s for s, v in t.sites.items() if v["fired"]}),
        "folds_run": dict(sorted(ran.items())),
        "folds_not_run": sorted(set(reg.folds) - set(ran)),
        "untagged": t.untagged,
        "mismatches": t.mismatches[:50],
        "unexplained": t.unexplained_cases[:50],
        "seconds": round(seconds, 1),
    }


def print_comparison(r: dict[str, Any]) -> None:
    c, t = r["cases"], r["regression_tests"]
    mark = "ok  " if r["status"] in ("ok", "no entry points") else "FAIL"
    lines = [
        f"{mark}  {r['family']}: {c['cases']} cases, {c['harvested']} from {t['read']} of LLVM's regression "
        f"tests ({t['unread']} opt can't read) and {c['generated']} generated",
        f"compared {c['compared']}: {c['matched']} where the model fires and opt agrees, "
        f"{c['agreed_no_fold']} where neither folds, {c['mismatched']} mismatched",
        f"not compared: {c['delegated']} delegated, {c['operand_changed']} with an operand changed first, "
        f"{c['fired_new_ir']} building new IR",
        f"opt folds and the model with Oracle.none doesn't: {c['analysis']} an analysis explains, "
        f"{c['unexplained']} nothing explains",
    ]
    for s, v in r["sites"].items():
        more = f" and {len(v['files']) - 6} more" if len(v["files"]) > 6 else ""
        lines.append(
            f"{s}: fired {v['fired']} ({v['fired_without_undef']} with no undef), matched {v['matched']}, "
            f"mismatched {v['mismatched']}, analysis {v['analysis']}; "
            f"tests: {', '.join(v['files'][:6]) + more or 'none'}"
        )
    if r["not_exercised"]:
        lines.append(f"never fired: {', '.join(r['not_exercised'])}")
    lines += [f"sites unknown for {u}" for u in r["untagged"]]
    lines.append(f"folds a compared run reached: {', '.join(r['folds_run']) or 'none'}")
    if r["folds_not_run"]:
        lines.append(f"this family's folds no compared run reached: {', '.join(r['folds_not_run'])}")
    if r.get("folds_unwatchable"):
        lines.append(
            "folds that can't be watched, as neither the fold nor <fold>.steps defines a result or steps: "
            + ", ".join(r["folds_unwatchable"])
        )
    if r["status"] == "no entry points":
        lines.append("no entry points: its folds run only through other families' entry points")
    for m in r["mismatches"][:10]:
        where = m["where"] or "generated"
        lines.append(
            f"MISMATCH {m['case']} ({where}), {m['site']}: the model gives {m['model']}, opt {m['opt']}"
        )
        lines.append(m["ir"])
    for m in r["unexplained"][:5]:
        lines += [f"unexplained {m['case']} ({m['where'] or 'generated'}): opt gives {m['opt']}", m["ir"]]
    print("\n      ".join(lines))


# ------------------------------------------------------------------------------------------------------------
# score


def recorded(reg: Registry) -> tuple[dict[str, Any] | None, str]:
    """The family's recorded comparison, and why it doesn't count, or "" if it does."""
    path = COMPARED / f"{reg.family}.json"
    again = f"run `tests/peephole.py compare --family {reg.family} --write`"
    if not path.is_file():
        return None, f"no comparison is recorded in {rel(path)}: {again}"
    rec = schemas.read(path, schemas.PEEPHOLE_COMPARISON)
    if rec.get("sources") != model_hash(reg):
        return rec, f"{rel(path)} compared other sources than the model's now: {again}"
    if rec.get("status") not in ("ok", "no entry points"):
        return rec, f"{rel(path)} says {rec.get('status')}"
    return rec, ""


def compared_runs(
    comparisons: dict[str, tuple[dict[str, Any] | None, str]],
) -> tuple[set[str], set[str], set[str]]:
    """From every comparison recorded for its sources now, with something compared and no mismatch: the folds
    a compared run reached; the sites that fired and matched `opt` in a compared case with no `undef` in it,
    which `opt` exercised; and the sites that fired in compared cases, but only in ones with an `undef`."""
    folds, exercised = set(), set()
    fired: Counter[str] = Counter()
    clean: Counter[str] = Counter()
    for rec, why_not in comparisons.values():
        if rec is None or why_not or rec.get("status") != "ok":
            continue
        folds |= set(rec.get("folds_run", {}))
        for s, v in rec.get("sites", {}).items():
            exercised |= {s} if v.get("matched_without_undef", 0) > 0 else set()
            fired[s] += v.get("fired", 0)
            clean[s] += v.get("fired_without_undef", 0)
    return folds, exercised, {s for s, n in fired.items() if n and not clean[s]}


def module_checks(modules: list[str]) -> dict[str, dict[str, Any]]:
    """Each module's axiom audit, which reads it and everything it imports as data, and its replay by
    leanchecker, a few at a time."""

    def audit(m: str) -> tuple[str, str, proc.Ran]:
        return m, "check_axioms", run(leanlib.audit_argv(LEAN_MB), {**lean_env(), **leanlib.audit_env(m)})

    def replay(m: str) -> tuple[str, str, proc.Ran]:
        return m, "leanchecker", run(leanlib.checker(m), lean_env())

    out: dict[str, dict[str, Any]] = {m: {} for m in modules}
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        for m, what, r in pool.map(
            lambda job: job[0](job[1]), [(f, m) for m in modules for f in (audit, replay)]
        ):
            out[m][what] = core.Step.of(what, r)
            if what == "check_axioms":
                said = re.search(r"and (\d+) from bv_decide", r.out)
                out[m]["bv_decide"] = int(said[1]) if said else None
    return out


def counts(
    site: str,
    found: dict[str, Any] | None,
    sound: str,
    snd: dict[str, Any],
    built: core.Step,
    ran: dict[str, Any],
    why_not: str,
    compared: bool = True,
    uncovered: frozenset[str] = frozenset(),
    undef_only: bool = False,
) -> tuple[str, core.Decision]:
    """Whether a rewrite counts toward G2, and if not, how far it got: what Lean says of its theorem, `found`,
    and of its fold's `sound` theorem, `snd`, its module's axiom audit and replay, `ran`, why its family's
    comparison with `opt` doesn't count, `why_not`, if it doesn't, whether a compared run reached its fold,
    `compared`, the types the inventory says it needs that its proof doesn't cover, `uncovered`, and whether
    its step fired in compared cases only where an operand reaches `undef`, `undef_only`. irlean.verdict
    decides. One of:

    - `counted`: every rule holds;
    - `proved, model not compared with opt`: proved, but no compared run reached its fold;
    - `undef-only`: proved and compared, but only `undef` reaches its step, which the proof doesn't cover;
    - `integer instance proved`: proved and compared, for integers, and the inventory says it needs more;
    - `not counted`: a rule about the proof or its family's comparison fails, and a registry listing it as
      proved is wrong."""
    rules = {
        f"Peephole.{site} is a theorem": bool(found) and found["kind"] == "theorem",
        "it rests on the standard three axioms only": bool(found) and set(found["axioms"]) <= STANDARD_AXIOMS,
        f"{sound} is a theorem on the standard three axioms only": snd.get("kind") == "theorem"
        and set(snd.get("axioms", ["?"])) <= STANDARD_AXIOMS,
        f"{sound} uses it": f"Peephole.{site}" in snd.get("sites", []),
        "its module passes the axiom audit, with nothing from bv_decide": ran.get("bv_decide") == 0,
        "its family's comparison with opt is recorded for its sources now, with no mismatch": not why_not,
    }

    def decide(checks: dict[str, bool]) -> core.Decision:
        evidence = core.Evidence(
            lean=built, replay=ran.get("leanchecker"), axioms=ran.get("check_axioms"), checks=checks
        )
        return core.decide(core.Verdict.PROVED, evidence)

    proof = decide(rules)
    if not proof.granted:
        return "not counted", proof
    every = {
        **rules,
        "a compared run reached its fold, so its model was compared with opt": compared,
        "it fired in a compared case with no undef, if it fired at all": not undef_only,
        "its proof covers every type the inventory says it needs": not uncovered,
    }
    decision = decide(every)
    if decision.granted:
        return "counted", decision
    if not compared:
        return "proved, model not compared with opt", decision
    return ("undef-only" if undef_only else "integer instance proved"), decision


def pct(n: int, d: int) -> float:
    return round(100 * n / d, 2) if d else 0.0


def score(args: argparse.Namespace) -> int:
    started = time.monotonic()
    regs = registries()
    inv = inventory()
    ids = {r["id"]: (p, r) for p, rs in inv.items() for r in rs}
    built = lake_built(["Peephole"])
    listed: dict[str, tuple[Registry, str, str]] = {}
    problems = []
    for reg in regs:
        for s, (fold, sound) in reg.sites().items():
            if s in listed:
                problems.append(f"{s} is listed by {listed[s][0].family} and by {reg.family}")
            listed[s] = (reg, fold, sound)
        for s in [*reg.sites(), *reg.data.get("unproved", {})]:
            if s not in ids:
                problems.append(f"{reg.family}: {s} isn't a rewrite in {rel(INVENTORY)}")
    with workdir(False) as work:
        build_harness(work)
        request = {
            "sites": [f"Peephole.{i}" for i in ids],
            "sounds": sorted({v[2] for v in listed.values()}),
            "reps": 0,
        }
        found = facts(work, request, library_modules())
    sites = {f["name"].removeprefix("Peephole."): f for f in found["sites"]}
    sounds = {f["name"]: f for f in found["sounds"]}
    checks = module_checks(sorted({sites[s]["module"] for s in listed if s in sites and sites[s]["module"]}))
    comparisons = {reg.family: recorded(reg) for reg in regs}
    folds_run, exercised, undef_only = compared_runs(comparisons)
    outcome: dict[str, dict[str, Any]] = {}
    for s, (reg, fold, sound) in sorted(listed.items()):
        f = sites.get(s)
        why_not = comparisons[reg.family][1]
        ran = checks.get(f["module"], {}) if f else {}
        needs = set(ids[s][1]["needs"]) - {"int"} if s in ids else set()
        uncovered = frozenset(needs - set(reg.data.get("covers", {}).get(s, [])))
        status, decision = counts(
            s,
            f,
            sound,
            sounds.get(sound, {}),
            built,
            ran,
            why_not,
            fold in folds_run,
            uncovered,
            s in undef_only,
        )
        outcome[s] = {
            "id": s,
            "family": reg.family,
            "fold": fold,
            "status": status,
            "exercised": s in exercised,
            "needs": sorted(ids[s][1]["needs"]) if s in ids else [],
            "why": "" if status == "counted" else decision.detail + (f"; {why_not}" if why_not else ""),
        }
    counted = {s for s, o in outcome.items() if o["status"] == "counted"}
    passes = {}
    every = [r for rewrites in inv.values() for r in rewrites]
    for p, rs in [*inv.items(), ("all", every)]:
        ints = [r for r in rs if r["needs"] == ["int"]]
        of = lambda status, rs=rs: sum(outcome.get(r["id"], {}).get("status") == status for r in rs)  # noqa: E731
        passes[p] = {
            "inventoried": len(rs),
            "proved": sum(r["id"] in counted for r in rs),
            "percent": pct(sum(r["id"] in counted for r in rs), len(rs)),
            "exercised": sum(r["id"] in counted and r["id"] in exercised for r in rs),
            "int": len(ints),
            "int_proved": sum(r["id"] in counted for r in ints),
            "int_percent": pct(sum(r["id"] in counted for r in ints), len(ints)),
            "not_compared": of("proved, model not compared with opt"),
            "integer_instances": of("integer instance proved"),
            "undef_only": of("undef-only"),
            "blocked": {
                k: {"waits_for": w, "count": len(b), "rewrites": b}
                for k, w in WAITS_FOR.items()
                for b in [sorted(r["id"] for r in rs if k in r["needs"])]
            },
        }
    proved = [o for o in outcome.values() if o["status"] == "counted"]
    not_counted = [o for o in outcome.values() if o["status"] == "not counted"]
    record = {
        "schema": schemas.PEEPHOLE_SCORE,
        "date": today(),
        "llvm": schemas.read(INVENTORY / PASSES["instsimplify"][0], schemas.REWRITES)["llvm"],
        "passes": passes,
        "families": {
            reg.family: {
                "registry": rel(reg.path),
                "sites": len(reg.sites()),
                "proved": sum(s in counted for s in reg.sites()),
                "exercised": sum(s in counted and s in exercised for s in reg.sites()),
                "not_compared": sum(
                    outcome[s]["status"] == "proved, model not compared with opt" for s in reg.sites()
                ),
                "integer_instances": sum(
                    outcome[s]["status"] == "integer instance proved" for s in reg.sites()
                ),
                "undef_only": sum(outcome[s]["status"] == "undef-only" for s in reg.sites()),
                "not_counted": sum(outcome[s]["status"] == "not counted" for s in reg.sites()),
                "unproved": len(reg.data.get("unproved", {})),
                "comparison": comparisons[reg.family][1]
                or (comparisons[reg.family][0] or {}).get("status", ""),
                "folds_not_run": sorted(set(reg.folds) - folds_run),
            }
            for reg in regs
        },
        "sites": list(outcome.values()),
        "proved": proved,
        "not_compared": [o for o in outcome.values() if o["status"] == "proved, model not compared with opt"],
        "integer_instances": [o for o in outcome.values() if o["status"] == "integer instance proved"],
        "undef_only": [o for o in outcome.values() if o["status"] == "undef-only"],
        "not_counted": not_counted,
        "problems": problems,
        "unproved": {s: why for reg in regs for s, why in sorted(reg.data.get("unproved", {}).items())},
        "unregistered": sorted(s for s, f in sites.items() if s not in listed and f["kind"] == "theorem"),
        "seconds": round(time.monotonic() - started, 1),
    }
    out = args.out or WORK / "score.json"
    schemas.write(out, record, schemas.PEEPHOLE_SCORE, indent=2)
    print(markdown(record))
    print(f"\nwritten to {out}, in {record['seconds']} s")
    failed = bool(problems or not_counted)
    for x in problems:
        print(f"FAIL  {x}")
    for x in not_counted:
        print(f"FAIL  {x['family']}: {x['id']} is listed as proved, and doesn't count: {x['why']}")
    for x in [*record["not_compared"], *record["undef_only"], *record["integer_instances"]]:
        print(f"      {x['family']}: {x['id']}: {x['status']}, not counted")
    if args.check:
        print(f"{'FAIL' if failed else 'ok  '}  every rewrite a registry lists as proved counts")
        return 1 if failed else 0
    return 0


NAMES = {
    "instsimplify": "InstSimplify",
    "instcombine": "InstCombine",
    "aggressive-instcombine": "AggressiveInstCombine",
    "reassociate": "Reassociate",
    "all": "All",
}


def markdown(record: dict[str, Any]) -> str:
    rows = [
        "| Pass | Rewrites | Proved | % | Of those, exercised by opt | Integers only | Proved of those | % "
        "| Proved, model not compared | Undef only | Integer instance proved | Need fp (SEM-05) "
        "| Need memory (F4) | Need calls |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for p, v in record["passes"].items():
        b = v["blocked"]
        rows.append(
            f"| {NAMES[p]} | {v['inventoried']:,} | {v['proved']:,} | {v['percent']} | {v['exercised']:,} "
            f"| {v['int']:,} | {v['int_proved']:,} | {v['int_percent']} | {v['not_compared']:,} "
            f"| {v['undef_only']:,} | {v['integer_instances']:,} | {b['fp']['count']:,} "
            f"| {b['memory']['count']:,} | {b['calls']['count']:,} |"
        )
    rows += [
        "",
        "| Family | Sites listed | Proved | Exercised by opt | Proved, model not compared | Undef only "
        "| Integer instance proved | Not counting | Listed unproved | Comparison |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for fam, v in record["families"].items():
        rows.append(
            f"| `{fam}` | {v['sites']} | {v['proved']} | {v['exercised']} | {v['not_compared']} "
            f"| {v['undef_only']} | {v['integer_instances']} | {v['not_counted']} | {v['unproved']} "
            f"| {v['comparison']} |"
        )
    return "\n".join(rows)


# ------------------------------------------------------------------------------------------------------------
# measure


def kind_of(family: str | None) -> str:
    """A stored lemma's kind, for counting reuse: a rewrite, or refinement's laws and LangRef's contracts."""
    if family and family.startswith(REWRITE_FAMILIES):
        return "rewrite"
    return "law or contract" if family in ("refinement", "contracts") else "other"


def site_time(site: str, commands: list[dict[str, Any]]) -> float:
    """A site's elaboration and kernel time: its theorem's command, and any whose theorem is named after
    it."""
    name = f"Peephole.{site}"
    return round(
        sum(
            c["ms"]
            for c in commands
            if any(n == name or n.startswith((f"{name}_", f"{name}.")) for n in c["names"])
        ),
        2,
    )


def measure(args: argparse.Namespace) -> int:
    started = time.monotonic()
    regs = registries(args.family)
    index = schemas.read(INDEX, schemas.STORE_INDEX)
    family_of = {e["name"]: e.get("family") for e in index["lemmas"]}
    lake_built(["Peephole"])
    # The proofs in the order they're counted: registries by name, and each one's sites as it lists them.
    listed = {s: reg for reg in regs for s in reg.sites()}
    with workdir(args.keep) as work:
        build_harness(work)
        request = {"sites": [f"Peephole.{s}" for s in listed], "stored": sorted(family_of), "reps": args.reps}
        found = facts(work, request, library_modules(), pool="peephole-facts")
        sites = {f["name"].removeprefix("Peephole."): f for f in found["sites"]}
        # The sample: each site with each stored rewrite lemma its proof names itself.
        sample = [
            (f"Peephole.{s}", lemma)
            for s, f in sites.items()
            for lemma in f["direct"]
            if kind_of(family_of.get(lemma)) == "rewrite"
        ]
        inline = (
            facts(
                work, {**request, "sites": [], "inline": sample}, library_modules(), pool="peephole-inline"
            )["inline"]
            if sample
            else []
        )
        # Each module the families' models and proofs are in, and every module of the library they import.
        named = {m for reg in regs for m in reg.modules} | {
            f["module"] for f in sites.values() if f["module"]
        }
        modules = [
            ".".join(p.relative_to(PEEPHOLE).with_suffix("").parts) for p in model_sources(sorted(named))
        ]
        (work / "Time.lean").write_text(
            "import PeepholeHarness\n\n"
            "def main (args : List String) : IO UInt32 := PeepholeHarness.timeMain args\n"
        )
        per_module, timed = {}, {}
        for m in modules:
            record, _ = pooled(
                f"peephole-{m}", leanlib.argv(LEAN_MB, module_file(m)), lean_env(), LEAN_MB + 1000, TIMEOUT
            )
            per_module[m] = {
                k: record[k]
                for k in ("outcome", "exit", "wall_s", "user_s", "peak_process_mb", "peak_tree_mb")
            }
            _, said = pooled(
                f"peephole-time-{m}",
                leanlib.argv(LEAN_MB, "--run", work / "Time.lean", module_file(m), m),
                lean_env(work),
                LEAN_MB + 1000,
                TIMEOUT,
            )
            timed[m] = harness_json(said)
            per_module[m]["commands_ms"] = round(sum(c["ms"] for c in timed[m]["commands"]), 1)
            per_module[m]["import_ms"] = round(timed[m]["import_ms"], 1)
            if timed[m]["errors"]:
                raise HarnessError(f"{m} has errors when its commands are timed: {timed[m]['errors'][:3]}")
    proofs: list[dict[str, Any]] = []
    for s, reg in listed.items():
        f = sites.get(s)
        if f is None:
            proofs.append({"id": s, "family": reg.family, "theorem": None})
            continue
        uses = {
            k: sorted(u for u in f["uses"] if kind_of(family_of.get(u)) == k)
            for k in ("rewrite", "law or contract", "other")
        }
        own = f"peephole-{reg.family}"
        proofs.append(
            {
                "id": s,
                "family": reg.family,
                "theorem": f["name"],
                "module": f["module"],
                "elaboration_ms": site_time(s, timed.get(f["module"], {}).get("commands", [])),
                "kernel_ms": f["kernel_ms"],
                "uses": uses,
                "uses_rewrite": bool(uses["rewrite"]),
                "uses_rewrite_from_elsewhere": any(family_of.get(u) != own for u in uses["rewrite"]),
            }
        )
    done = [p for p in proofs if p["theorem"]]
    rewrite_lemmas = [e for e in index["lemmas"] if kind_of(e.get("family")) == "rewrite"]
    store_ms = [x["store_ms"] for x in inline if x["checked"]]
    inlined_ms = [x["inlined_ms"] for x in inline if x["checked"]]
    peaks = {m: v["peak_process_mb"] for m, v in per_module.items()}
    record = {
        "schema": schemas.PEEPHOLE_MEASURE,
        "date": today(),
        "host": {"platform": sys.platform, "cpus": os.cpu_count(), "memory_mb": proc.memory()["total_mb"]},
        "lean_mb": LEAN_MB,
        "proofs": proofs,
        "modules": per_module,
        "e3": {
            "proofs": len(done),
            "using_a_stored_rewrite_lemma": sum(p["uses_rewrite"] for p in done),
            "using_one_from_elsewhere": sum(p["uses_rewrite_from_elsewhere"] for p in done),
            "using_any_stored_lemma": sum(
                bool(p["uses"]["rewrite"] or p["uses"]["law or contract"] or p["uses"]["other"]) for p in done
            ),
            "lemmas_meeting_all_four_rules": sum(e.get("status") == "admitted" for e in index["lemmas"]),
            "rewrite_lemmas_meeting_all_four_rules": sum(
                e.get("status") == "admitted" for e in rewrite_lemmas
            ),
            "rewrite_lemmas": len(rewrite_lemmas),
            "inline_sample": inline,
            "median_store_ms": median(store_ms),
            "median_inlined_ms": median(inlined_ms),
        },
        "targets": targets(peaks),
        "seconds": round(time.monotonic() - started, 1),
    }
    out = args.out or WORK / "measure.json"
    schemas.write(out, record, schemas.PEEPHOLE_MEASURE, indent=2)
    print_measure(record)
    print(f"written to {out}, in {record['seconds']} s")
    return 0


def median(xs: list[float]) -> float | None:
    if not xs:
        return None
    s = sorted(xs)
    return round(s[len(s) // 2] if len(s) % 2 else (s[len(s) // 2 - 1] + s[len(s) // 2]) / 2, 3)


def targets(peaks: dict[str, float]) -> dict[str, Any]:
    """Peak-memory targets from what was measured: each module at most one and a half times its peak, in steps
    of 256 MB, and the library at most the largest of those, under the 4 GB each Lean process may take."""
    per = {m: int(-(-1.5 * p // 256) * 256) for m, p in peaks.items()}
    return {"per_module_mb": per, "library_mb": max(per.values(), default=0), "cap_mb": LEAN_MB}


def print_measure(r: dict[str, Any]) -> None:
    print("| Module | Wall | Peak | Commands |")
    print("| --- | --- | --- | --- |")
    for m, v in r["modules"].items():
        print(f"| `{m}` | {v['wall_s']} s | {v['peak_process_mb']:.0f} MiB | {v['commands_ms']} ms |")
    print("\n| Site | Elaboration and kernel | Kernel | Stored rewrite lemmas | Laws and contracts |")
    print("| --- | --- | --- | --- | --- |")
    for p in r["proofs"]:
        if p["theorem"]:
            rewrites = ", ".join(p["uses"]["rewrite"]) or "none"
            laws = ", ".join(p["uses"]["law or contract"]) or "none"
            print(
                f"| `{p['id']}` | {p['elaboration_ms']} ms | {p['kernel_ms']:.3f} ms | {rewrites} | {laws} |"
            )
    e = r["e3"]
    print(
        f"\nE3: {e['using_a_stored_rewrite_lemma']} of {e['proofs']} proofs use a stored rewrite lemma, "
        f"{e['using_one_from_elsewhere']} one cut from another family's proofs. "
        f"{e['lemmas_meeting_all_four_rules']} lemmas meet all four rules, "
        f"{e['rewrite_lemmas_meeting_all_four_rules']} of them rewrites."
    )
    print(
        f"The kernel, at the median over {len(e['inline_sample'])} pairs of a site and a lemma it names: "
        f"{e['median_store_ms']} ms with the store, {e['median_inlined_ms']} ms with the lemma's proof "
        "inlined."
    )
    print(f"Peak-memory targets: {r['targets']}")


# ------------------------------------------------------------------------------------------------------------
# store


def store(args: argparse.Namespace) -> int:
    reg = registries(args.family)[0]
    lemmas = reg.data.get("lemmas", [])
    if not lemmas:
        print(f"{reg.family} offers no lemmas: its registry's `lemmas` is empty")
        return 0
    family = f"peephole-{reg.family}"
    provenance = f"chunk 1's G2, {rel(reg.path)}, cut from the proofs of {', '.join(sorted(reg.sites()))}"
    WORK.mkdir(parents=True, exist_ok=True)
    # The store's index is one file: one family at a time.
    with (WORK / "store.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)

        def add(names: list[str], dry: bool) -> dict[str, Any]:
            argv = [
                sys.executable,
                STORE,
                "add",
                "--existing",
                *names,
                "--family",
                family,
                "--provenance",
                provenance,
                "--json",
            ]
            r = run([*argv, *(["--dry-run"] if dry else [])], timeout=3600)
            try:
                return json.loads(r.out)
            except json.JSONDecodeError as e:
                raise HarnessError(f"store.py add said nothing it could read:\n{r.output[-3000:]}") from e

        judged = add(lemmas, True)
        if judged.get("status") == "error":
            raise HarnessError(f"store.py add: {judged.get('reason')}: {judged.get('detail')}")
        passing = [x["name"] for x in judged["lemmas"] if x["status"] != "refused"]
        for x in judged["lemmas"]:
            why = "; ".join(f"{y['code']}: {y['detail']}" for y in x["reasons"])
            print(f"{x['status']:9}  {x['name']}" + (f"  {why}" if why else ""))
        stored = None
        if passing and not args.dry_run:
            stored = add(passing, False)
            if stored.get("status") != "accepted":
                raise HarnessError(
                    f"store.py add refused what it accepted on a dry run: {json.dumps(stored)[:3000]}"
                )
            # What uses each stored lemma now, the Peephole library's proofs included.
            r = run([sys.executable, STORE, "check", "--write", "--json"], timeout=3600)
            if r.exit not in (0, 2):
                raise HarnessError(f"store.py check --write failed:\n{r.output[-3000:]}")
        report = {
            "family": reg.family,
            "date": today(),
            "judged": judged,
            "stored": passing if stored else [],
        }
        (WORK / f"store-{reg.family}.json").write_text(json.dumps(report, indent=2) + "\n")
        print(
            f"{len(passing)} of {len(lemmas)} admitted or candidates, {len(lemmas) - len(passing)} refused; "
            + ("stored" if stored else "nothing stored")
        )
    return 0


# ------------------------------------------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("compare", help="each registered model against the pinned opt")
    p.add_argument("--family")
    p.add_argument("--write", action="store_true", help="record each family's result for `score`")
    p.add_argument(
        "--strict", action="store_true", help="fail where opt folds and nothing explains the model not"
    )
    p.add_argument("--out", type=Path, help="write every family's report here, as JSON")
    p.add_argument("--keep", action="store_true", help="keep the work directory, and print it")
    p = sub.add_parser("measure", help="E3's numbers for every site's proof")
    p.add_argument("--family")
    p.add_argument("--reps", type=int, default=11, help="kernel checks of each proof, for the median")
    p.add_argument("--out", type=Path)
    p.add_argument("--keep", action="store_true")
    p = sub.add_parser("score", help="chunk 1's G2, per pass")
    p.add_argument("--check", action="store_true", help="fail if a registry lists a site that doesn't count")
    p.add_argument("--out", type=Path)
    p = sub.add_parser("store", help="offer a family's value lemmas to the lemma store")
    p.add_argument("--family", required=True)
    p.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    try:
        return {"compare": compare, "measure": measure, "score": score, "store": store}[args.command](args)
    except Unknown as e:
        print(
            f"UNKNOWN  {e}: a limit stopped a step, so this is neither a pass nor a failure", file=sys.stderr
        )
        return 1
    except (HarnessError, schemas.SchemaError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
