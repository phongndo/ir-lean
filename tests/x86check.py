#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks the model's `bitcast` between integers and vectors of them, and x86's intrinsics but the bit
functions tests/vecopcheck.py has, through the emitter, against LLVM itself, poison included, on any
processor.

tests/x86native.py runs the intrinsics on the processor, which can't see poison. This asks two oracles that
can, for each operation at every form tests/x86ops.py lists, on random inputs, inputs at the extremes, every
operand a splat of an extreme, where saturation and wrapping show, and inputs with poison lanes:
  - Alive2, where it knows the operation. A function that calls it on constant inputs, and one that returns
    what the model gives, have to refine each other both ways, so the model is exactly as poisonous as
    Alive2, lane by lane.
  - InstCombine, with x86's own folds. Where it folds a call to a constant, every lane the model gives a value
    has to fold to that value. A lane the model makes poison may fold to anything, since that only refines
    it. Where it only replaces operands, as it drops the quadwords PCLMULQDQ doesn't read, the model on the
    new operands has to give every value it gave on the old ones, as a rewrite that refines has to.
Each can fail. For each operation Alive2 knows, it has to find a changed result wrong, and what the wrong
version in tests/x86/Wrong.lean gives on some input. For each InstCombine folds, the fold has to differ from
the wrong version on some input.

An operation only the processor checks is said to be one: Alive2 has to call it an unknown function, and
InstCombine has to leave it on inputs without poison, so the list can't go stale.

usage: tests/x86check.py path/to/ir-lean
"""

import os
import random
import re
import shutil
import sys
import tempfile

import alive
import x86ops
from differential import NATIVE, lean_output
from opcheck import alive_verdict, lean_env, sh
from x86ops import POISON, ty

sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
from irlean import hashing, proc

TRIPLE = "x86_64-unknown-linux-gnu"
# A lane LLVM folds to `undef`, which may be anything.
UNDEF = "undef"

# Every shape the q4_K kernels' slices use, both ways, and some the model has to get right anyway: lanes that
# aren't bytes, a single lane, and the same type.
BITCASTS = [
    ((16, 16), (32, 8)),
    ((16, 16), (8, 32)),
    ((16, 32), (32, 16)),
    ((16, 32), (64, 8)),
    ((32, 16), (16, 32)),
    ((32, 16), (64, 8)),
    ((4, 32), (16, 8)),
    ((4, 64), (16, 16)),
    ((4, 64), (32, 8)),
    ((4, 64), (8, 32)),
    ((8, 32), (16, 16)),
    ((8, 32), (32, 8)),
    ((32, 8), (8, 32)),
    ((32, 8), (4, 64)),
    ((64, 8), (16, 32)),
    ((16, 8), (4, 32)),
    ((2, 64), (1, 128)),
    ((1, 128), (16, 8)),
    ((8, 1), (1, 8)),
    ((1, 8), (8, 1)),
    ((4, 2), (2, 4)),
    ((2, 4), (8, 1)),
    ((4, 32), (4, 32)),
    # A scalar, as (0, width), is a vector of one lane to the model. The first is the Q5 rewrite's.
    ((0, 32), (32, 1)),
    ((32, 1), (0, 32)),
    ((0, 8), (8, 1)),
    ((0, 16), (2, 8)),
    ((4, 8), (0, 32)),
    ((0, 64), (2, 32)),
    ((1, 32), (0, 32)),
    ((0, 32), (1, 32)),
    ((0, 32), (0, 32)),
]
# The intrinsics checked here: all but the bit functions, which tests/vecopcheck.py checks the same way, and
# VZEROUPPER, which computes nothing for Alive2 or InstCombine to say anything about.
INTRINSICS = [op for op in x86ops.OPS if op not in x86ops.bit_functions() and not op.body]


def label(shape):
    return f"i{shape[1]}" if shape[0] == 0 else f"{shape[0]}x{shape[1]}"


def operations():
    """Each operation as (name, result shape, argument shapes, the instruction on %a0, %a1, ..., and the
    intrinsic it is, or None for a `bitcast`)."""
    ops: list[tuple[str, x86ops.Shape, list[x86ops.Shape], str, x86ops.Op | None]] = [
        (op.name, op.ret, list(op.args), op.call, op) for op in INTRINSICS
    ]
    for src, dst in BITCASTS:
        name = f"bitcast_{label(src)}_{label(dst)}"
        ops.append((name, dst, [src], f"bitcast {ty(src)} %a0 to {ty(dst)}", None))
    return ops


def declarations():
    return "\n".join(sorted({op.declaration for op in INTRINSICS})) + "\n"


def extremes(w):
    m = (1 << w) - 1
    return sorted({0, 1, m, 1 << (w - 1), (1 << (w - 1)) - 1, 0x0F & m, 0x80 & m})


def cases(args, op, rand):
    """Random inputs, inputs at the extremes and where the operation saturates or wraps, and inputs with
    poison lanes. Each is a list of lanes for each argument."""
    if op:
        out = x86ops.value_cases(op, rand, random=6, edges=4, tables=False) + x86ops.poison_cases(op, rand)
        # Every lane of one operand poison.
        for i, (n, _) in enumerate(op.args):
            case = [x86ops.operand(op, j, rand) for j in range(len(op.args))]
            case[i] = [POISON] * max(n, 1)
            out.append(case)
        return out
    out = []
    args = [(max(n, 1), w) for n, w in args]
    for _ in range(6):
        out.append([[rand.getrandbits(w) for _ in range(n)] for n, w in args])
    for _ in range(4):
        out.append([[rand.choice(extremes(w)) for _ in range(n)] for n, w in args])
    for k in range(6):
        case = [[rand.getrandbits(w) for _ in range(n)] for n, w in args]
        # In one argument, or in each, one lane or several.
        for i, (n, _) in enumerate(args):
            if k % 2 == 0 and i > 0:
                continue
            for lane in rand.sample(range(n), 1 if k < 2 else max(1, n // 4)):
                case[i][lane] = POISON
        out.append(case)
    return out


def constant(shape, lanes):
    w = shape[1]

    def one(x):
        if x == POISON:
            return "poison"
        return ("true" if x else "false") if w == 1 else str(x)

    if shape[0] == 0:
        return one(lanes[0])
    return "<" + ", ".join(f"i{w} {one(x)}" for x in lanes) + ">"


def eval_in_lean(tool, ops, all_cases, work):
    """What the model gives for each case, and what the wrong versions of tests/x86/Wrong.lean give: a pair
    of lists of lanes, each lane a number or POISON, or why there's none."""
    ll = os.path.join(work, "ops.ll")
    with open(ll, "w") as f:
        f.write(declarations())
        for name, ret, args, instruction, _ in ops:
            params = ", ".join(f"{ty(a)} %a{i}" for i, a in enumerate(args))
            f.write(
                f"\ndefine {ty(ret)} @{name}({params}) {{\n  %r = {instruction}\n  ret {ty(ret)} %r\n}}\n"
            )
    r = proc.run([tool, ll, "-o", os.path.join(work, "Ops.lean"), "--namespace", "Ops"])
    if r.exit != 0:
        sys.exit(f"the emitter left operations out:\n{r.err}")
    with open(os.path.join(work, "Ops.lean")) as f:
        emitted = f.read()
    with open(os.path.join(work, "OpsWrong.lean"), "w") as f:
        f.write(x86ops.wrong_module(emitted))
    shutil.copyfile(x86ops.WRONG, os.path.join(work, "X86Wrong.lean"))
    # Inputs are read as the test runs: Lean takes too long to elaborate this many numerals as literals.
    inputs = os.path.join(work, "inputs.txt")
    with open(inputs, "w") as f:
        for cs in all_cases:
            for c in cs:
                f.write("|".join(" ".join(map(str, lanes)) for lanes in c) + "\n")
    src = [
        # The inputs aren't a .lean file, and what Lean printed is kept by the .lean files it read.
        f"-- inputs {hashing.sha256_file(inputs)}",
        "import Ops",
        "import OpsWrong",
        "open IRLean",
        "def lanes {n w : Nat} (xs : List Int) : Vec n w :=",
        "  Vector.ofFn fun i => let x := xs.getD i 0; if x < 0 then none else some (BitVec.ofNat w x.toNat)",
        "def val {w : Nat} : List Int → Val w",
        "  | x :: _ => if x < 0 then none else some (BitVec.ofNat w x.toNat)",
        "  | [] => none",
        "def showVal {w : Nat} : Val w → String",
        "  | some v => toString v.toNat",
        f'  | none => "{POISON}"',
        "def showStop {α : Type} : Outcome α → String",
        '  | some (.error (.undefined _)) => "ub"',
        '  | some (.error (.model _)) => "stop"',
        '  | _ => "diverged"',
        "def show' {n w : Nat} : Outcome (Vec n w) → String",
        '  | some (.ok v) => " ".intercalate (v.toList.map showVal)',
        "  | o => showStop o",
        "def showOne {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok v) => showVal v",
        "  | o => showStop o",
        "def parse (line : String) : Array (List Int) :=",
        '  ((line.splitOn "|").map fun part => (part.splitOn " ").filterMap String.toInt?).toArray',
    ]
    rows = []
    for k, ((name, ret, args, _, _), cs) in enumerate(zip(ops, all_cases, strict=True)):
        call = " ".join(
            f"(val (w := {w}) c[{i}]!)" if n == 0 else f"(lanes (n := {n}) (w := {w}) c[{i}]!)"
            for i, (n, w) in enumerate(args)
        )
        shows = "showOne" if ret[0] == 0 else "show'"
        src.append(
            f"def r{k} (c : Array (List Int)) : String × String :=\n"
            f"  ({shows} (Ops.{name} {call}), {shows} (OpsWrong.{name} {call}))"
        )
        rows.append(f"({len(cs)}, r{k})")
    src += [
        "def table : Array (Nat × (Array (List Int) → String × String)) := #[",
        "  " + ",\n  ".join(rows) + "]",
        "def main (args : List String) : IO Unit := do",
        "  let lines ← IO.FS.lines args.head!",
        "  let mut line := 0",
        "  for (cases, run) in table do",
        "    for _ in [0:cases] do",
        "      let (model, wrong) := run (parse lines[line]!)",
        "      IO.println model",
        "      IO.println wrong",
        "      line := line + 1",
    ]
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_ops():
        for module in ("Ops", "X86Wrong", "OpsWrong"):
            out, source = os.path.join(work, f"{module}.olean"), os.path.join(work, f"{module}.lean")
            sh(["lean", "-R", work, "-o", out, source], env=env)

    lines = lean_output(work, ["lean", *NATIVE, "--run", path, inputs], env, compile_ops).splitlines()
    if len(lines) != 2 * sum(len(cs) for cs in all_cases):
        sys.exit("Lean printed the wrong number of results")

    def read(line):
        return [int(x) for x in line.split()] if re.fullmatch(r"[\d -]+", line) else line

    results, pos = [], 0
    for cs in all_cases:
        results.append([(read(lines[pos + 2 * c]), read(lines[pos + 2 * c + 1])) for c in range(len(cs))])
        pos += 2 * len(cs)
    return results


def calls(ops, all_cases):
    """For each case, the operation on its constant inputs as a function @F, with its result shape."""
    out = []
    for (name, ret, args, instruction, _), cs in zip(ops, all_cases, strict=True):
        for k, c in enumerate(cs):
            body = instruction
            for i, (shape, lanes) in enumerate(zip(args, c, strict=True)):
                body = body.replace(f"{ty(shape)} %a{i}", f"{ty(shape)} {constant(shape, lanes)}")
            out.append((name, k, ret, f"define {ty(ret)} @F() {{\n  %r = {body}\n  ret {ty(ret)} %r\n}}\n"))
    return out


def returns(shape, lanes):
    return f"define {ty(shape)} @F() {{\n  ret {ty(shape)} {constant(shape, lanes)}\n}}\n"


def check_alive(ops, all_cases, results, work):
    """Each case of an operation Alive2 knows, the call and what the model returns, refining each other both
    ways. For each such operation, two controls Alive2 has to find wrong, so a pass can't come from Alive2
    reading something else: its first input with lane 0 of the result changed, from a value to the next one or
    from poison to 0, and an input where the wrong version gives something else, with what it gives. And each
    operation Alive2 doesn't know, which it has to call an unknown function."""
    jobs, wrong, controls, mutants, strangers = [], [], {}, {}, {}
    by_name = {name: op for name, _, _, _, op in ops}
    flat = [r for rs in results for r in rs]
    for (name, k, ret, src), (result, twin) in zip(calls(ops, all_cases), flat, strict=True):
        op = by_name[name]
        if isinstance(result, str):
            wrong.append((name, k, f"the model gives {result}"))
            continue
        if op and not op.alive:
            strangers.setdefault(name, (src, returns(ret, result)))
            continue
        jobs.append((name, k, src, returns(ret, result)))
        if name not in controls:
            changed = [0 if result[0] == POISON else (result[0] + 1) % (1 << ret[1]), *result[1:]]
            controls[name] = (src, returns(ret, changed))
        if op and name not in mutants and not isinstance(twin, str) and twin != result:
            mutants[name] = (src, returns(ret, twin))
    refuted = [*controls.items(), *mutants.items()]
    pairs = [pair for _, _, src, tgt in jobs for pair in ((src, tgt), (tgt, src))]
    pairs += [pair for _, (src, tgt) in refuted for pair in ((src, tgt), (tgt, src))]
    pairs += list(strangers.values())
    outputs = alive.refinements(declarations(), pairs, work)
    at = 2 * len(jobs)
    for j, (name, _) in enumerate(refuted):
        verdicts = [alive_verdict("", outputs[at + 2 * j + d]) for d in (0, 1)]
        if not any(v and v[0] == "fail" for v in verdicts):
            what = "a wrong result" if j < len(controls) else "the wrong version's result"
            wrong.append((name, 0, f"Alive2 doesn't find {what} wrong"))
    for name in sorted({n for n, _, _, _, op in ops if op and op.alive} - set(mutants)):
        wrong.append((name, 0, "no input tells the model from its wrong version"))
    at += 2 * len(refuted)
    for j, name in enumerate(strangers):
        if f"Unknown libcall: @{by_name[name].intrinsic}" not in (outputs[at + j] or ""):
            wrong.append((name, 0, "Alive2 knows it now: say so in tests/x86ops.py, so it's checked"))
    proved, unknown = 0, []
    for j, (name, k, _, _) in enumerate(jobs):
        verdicts = [
            alive_verdict("the operation refines the model", outputs[2 * j]),
            alive_verdict("the model refines the operation", outputs[2 * j + 1]),
        ]
        if fails := [v for v in verdicts if v and v[0] == "fail"]:
            wrong.append((name, k, f"{fails[0][1]}:\n{fails[0][2]}"))
        elif skips := [v for v in verdicts if v]:
            unknown.append((name, k, skips[0][1]))
        else:
            proved += 1
    return proved, len(jobs), len(mutants), wrong, unknown


def lanes_of(value, n, w):
    """A constant `opt` printed, as lanes, each a number below 2^w, POISON or UNDEF. None if it isn't one."""
    count = max(n, 1)
    if value == "zeroinitializer":
        lanes = [0] * count
    elif value in ("poison", "undef"):
        lanes = [value] * count
    elif s := re.fullmatch(r"splat \(i\d+ (\S+)\)", value):
        lanes = [s.group(1)] * count
    elif value.startswith("<"):
        lanes = [x.split()[1] for x in value[1:-1].split(", ")]
    elif n == 0 and re.fullmatch(r"-?\d+|true|false", value):
        lanes = [value]
    else:
        return None
    return [lane_value(x, w) for x in lanes]


def lane_value(x, w):
    if x == "poison":
        return POISON
    if x == "undef":
        return UNDEF
    if x in ("true", "false"):
        return int(x == "true")
    return int(x) & ((1 << w) - 1)


def operands(text):
    """The operands of a call `opt` printed, split at the commas between them."""
    out, depth, start = [], 0, 0
    for i, c in enumerate(text):
        depth += (c in "<(") - (c in ">)")
        if c == "," and depth == 0:
            out.append(text[start:i].strip())
            start = i + 1
    return [*out, text[start:].strip()]


def simplified(ops, all_cases, work):
    """What InstCombine makes of each call on constants. For each case: ("constant", lanes) if it folds,
    ("call", operands) if it leaves the call with other constant operands, and None if it leaves it alone or
    makes anything else of it."""
    functions = [src.replace("@F()", f"@{name}__{k}()") for name, k, _, src in calls(ops, all_cases)]
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write(declarations() + "\n" + "\n".join(functions))
    # x86's own folds only run for an x86 target.
    text = sh(["opt", f"-mtriple={TRIPLE}", "-passes=instcombine", "-S", path]).out
    bodies = {
        m.group(1): m.group(2).strip()
        for m in re.finditer(r"define \S+(?: x \S+>)? @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", text)
    }
    out = []
    for (name, ret, args, _, op), cs in zip(ops, all_cases, strict=True):
        row = []
        for k, case in enumerate(cs):
            body, found = bodies.get(f"{name}__{k}", ""), None
            if r := re.fullmatch(r"ret \S+(?: x \S+>)? (.*)", body):
                if (lanes := lanes_of(r.group(1), *ret)) is not None:
                    found = ("constant", lanes)
            elif op and (
                c := re.fullmatch(r"%r = (?:tail )?call [^@]*@([\w.]+)\((.*)\)\n\s*ret .* %r", body)
            ):
                given = [o.split(" ", 3 if o.startswith("<") else 1)[-1] for o in operands(c.group(2))]
                new = [lanes_of(v, *shape) for v, shape in zip(given, args, strict=False)]
                if c.group(1) == op.intrinsic and None not in new and not any(UNDEF in x for x in new):
                    found = ("call", new) if new != case else None
            row.append(found)
        out.append(row)
    return out


def check_folder(ops, all_cases, results, found, rewritten):
    """Every lane the model gives a value has to fold to it, and where InstCombine only replaced operands,
    `rewritten` is what the model gives on the new ones, which has to keep every value. Both can fail: for
    each intrinsic InstCombine folds, the fold has to differ from what the wrong version gives on some input,
    and for each whose operands it replaces, the wrong version has to lose a value on some input."""
    agreed = refined = unfolded = kept = 0
    wrong = []
    # For each intrinsic, whether InstCombine folds it or replaces its operands, and whether that refuted
    # the wrong version.
    refuted = {}
    for (name, _, _, _, op), cs, rs, fs, ws in zip(ops, all_cases, results, found, rewritten, strict=True):
        folds = False
        again = iter(ws)
        for k, case in enumerate(cs):
            (model, twin), fold = rs[k], fs[k]
            if fold and fold[0] == "call":
                after, after_twin = next(again)
                for lane, (m, a) in enumerate(zip(model, after, strict=True)):
                    if m not in (POISON, a):
                        why = f"lane {lane}: the model gives {m}, and {a} on the operands LLVM leaves"
                        wrong.append((name, k, why))
                kept += 1
                lost = any(t not in (POISON, a) for t, a in zip(twin, after_twin, strict=True))
                refuted[op.intrinsic, "replaces"] = refuted.get((op.intrinsic, "replaces"), False) or lost
                continue
            if fold is None or isinstance(model, str):
                unfolded += 1
                continue
            for lane, (m, f) in enumerate(zip(model, fold[1], strict=True)):
                if m == POISON or f == UNDEF:
                    refined += 1
                elif m == f:
                    agreed += 1
                else:
                    wrong.append((name, k, f"lane {lane}: the model gives {m}, and LLVM folds it to {f}"))
            if op and not any(POISON in lanes for lanes in case):
                folds = True
                differs = any(t not in (POISON, f) and f != UNDEF for t, f in zip(twin, fold[1], strict=True))
                refuted[op.intrinsic, "folds"] = refuted.get((op.intrinsic, "folds"), False) or differs
        if op and folds != op.folds:
            says = "folds it on inputs without poison" if folds else "doesn't fold it"
            wrong.append((name, 0, f"InstCombine {says}: say so in tests/x86ops.py"))
    for (intrinsic, how), done in sorted(refuted.items()):
        if not done:
            wrong.append(
                (intrinsic, 0, f"InstCombine {how}, and no input tells the model from its wrong version")
            )
    return agreed, refined, unfolded, kept, sum(refuted.values()), wrong


def main():
    tool = os.path.abspath(sys.argv[1])
    if not shutil.which("alive-tv"):
        sys.exit("FAIL  alive-tv isn't on PATH")
    rand = random.Random(13)
    ops = operations()
    all_cases = [cases(args, op, rand) for _, _, args, _, op in ops]
    work = tempfile.mkdtemp(prefix="x86check-")
    try:
        found = simplified(ops, all_cases, work)
        # The operands InstCombine replaced a call's with are inputs too, after each operation's own.
        again = [[f[1] for f in fs if f and f[0] == "call"] for fs in found]
        results = eval_in_lean(
            tool, ops, [cs + more for cs, more in zip(all_cases, again, strict=True)], work
        )
        rewritten = [rs[len(cs) :] for rs, cs in zip(results, all_cases, strict=True)]
        results = [rs[: len(cs)] for rs, cs in zip(results, all_cases, strict=True)]
        total = sum(len(cs) for cs in all_cases)
        print(f"{len(ops)} operations, {total} inputs")
        agreed, refined, unfolded, kept, refuted, fwrong = check_folder(
            ops, all_cases, results, found, rewritten
        )
        print(
            f"constant folder: {agreed} lanes agree, {refined} where the model is poison and LLVM refines "
            f"it, {kept} inputs whose operands LLVM replaces and the model keeps its values, {unfolded} "
            f"inputs not folded, the wrong version of each of {refuted} intrinsics refuted, "
            f"{len(fwrong)} wrong"
        )
        proved, asked, mutants, awrong, unknown = check_alive(ops, all_cases, results, work)
        print(
            f"alive2: {proved} of {asked} inputs proved exact in both directions, a wrong result for each "
            f"operation refuted, and the wrong version of each of {mutants} intrinsics, {len(awrong)} wrong, "
            f"{len(unknown)} it couldn't check"
        )
        only = sorted({op.intrinsic for *_, op in ops if op and not op.alive and not op.folds})
        print(f"neither computes {len(only)} intrinsics, which only the processor checks: {' '.join(only)}")
        for name, k, why in (fwrong + awrong)[:20]:
            print(f"  WRONG {name}, input {k}: {why[:800]}")
        for name, k, why in unknown[:8]:
            print(f"  unknown {name}, input {k}: {why.strip()[:200]}")
        failed = bool(fwrong or awrong or unknown) or proved != asked or not agreed
        print("FAIL" if failed else "ok")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
