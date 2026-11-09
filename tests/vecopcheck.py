#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks the model's lane-by-lane forms of integer operations, IRLean/Lanes.lean and IRLean/Vec.lean,
through the emitter, against LLVM itself, poison lanes and undefined behavior included: the vector forms of
the integer intrinsics, vector division and remainder, and `noundef` and `range` on vectors and structs.

Each operation runs on constant inputs: random lanes, lanes at the extremes, poison lanes, and for division, a
zero lane in the divisor and the one signed division that overflows. Two oracles:
  - Alive2. A function that runs the operation on the constants, and one that returns what the model gives, or
    is `unreachable` where the model says the run is undefined, have to refine each other both ways. So a lane
    the model makes poison has to be poison in Alive2, and a run the model calls undefined has to be undefined
    there.
  - LLVM's constant folder. Every lane the model gives a value has to fold to that value.
For each operation, a wrong result has to be refuted too, so a pass can't come from Alive2 reading something
else.

usage: tests/vecopcheck.py path/to/ir-lean
"""

import os
import random
import re
import shutil
import sys
import tempfile

import alive
from differential import NATIVE, lean_output
from opcheck import alive_verdict, lean_env, sh

sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
from irlean import proc

POISON = -1
UB = "ub"


def ty(shape):
    n, w = shape
    return f"i{w}" if n == 0 else f"<{n} x i{w}>"


def suffix(shape):
    n, w = shape
    return f"i{w}" if n == 0 else f"v{n}i{w}"


def operations():
    """Each operation as (name, result shape, argument shapes, body defining %r from %a0, %a1, ..., and the
    declarations it needs)."""
    ops = []

    def call(name, ret, args, extra="", attrs="", arg_attrs=()):
        params = ", ".join(
            f"{ty(a)} {arg_attrs[i] if i < len(arg_attrs) else ''}%a{i}".replace("  ", " ")
            for i, a in enumerate(args)
        )
        sep = ", " if extra else ""
        return f"%r = call {attrs}{ty(ret)} @{name}({params}{sep}{extra})"

    def decl(name, ret, args, extra=""):
        types = ", ".join([ty(a) for a in args] + ([extra] if extra else []))
        return f"declare {ty(ret)} @{name}({types})"

    for shape in [(4, 8), (2, 4)]:
        s = suffix(shape)
        for f in ["ctpop", "bitreverse"]:
            n = f"llvm.{f}.{s}"
            ops.append((f"{f}_{s}", shape, [shape], call(n, shape, [shape]), [decl(n, shape, [shape])]))
        for f in ["ctlz", "cttz", "abs"]:
            for flag in ["false", "true"]:
                n = f"llvm.{f}.{s}"
                ops.append(
                    (
                        f"{f}_{flag}_{s}",
                        shape,
                        [shape],
                        call(n, shape, [shape], f"i1 {flag}"),
                        [decl(n, shape, [shape], "i1")],
                    )
                )
        for f in ["fshl", "fshr"]:
            n = f"llvm.{f}.{s}"
            ops.append(
                (f"{f}_{s}", shape, [shape] * 3, call(n, shape, [shape] * 3), [decl(n, shape, [shape] * 3)])
            )
        result = (shape[0], 2)
        for f in ["ucmp", "scmp"]:
            n = f"llvm.{f}.{suffix(result)}.{s}"
            ops.append(
                (
                    f"{f}_{s}",
                    result,
                    [shape] * 2,
                    call(n, result, [shape] * 2),
                    [decl(n, result, [shape] * 2)],
                )
            )
        for f in ["uadd", "sadd", "usub", "ssub", "umul", "smul"]:
            n = f"llvm.{f}.with.overflow.{s}"
            pair = f"{{ {ty(shape)}, {ty((shape[0], 1))} }}"
            for field, out in [(0, shape), (1, (shape[0], 1))]:
                body = (
                    f"%p = call {pair} @{n}({ty(shape)} %a0, {ty(shape)} %a1)\n"
                    f"  %r = extractvalue {pair} %p, {field}"
                )
                ops.append(
                    (
                        f"{f}_overflow_{field}_{s}",
                        out,
                        [shape] * 2,
                        body,
                        [f"declare {pair} @{n}({ty(shape)}, {ty(shape)})"],
                    )
                )
        for op, flags in [("udiv", ["", "exact "]), ("sdiv", ["", "exact "]), ("urem", [""]), ("srem", [""])]:
            for f in flags:
                ops.append(
                    (
                        f"{op}_{f.strip() or 'plain'}_{s}",
                        shape,
                        [shape] * 2,
                        f"%r = {op} {f}{ty(shape)} %a0, %a1",
                        [],
                    )
                )
        umin = f"llvm.umin.{s}"
        lo, hi = 1, 1 << (shape[1] - 1)
        ops.append(
            (
                f"range_call_return_{s}",
                shape,
                [shape] * 2,
                call(umin, shape, [shape] * 2, attrs=f"range(i{shape[1]} {lo}, {hi}) "),
                [decl(umin, shape, [shape] * 2)],
            )
        )
        ops.append(
            (
                f"noundef_call_return_{s}",
                shape,
                [shape] * 2,
                call(umin, shape, [shape] * 2, attrs="noundef "),
                [decl(umin, shape, [shape] * 2)],
            )
        )
        ops.append(
            (
                f"noundef_call_argument_{s}",
                shape,
                [shape] * 2,
                call(umin, shape, [shape] * 2, arg_attrs=("noundef ",)),
                [decl(umin, shape, [shape] * 2)],
            )
        )
    for w in [8, 4]:
        pair = f"{{ i{w}, i1 }}"
        n = f"llvm.uadd.with.overflow.i{w}"
        ops.append(
            (
                f"noundef_struct_i{w}",
                (0, w),
                [(0, w), (0, w)],
                f"%p = call noundef {pair} @{n}(i{w} %a0, i{w} %a1)\n  %r = extractvalue {pair} %p, 0",
                [f"declare {pair} @{n}(i{w}, i{w})"],
            )
        )
    ops.append(
        (
            "bswap_v2i16",
            (2, 16),
            [(2, 16)],
            "%r = call <2 x i16> @llvm.bswap.v2i16(<2 x i16> %a0)",
            ["declare <2 x i16> @llvm.bswap.v2i16(<2 x i16>)"],
        )
    )
    return ops


def declarations(ops):
    return "\n".join(sorted({d for op in ops for d in op[4]})) + "\n"


def extremes(w):
    m = (1 << w) - 1
    return sorted({0, 1, m, 1 << (w - 1), (1 << (w - 1)) - 1})


def cases(name, args, rand):
    """Each case is a list of lanes for each argument, a scalar being one lane."""
    shapes = [(max(n, 1), w) for n, w in args]
    out = []
    for _ in range(8):
        out.append([[rand.getrandbits(w) for _ in range(n)] for n, w in shapes])
    for _ in range(6):
        out.append([[rand.choice(extremes(w)) for _ in range(n)] for n, w in shapes])
    for k in range(6):
        case = [[rand.getrandbits(w) for _ in range(n)] for n, w in shapes]
        i = k % len(shapes)
        case[i][rand.randrange(shapes[i][0])] = POISON
        out.append(case)
    if re.match(r"[us](div|rem)", name):
        n, w = shapes[0]
        # One divisor lane zero, the others not.
        case = [[rand.getrandbits(w) for _ in range(n)], [rand.getrandbits(w) | 1 for _ in range(n)]]
        case[1][0] = 0
        out.append(case)
        # The one signed division that overflows, in one lane.
        case = [[rand.getrandbits(w) for _ in range(n)], [1] * n]
        case[0][-1], case[1][-1] = 1 << (w - 1), (1 << w) - 1
        out.append(case)
        # No zero, poison or overflowing divisor lane: every lane defined.
        for _ in range(4):
            out.append(
                [[rand.getrandbits(w) for _ in range(n)], [rand.randrange(1, (1 << w) - 1) for _ in range(n)]]
            )
    return out


def constant(shape, lanes):
    n, w = shape

    def one(x):
        if x == POISON:
            return "poison"
        return ("true" if x else "false") if w == 1 else str(x)

    if n == 0:
        return one(lanes[0])
    return "<" + ", ".join(f"i{w} {one(x)}" for x in lanes) + ">"


def eval_in_lean(tool, ops, all_cases, work):
    ll = os.path.join(work, "ops.ll")
    with open(ll, "w") as f:
        f.write(declarations(ops))
        for name, ret, args, body, _ in ops:
            params = ", ".join(f"{ty(a)} %a{i}" for i, a in enumerate(args))
            f.write(f"\ndefine {ty(ret)} @{name}({params}) {{\n  {body}\n  ret {ty(ret)} %r\n}}\n")
    r = proc.run([tool, ll, "-o", os.path.join(work, "Ops.lean"), "--namespace", "Ops"])
    if r.exit != 0:
        sys.exit(f"the emitter left operations out:\n{r.err}")
    src = [
        "import Ops",
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
        f'  | some (.error (.undefined _)) => "{UB}"',
        '  | some (.error (.model _)) => "stop"',
        '  | _ => "diverged"',
        "def show' {n w : Nat} : Outcome (Vec n w) → String",
        '  | some (.ok v) => " ".intercalate (v.toList.map showVal)',
        "  | o => showStop o",
        "def showOne {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok v) => showVal v",
        "  | o => showStop o",
    ]
    runners = []
    for k, ((name, ret, args, _, _), cs) in enumerate(zip(ops, all_cases, strict=True)):
        src.append(f"def cases{k} : List (List (List Int)) := {cs}")
        call = " ".join(
            f"(val (w := {w}) c[{i}]!)" if n == 0 else f"(lanes (n := {n}) (w := {w}) c[{i}]!)"
            for i, (n, w) in enumerate(args)
        )
        shows = "showOne" if ret[0] == 0 else "show'"
        src.append(f"def r{k} : IO Unit := for c in cases{k} do IO.println ({shows} (Ops.{name} {call}))")
        runners.append(f"r{k}")
    src.append("def main : IO Unit := do\n  for r in [" + ", ".join(runners) + "] do r")
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_ops():
        sh(
            ["lean", "-R", work, "-o", os.path.join(work, "Ops.olean"), os.path.join(work, "Ops.lean")],
            env=env,
        )

    lines = lean_output(work, ["lean", *NATIVE, "--run", path], env, compile_ops).splitlines()
    if len(lines) != sum(len(cs) for cs in all_cases):
        sys.exit("Lean printed the wrong number of results")
    results, pos = [], 0
    for cs in all_cases:
        results.append(
            [
                [int(x) for x in line.split()] if re.fullmatch(r"[\d -]+", line) else line
                for line in lines[pos : pos + len(cs)]
            ]
        )
        pos += len(cs)
    return results


def calls(ops, all_cases):
    """For each case, the operation on its constant inputs as a function @F."""
    out = []
    for (name, ret, args, body, _), cs in zip(ops, all_cases, strict=True):
        for k, c in enumerate(cs):
            text = body
            for i, (shape, lanes) in enumerate(zip(args, c, strict=True)):
                text = re.sub(rf"%a{i}\b", constant(shape, lanes), text)
            out.append((name, k, ret, f"define {ty(ret)} @F() {{\n  {text}\n  ret {ty(ret)} %r\n}}\n"))
    return out


def returns(shape, result):
    if result == UB:
        return f"define {ty(shape)} @F() {{\n  unreachable\n}}\n"
    return f"define {ty(shape)} @F() {{\n  ret {ty(shape)} {constant(shape, result)}\n}}\n"


def wrong_result(shape, result):
    """A result Alive2 has to refute: lane 0 changed, or a value where the model says undefined."""
    if result == UB:
        return [0] * max(shape[0], 1)
    return [0 if result[0] == POISON else (result[0] + 1) % (1 << shape[1]), *result[1:]]


def check_alive(ops, all_cases, results):
    jobs, wrong, controls = [], [], {}
    for (name, k, ret, src), result in zip(
        calls(ops, all_cases), [r for rs in results for r in rs], strict=True
    ):
        if isinstance(result, str) and result != UB:
            wrong.append((name, k, f"the model gives {result}"))
            continue
        jobs.append((name, k, src, returns(ret, result)))
        if name not in controls and result != UB:
            controls[name] = (src, returns(ret, wrong_result(ret, result)))
    work = tempfile.mkdtemp(prefix="vecopcheck-alive-")
    try:
        pairs = [pair for _, _, src, tgt in jobs for pair in ((src, tgt), (tgt, src))]
        pairs += [pair for src, tgt in controls.values() for pair in ((src, tgt), (tgt, src))]
        # Both ways round, so an input the operation is undefined on is checked without --fail-src-ub.
        outputs = alive.refinements(declarations(ops), pairs, work, alive.BOTH_WAYS)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    for j, name in enumerate(controls):
        verdicts = [alive_verdict("", outputs[2 * len(jobs) + 2 * j + d]) for d in (0, 1)]
        if not any(v and v[0] == "fail" for v in verdicts):
            wrong.append((name, 0, "Alive2 doesn't find a wrong result wrong"))
    missing = sorted({op[0] for op in ops} - set(controls))
    for name in missing:
        wrong.append((name, 0, "no input the model gives a value for, so no wrong result to refute"))
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
    return proved, wrong, unknown


def folded(text):
    """Each function's returned constant, as lanes, from what `opt` printed, for those it folded."""
    out = {}
    for m in re.finditer(r"define (<(\d+) x i(\d+)>|i(\d+)) @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", text):
        n = int(m.group(2) or 0)
        w = int(m.group(3) or m.group(4))
        fn, body = m.group(5), m.group(6).strip()
        r = re.fullmatch(r"ret \S+(?: x \S+>)? (.*)", body)
        if not r:
            continue
        value = r.group(1)
        count = max(n, 1)
        if value == "zeroinitializer":
            lanes = [0] * count
        elif value == "poison":
            lanes = [POISON] * count
        elif s := re.fullmatch(r"splat \(i\d+ (\S+)\)", value):
            lanes = [s.group(1)] * count
        elif value.startswith("<"):
            lanes = [x.split()[1] for x in value[1:-1].split(", ")]
        elif n == 0:
            lanes = [value]
        else:
            continue
        out[fn] = [lane_value(x, w) for x in lanes]
    return out


def lane_value(x, w):
    if x in (POISON, "poison"):
        return POISON
    if x in ("true", "false"):
        return int(x == "true")
    return int(x) & ((1 << w) - 1)


def check_folder(ops, all_cases, results, work):
    functions = [src.replace("@F()", f"@{name}__{k}()") for name, k, _, src in calls(ops, all_cases)]
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write(declarations(ops) + "\n" + "\n".join(functions))
    found = folded(sh(["opt", "-passes=instcombine", "-S", path]).out)
    agreed = refined = unfolded = 0
    wrong = []
    for (name, *_), cs, rs in zip(ops, all_cases, results, strict=True):
        for k in range(len(cs)):
            fold, model = found.get(f"{name}__{k}"), rs[k]
            if fold is None or isinstance(model, str):
                unfolded += 1
                continue
            for lane, (m, f) in enumerate(zip(model, fold, strict=True)):
                if m == POISON:
                    refined += 1
                elif m == f:
                    agreed += 1
                else:
                    wrong.append((name, k, f"lane {lane}: the model gives {m}, and LLVM folds it to {f}"))
    return agreed, refined, unfolded, wrong


def main():
    tool = os.path.abspath(sys.argv[1])
    if not shutil.which("alive-tv"):
        sys.exit("FAIL  alive-tv isn't on PATH")
    rand = random.Random(29)
    ops = operations()
    all_cases = [cases(name, args, rand) for name, _, args, _, _ in ops]
    work = tempfile.mkdtemp(prefix="vecopcheck-")
    try:
        results = eval_in_lean(tool, ops, all_cases, work)
        total = sum(len(cs) for cs in all_cases)
        ub = sum(r == UB for rs in results for r in rs)
        print(f"{len(ops)} operations, {total} inputs, {ub} of them undefined in the model")
        agreed, refined, unfolded, fwrong = check_folder(ops, all_cases, results, work)
        print(
            f"constant folder: {agreed} lanes agree, {refined} where the model is poison and LLVM refines "
            "it, "
            f"{unfolded} inputs not folded or undefined, {len(fwrong)} wrong"
        )
        proved, awrong, unknown = check_alive(ops, all_cases, results)
        print(
            f"alive2: {proved} of {total} inputs proved exact in both directions, and a wrong result for "
            "each "
            f"operation refuted, {len(awrong)} wrong, {len(unknown)} it couldn't check"
        )
        for name, k, why in (fwrong + awrong)[:20]:
            print(f"  WRONG {name}, input {k}: {why[:800]}")
        for name, k, why in unknown[:8]:
            print(f"  unknown {name}, input {k}: {why.strip()[:200]}")
        failed = bool(fwrong or awrong or unknown) or proved != total or not agreed or not ub
        print("FAIL" if failed else "ok")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
