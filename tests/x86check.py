#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks the model's `bitcast` between integers and vectors of them, and x86's PMADDUBSW and PMADDWD,
through the emitter, against LLVM itself, poison included, on any processor.

tests/real/x86.ll runs these and VPDPBUSD natively, which needs AVX-512 VNNI and can't see poison. This asks
two oracles that need neither, for each operation at every width the q4_K kernels use and more, on random
inputs, inputs at the extremes, where PMADDUBSW saturates and PMADDWD wraps, and inputs with poison lanes:
  - Alive2. A function that calls the operation on constant inputs, and one that returns what the model gives,
    have to refine each other both ways, so the model is exactly as poisonous as Alive2, lane by lane.
  - LLVM's constant folder, with x86's own folds. Every lane the model gives a value has to fold to that
    value. A lane the model makes poison may fold to anything, since that only refines it.
Neither knows VPDPBUSD, so it isn't checked here.

usage: tests/x86check.py path/to/ir-lean
"""

import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

import alive
from differential import NATIVE, lean_output
from opcheck import alive_verdict, lean_env, sh

TRIPLE = "x86_64-unknown-linux-gnu"
# Stands for a poison lane.
POISON = -1


# Each intrinsic, its result shape and its arguments' shapes, each (lanes, width).
INTRINSICS = [
    ("llvm.x86.ssse3.pmadd.ub.sw.128", (8, 16), [(16, 8), (16, 8)]),
    ("llvm.x86.avx2.pmadd.ub.sw", (16, 16), [(32, 8), (32, 8)]),
    ("llvm.x86.avx512.pmaddubs.w.512", (32, 16), [(64, 8), (64, 8)]),
    ("llvm.x86.sse2.pmadd.wd", (4, 32), [(8, 16), (8, 16)]),
    ("llvm.x86.avx2.pmadd.wd", (8, 32), [(16, 16), (16, 16)]),
    ("llvm.x86.avx512.pmaddw.d.512", (16, 32), [(32, 16), (32, 16)]),
]
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


def ty(shape):
    return f"i{shape[1]}" if shape[0] == 0 else f"<{shape[0]} x i{shape[1]}>"


def label(shape):
    return f"i{shape[1]}" if shape[0] == 0 else f"{shape[0]}x{shape[1]}"


def operations():
    """Each operation as (name, result shape, argument shapes, the instruction on %a0, %a1, ...)."""
    ops = []
    for name, ret, args in INTRINSICS:
        params = ", ".join(f"{ty(a)} %a{i}" for i, a in enumerate(args))
        ops.append((re.sub(r"\W", "_", name[5:]), ret, args, f"call {ty(ret)} @{name}({params})"))
    for src, dst in BITCASTS:
        ops.append(
            (
                f"bitcast_{label(src)}_{label(dst)}",
                dst,
                [src],
                f"bitcast {ty(src)} %a0 to {ty(dst)}",
            )
        )
    return ops


def declarations():
    return "".join(
        f"declare {ty(ret)} @{name}({', '.join(ty(a) for a in args)})\n" for name, ret, args in INTRINSICS
    )


def extremes(w):
    m = (1 << w) - 1
    return sorted({0, 1, m, 1 << (w - 1), (1 << (w - 1)) - 1, 0x0F & m, 0x80 & m})


def cases(name, args, rand):
    """Random inputs, inputs at the extremes and where the operation saturates or wraps, and inputs with
    poison lanes. Each is a list of lanes for each argument."""
    out = []
    args = [(max(n, 1), w) for n, w in args]
    for _ in range(6):
        out.append([[rand.getrandbits(w) for _ in range(n)] for n, w in args])
    for _ in range(4):
        out.append([[rand.choice(extremes(w)) for _ in range(n)] for n, w in args])
    if "pmadd_ub_sw" in name or "pmaddubs" in name:
        # 255 times 127, twice, is past 32767, and 255 times -128, twice, is below -32768.
        out.append([[255] * args[0][0], [127] * args[1][0]])
        out.append([[255] * args[0][0], [128] * args[1][0]])
    if "pmadd_wd" in name or "pmaddw_d" in name:
        # -32768 times -32768, twice, is 2^31, which wraps.
        out.append([[0x8000] * args[0][0], [0x8000] * args[1][0]])
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
    """What the model gives for each case: a list of lanes, each a number or POISON, or why it gave none."""
    ll = os.path.join(work, "ops.ll")
    with open(ll, "w") as f:
        f.write(declarations())
        for name, ret, args, instruction in ops:
            params = ", ".join(f"{ty(a)} %a{i}" for i, a in enumerate(args))
            f.write(
                f"\ndefine {ty(ret)} @{name}({params}) {{\n  %r = {instruction}\n  ret {ty(ret)} %r\n}}\n"
            )
    r = subprocess.run(
        [tool, ll, "-o", os.path.join(work, "Ops.lean"), "--namespace", "Ops"],
        text=True,
        capture_output=True,
        check=False,
    )
    if r.returncode != 0:
        sys.exit(f"the emitter left operations out:\n{r.stderr}")
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
        '  | some (.error (.undefined _)) => "ub"',
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
    for k, ((name, ret, args, _), cs) in enumerate(zip(ops, all_cases, strict=True)):
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
    """For each case, the operation on its constant inputs as a function @F, with its result shape."""
    out = []
    for (name, ret, args, instruction), cs in zip(ops, all_cases, strict=True):
        for k, c in enumerate(cs):
            body = instruction
            for i, (shape, lanes) in enumerate(zip(args, c, strict=True)):
                body = body.replace(f"{ty(shape)} %a{i}", f"{ty(shape)} {constant(shape, lanes)}")
            out.append((name, k, ret, f"define {ty(ret)} @F() {{\n  %r = {body}\n  ret {ty(ret)} %r\n}}\n"))
    return out


def returns(shape, lanes):
    return f"define {ty(shape)} @F() {{\n  ret {ty(shape)} {constant(shape, lanes)}\n}}\n"


def check_alive(ops, all_cases, results, work):
    """Each case, the call and what the model returns, refining each other both ways. And for each operation,
    a control: its first input with a lane 0 changed, from a value to the next one or from poison to 0, which
    Alive2 has to find wrong, so a pass can't come from Alive2 reading something else."""
    jobs, wrong, controls = [], [], {}
    for (name, k, ret, src), result in zip(
        calls(ops, all_cases), [r for rs in results for r in rs], strict=True
    ):
        if isinstance(result, str):
            wrong.append((name, k, f"the model gives {result}"))
            continue
        jobs.append((name, k, src, returns(ret, result)))
        if name not in controls:
            changed = [0 if result[0] == POISON else (result[0] + 1) % (1 << ret[1]), *result[1:]]
            controls[name] = (src, returns(ret, changed))
    pairs = [pair for _, _, src, tgt in jobs for pair in ((src, tgt), (tgt, src))]
    pairs += [pair for src, tgt in controls.values() for pair in ((src, tgt), (tgt, src))]
    outputs = alive.refinements(declarations(), pairs, work)
    for j, name in enumerate(controls):
        verdicts = [alive_verdict("", outputs[2 * len(jobs) + 2 * j + d]) for d in (0, 1)]
        if not any(v and v[0] == "fail" for v in verdicts):
            wrong.append((name, 0, "Alive2 doesn't find a wrong result wrong"))
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
    for m in re.finditer(r"define <(\d+) x i(\d+)> @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", text):
        n, w, fn, body = int(m.group(1)), int(m.group(2)), m.group(3), m.group(4).strip()
        r = re.fullmatch(r"ret <\d+ x i\d+> (.*)", body)
        if not r:
            continue
        value = r.group(1)
        if value == "zeroinitializer":
            lanes = [0] * n
        elif value == "poison":
            lanes = [POISON] * n
        elif s := re.fullmatch(r"splat \(i\d+ (\S+)\)", value):
            lanes = [s.group(1)] * n
        elif value.startswith("<"):
            lanes = [x.split()[1] for x in value[1:-1].split(", ")]
        else:
            continue
        out[fn] = [lane_value(x, w) for x in lanes]
    for m in re.finditer(r"define i(\d+) @(\w+)\(\) [^{]*\{\n\s*ret i\d+ (\S+)\n\}", text):
        out[m.group(2)] = [lane_value(m.group(3), int(m.group(1)))]
    return out


def lane_value(x, w):
    """A lane `opt` printed, as a number below 2^w, or POISON."""
    if x in (POISON, "poison"):
        return POISON
    if x in ("true", "false"):
        return int(x == "true")
    return int(x) & ((1 << w) - 1)


def check_folder(ops, all_cases, results, work):
    """Every lane the model gives a value has to fold to it."""
    functions = [src.replace("@F()", f"@{name}__{k}()") for name, k, _, src in calls(ops, all_cases)]
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write(declarations() + "\n" + "\n".join(functions))
    found = folded(sh(["opt", f"-mtriple={TRIPLE}", "-passes=instcombine", "-S", path]).stdout)
    agreed = refined = unfolded = 0
    wrong = []
    for (name, _, _, _), cs, rs in zip(ops, all_cases, results, strict=True):
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
    rand = random.Random(13)
    ops = operations()
    all_cases = [cases(name, args, rand) for name, _, args, _ in ops]
    work = tempfile.mkdtemp(prefix="x86check-")
    try:
        results = eval_in_lean(tool, ops, all_cases, work)
        total = sum(len(cs) for cs in all_cases)
        print(f"{len(ops)} operations, {total} inputs")
        agreed, refined, unfolded, fwrong = check_folder(ops, all_cases, results, work)
        print(
            f"constant folder: {agreed} lanes agree, {refined} where the model is poison and LLVM refines "
            f"it, {unfolded} inputs not folded, {len(fwrong)} wrong"
        )
        proved, awrong, unknown = check_alive(ops, all_cases, results, work)
        print(
            f"alive2: {proved} of {total} inputs proved exact in both directions, and a wrong result for "
            f"each operation refuted, {len(awrong)} wrong, {len(unknown)} it couldn't check"
        )
        for name, k, why in (fwrong + awrong)[:20]:
            print(f"  WRONG {name}, input {k}: {why[:800]}")
        for name, k, why in unknown[:8]:
            print(f"  unknown {name}, input {k}: {why.strip()[:200]}")
        failed = bool(fwrong or awrong or unknown) or proved != total or not agreed
        print("FAIL" if failed else "ok")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
