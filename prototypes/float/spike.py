#!/usr/bin/env python3
"""Measures `bv_decide` on FloatSpike's operations, for docs/float.md.

Writes one Lean file per goal and format, each a theorem closed by `bv_decide`, and runs each in a Lean
process of its own through tools/measure.py, which records its wall time and peak memory and holds a slot in
the machine's pool of heavy jobs. A goal that runs out of time or memory is recorded as that, never as
proved.

usage: prototypes/float/spike.py OUT.jsonl [--timeout S] [--memory MB] [--only NAME ...]

Run it in `nix develop`, from anywhere. It compiles FloatSpike.lean first, into a temporary directory.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent

FORMATS = {"half": (5, 10), "bfloat": (8, 7), "float": (8, 23), "double": (11, 52)}

# Each goal is a theorem statement about `a` and `b`, in a format of `e` exponent and `m` fraction bits.
# `keep a` is the NaN choice that returns `a` unchanged, with its own sign. `swap k` is the choice `k` with
# the operands swapped.
PRELUDE = """import FloatSpike
open FloatSpike

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The NaN choice that returns the first operand unchanged, with its sign. -/
@[bv_normalize] def keep (a : BitVec {w}) : BitVec 4 := (BitVec.ofBool a.msb).setWidth 4 ||| 0b0110#4

/-- The NaN choice `k` with the operands swapped. -/
@[bv_normalize] def swap (k : BitVec 4) : BitVec 4 :=
  let sel := k.extractLsb' 2 2
  let sel' := if sel == 1#2 then 2#2 else if sel == 2#2 then 1#2 else sel
  (sel' ++ k.extractLsb' 0 2)

/-- The predicate with `<` and `>` swapped. -/
@[bv_normalize] def swapPred (p : BitVec 4) : BitVec 4 :=
  (p &&& 0b1001#4) ||| ((p &&& 0b0010#4) <<< 1) ||| ((p &&& 0b0100#4) >>> 1)

/-- `1.0`, `2.0`, `0.5` and `-0.0`. -/
@[bv_normalize] def one : BitVec {w} := BitVec.ofNat _ ({bias} * 2 ^ {m})
@[bv_normalize] def two : BitVec {w} := BitVec.ofNat _ (({bias} + 1) * 2 ^ {m})
@[bv_normalize] def half' : BitVec {w} := BitVec.ofNat _ (({bias} - 1) * 2 ^ {m})
@[bv_normalize] def negZero : BitVec {w} := BitVec.ofNat _ (2 ^ ({e} + {m}))
"""

GOALS = {
    # Two whole circuits, both operands free.
    "fadd_comm": "∀ (a b : BitVec {w}) (k : BitVec 4), fadd {F} k a b = fadd {F} (swap k) b a",
    "fmul_comm": "∀ (a b : BitVec {w}) (k : BitVec 4), fmul {F} k a b = fmul {F} (swap k) b a",
    # One circuit, one operand a constant.
    "fadd_negzero": "∀ (a : BitVec {w}), fadd {F} (keep a) a negZero = a",
    "fmul_one": "∀ (a : BitVec {w}), fmul {F} (keep a) a one = a",
    "fdiv_one": "∀ (a : BitVec {w}), fdiv {F} (keep a) a one = a",
    # Two different circuits on one free operand.
    "fdiv_two": "∀ (a : BitVec {w}) (k : BitVec 4), fdiv {F} k a two = fmul {F} k a half'",
    # Comparison.
    "fcmp_swap": "∀ (a b : BitVec {w}) (p : BitVec 4), fcmp {F} p a b = fcmp {F} (swapPred p) b a",
    "fcmp_oeq_self": "∀ (a : BitVec {w}), fcmp {F} 1#4 a a = !isNaN {F} a",
    # Exactness of a known-wrong rewrite: a + b - b = a fails, so this must be refuted, not proved.
    "fadd_sub_wrong": "∀ (a b : BitVec {w}), isNaN {F} a = false → isNaN {F} b = false → "
    "isInf {F} b = false → fsub {F} 0 (fadd {F} 0 a b) b = a",
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("out", type=Path)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--memory", type=int, default=16000, help="MB, for the process tree and Lean's -M")
    ap.add_argument("--only", nargs="*", help="goal or goal:format names")
    ap.add_argument("--formats", nargs="*", default=["half", "float", "double"])
    args = ap.parse_args()
    work = Path(tempfile.mkdtemp(prefix="floatspike-"))
    subprocess.run(
        ["lean", "-M", "4000", "-o", str(work / "FloatSpike.olean"), str(HERE / "FloatSpike.lean")],
        check=True,
    )
    env = dict(os.environ, LEAN_PATH=str(work))
    for goal, stmt in GOALS.items():
        for fmt in args.formats:
            if args.only and goal not in args.only and f"{goal}:{fmt}" not in args.only:
                continue
            e, m = FORMATS[fmt]
            values = {"e": e, "m": m, "w": 1 + e + m, "bias": 2 ** (e - 1) - 1, "F": f"(e := {e}) (m := {m})"}
            src = PRELUDE.format(**values) + (
                f"\ntheorem {goal} : {stmt.format(**values)} := by\n"
                f"  intros; bv_decide (config := {{ timeout := {args.timeout} }})\n"
            )
            path = work / f"{goal}_{fmt}.lean"
            path.write_text(src)
            record = work / "record.jsonl"
            record.unlink(missing_ok=True)
            log = work / f"{goal}_{fmt}.log"
            subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "tools" / "measure.py"),
                    "run",
                    "--label",
                    f"{goal}:{fmt}",
                    "--heavy",
                    "--max-tree-rss-mb",
                    str(args.memory),
                    "--timeout",
                    str(args.timeout + 120),
                    "--out",
                    str(record),
                    "--log",
                    str(log),
                    "--",
                    "lean",
                    "-M",
                    str(args.memory),
                    str(path),
                ],
                env=env,
                check=False,
            )
            rec = json.loads(record.read_text().splitlines()[-1]) if record.exists() else {}
            text = log.read_text(errors="replace") if log.exists() else ""
            if rec.get("outcome") == "ok" and rec.get("exit") == 0:
                verdict = "proved"
            elif "The prover found a counterexample" in text or "found a counterexample" in text:
                verdict = "refuted"
            elif "timeout" in text.lower() or rec.get("outcome") in ("time_limit", "resource_limit"):
                verdict = "limit"
            else:
                verdict = "error"
            row = {
                "goal": goal,
                "format": fmt,
                "verdict": verdict,
                "record": rec,
                "output": text.strip().splitlines()[-12:],
            }
            with open(args.out, "a") as f:
                f.write(json.dumps(row) + "\n")
            print(goal, fmt, verdict, rec.get("wall_s"), rec.get("peak_tree_mb"), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
