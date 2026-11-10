#!/usr/bin/env python3
"""tests/alive.py's verdicts on three small rewrites: a right one is correct, a wrong one is incorrect, and
one whose source is undefined on every input is unknown, never correct. Without `--fail-src-ub`, alive-tv
counts that last one correct, since any target refines a source that's always undefined. Each is asked through
`run` and through `refinements`, with a fresh cache of what's proved, so a pair proved under other flags can't
answer.
Fails without alive-tv on PATH."""

import os
import shutil
import sys
import tempfile
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import alive

# What a crashed alive-tv may have printed before it died: f0's result, said correct, and no summary. Without
# the signal check in `run`, `proved` would read f0 as proved from this.
PARTIAL_THEN_CRASH = (
    "-" * 40 + "\n"
    "define i8 @f0(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n=>\n"
    "define i8 @f0(i8 %x) {\n  %r = shl i8 %x, 1\n  ret i8 %r\n}\n\n"
    f"{alive.CORRECT}\n\n"
)

RIGHT = (
    "define i8 @F(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n",
    "define i8 @F(i8 %x) {\n  %r = shl i8 %x, 1\n  ret i8 %r\n}\n",
)
WRONG = (
    "define i8 @F(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n",
    "define i8 @F(i8 %x) {\n  %r = shl i8 %x, 2\n  ret i8 %r\n}\n",
)
# `udiv` by 0 is undefined for every %x, so any target refines it, even one that returns a constant.
ALWAYS_UB = (
    "define i8 @F(i8 %x) {\n  %r = udiv i8 %x, 0\n  ret i8 %r\n}\n",
    "define i8 @F(i8 %x) {\n  ret i8 7\n}\n",
)
CASES = [
    ("right", RIGHT, "correct"),
    ("wrong", WRONG, "incorrect"),
    ("source always UB", ALWAYS_UB, "unknown"),
]


def main() -> int:
    if not shutil.which("alive-tv"):
        print("FAIL  alive-tv is not on PATH")
        return 1
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        alive.PROVED = os.path.join(work, "alive-proved")
        alive.RESULTS = work
        for name, (src, tgt), want in CASES:
            output = alive.run(src, tgt, work)
            got = alive.verdict(output)
            if got != want:
                print(f"FAIL  {name}: alive.run says {got}, not {want}:\n{output[-1200:]}")
                failed += 1
            elif name == "source always UB" and "Source function is always UB" not in output:
                print(f"FAIL  {name}: unknown, but not because the source is always UB:\n{output[-1200:]}")
                failed += 1
            else:
                print(f"ok    {name}: {got}")
        outputs = alive.refinements("", [pair for _, pair, _ in CASES], work)
        for (name, _, want), output in zip(CASES, outputs, strict=True):
            got = alive.verdict(output)
            if got != want:
                print(f"FAIL  {name}: alive.refinements says {got}, not {want}")
                failed += 1
            else:
                print(f"ok    {name}, through refinements: {got}")
        # A second time, from the cache: only the right rewrite may be remembered as proved.
        again = alive.refinements("", [pair for _, pair, _ in CASES], work)
        if [o is None for o in again] != [True, False, False]:
            held = [o is None for o in again]
            print(f"FAIL  the cache of what's proved holds {held}, not [True, False, False]")
            failed += 1
        else:
            print("ok    only the right rewrite is cached as proved")
        # A crash is not clean evidence: alive-tv ending abnormally after it printed `correct` for some
        # functions mustn't let `proved` read them as proved. This holds for a signal death (-6) and for a
        # crash/error exit code (134, 255), which a negative-only guard would have missed.
        for exit_code in (-6, 134, 255):
            crashed = alive.proc.Ran(["alive-tv"], exit_code, PARTIAL_THEN_CRASH.encode(), b"", 0.1)
            with mock.patch.object(alive.proc, "run", return_value=crashed):
                out = alive.run(RIGHT[0], RIGHT[1], work)
            if not out.startswith("ERROR:") or alive.proved(out) or alive.verdict(out) != "unknown":
                print(
                    f"FAIL  alive-tv exit {exit_code} read as evidence: proved={alive.proved(out)}, {out!r}"
                )
                failed += 1
            else:
                print(f"ok    alive-tv exit {exit_code} proves nothing")
    total = 2 * len(CASES) + 4
    print(f"{total - failed} of {total} checks passed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
