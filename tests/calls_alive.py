#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Alive2's verdict on each rewrite in tests/calls, against the theorem of its name in
tests/calls/CallsModel.lean.

Each case is a file with `@src`, `@tgt` and the declarations they call. Its first line is the model's
verdict, `; correct` or `; incorrect`, which the theorem of the file's name has to state: `Refines` for a
correct one, and its negation for an incorrect one. Alive2 has to give the same verdict, unless the second
line says it doesn't and why: `; alive2: correct: REASON`. Those are where the model and Alive2 differ by
design, as docs/calls.md lists. Anything but a proof or a counterexample, such as a timeout, is a failure,
not agreement. Alive2 runs with `undef` inputs off, since an argument of the model is a value or poison, one
process at a time. Run by tests/calls.sh."""

import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alive
from undef_freeze_alive import statement

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
from irlean import proc  # noqa: E402

CASES = os.path.join(ROOT, "tests", "calls")
MODEL = os.path.join(CASES, "CallsModel.lean")
TIMEOUT_SECONDS = 120
# What both sides are renamed: a name no case gives a callee.
PAIR = "pair"
VERDICTS = ("correct", "incorrect")


def side(text, keep, drop):
    """The module with `@drop` left out and `@keep` renamed `@pair`, so `alive-tv` pairs the two sides across
    two files, each with the declarations both call. It only prints the summary `alive.verdict` reads for two
    files."""
    text = re.sub(rf"^define [^@\n]*@{drop}\(.*?^\}}\n", "", text, flags=re.M | re.S)
    return text.replace(f"@{keep}(", f"@{PAIR}(")


def check(path, lean, work):
    """None if the theorem states the case's verdict and Alive2 gives the one the case says it does, and
    otherwise why not."""
    name = os.path.basename(path).removesuffix(".ll")
    with open(path) as f:
        lines = f.read().split("\n")
    expected = lines[0].removeprefix(";").strip()
    if expected not in VERDICTS:
        return f"its first line says {expected!r}, not correct or incorrect"
    differs = re.match(r";\s*alive2:\s*(\w+):\s*(\S.*)$", lines[1] if len(lines) > 1 else "")
    alive2 = differs.group(1) if differs else expected
    if alive2 not in VERDICTS or (differs and alive2 == expected):
        return f"its second line names {alive2!r} as Alive2's verdict, which has to be the other one"
    if f"@{PAIR}(" in "\n".join(lines):
        return f"it names something @{PAIR}, which both sides are renamed to for Alive2"
    claim = statement(lean, name)
    if claim is None:
        return "no theorem of its name"
    if claim.startswith("¬") != (expected == "incorrect") or not re.match(r"¬?\s*Refines\b", claim):
        return f"the theorem doesn't state that it's {expected}: {' '.join(claim.split())}"
    with open(path) as f:
        text = f.read()
    files = [os.path.join(work, f"{name}.{keep}.ll") for keep in ("src", "tgt")]
    for file, (keep, drop) in zip(files, (("src", "tgt"), ("tgt", "src")), strict=True):
        with open(file, "w") as f:
            f.write(side(text, keep, drop))
    r = proc.run(["alive-tv", "--disable-undef-input", "--smt-to=20000", *files], timeout=TIMEOUT_SECONDS)
    output = f"alive-tv didn't finish in {TIMEOUT_SECONDS} s" if r.limit == "time_limit" else r.out + r.err
    got = alive.verdict(output)
    if got != alive2:
        return (
            f"Alive2 says {got}, and the case says it {'differs' if differs else 'agrees'}:\n{output[-1500:]}"
        )
    return None


def main():
    if len(sys.argv) > 1:
        sys.exit("usage: tests/calls_alive.py")
    with open(MODEL) as f:
        lean = f.read()
    paths = [os.path.join(CASES, n) for n in sorted(os.listdir(CASES)) if n.endswith(".ll")]
    if not paths:
        sys.exit(f"no cases in {CASES}")
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        for path in paths:
            name = os.path.basename(path).removesuffix(".ll")
            problem = check(path, lean, work)
            if problem is None:
                print(f"ok    Alive2 gives the verdict the case says: {name}")
            else:
                print(f"FAIL  {name}: {problem}")
                failed += 1
    print(f"{len(paths) - failed} of {len(paths)} rewrites: Alive2 agrees, or differs as the case says")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
