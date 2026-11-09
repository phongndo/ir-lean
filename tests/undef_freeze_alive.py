#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Alive2's verdict on each rewrite in tests/undef_freeze/alive2, against the experimental semantics' own.

Each case is a file with `@src` and `@tgt`, whose first line is the verdict, `; correct` or `; incorrect`,
and whose name is a theorem in tests/undef_freeze/UndefFreezeTests.lean that proves `Refines` for a correct
one, or its negation for an incorrect one. Alive2 runs with `undef` inputs allowed, since the semantics
quantifies over them, one process at a time. Anything but a proof or a counterexample, such as a timeout, is
a failure, not agreement. Run by tests/undef_freeze.sh."""

import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alive

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CASES = os.path.join(ROOT, "tests", "undef_freeze", "alive2")
TESTS = os.path.join(ROOT, "tests", "undef_freeze", "UndefFreezeTests.lean")
TIMEOUT_SECONDS = 120


def functions(text):
    """The text of `@src` and of `@tgt`, each renamed `@f`, so `alive-tv` pairs them across two files."""
    found = {}
    for m in re.finditer(r"^define [^@]*@(src|tgt)\(.*?^\}\n", text, flags=re.M | re.S):
        found[m.group(1)] = m.group(0).replace(f"@{m.group(1)}(", "@f(", 1)
    return found.get("src"), found.get("tgt")


def statement(lean, name):
    """What the theorem `name` concludes, after its hypotheses and up to `:=`, or None if there's no such
    theorem."""
    m = re.search(rf"^theorem {re.escape(name)}\b(.*?):=", lean, flags=re.M | re.S)
    if not m:
        return None
    depth = 0
    for i, c in enumerate(m.group(1)):
        depth += (c in "([{⟨") - (c in ")]}⟩")
        if c == ":" and depth == 0:
            return m.group(1)[i + 1 :].strip()
    return None


def check(name, lean, work):
    """None if Alive2 and the theorem agree with the case's verdict, and otherwise why not."""
    with open(os.path.join(CASES, name + ".ll")) as f:
        text = f.read()
    expected = text.split("\n", 1)[0].removeprefix(";").strip()
    if expected not in ("correct", "incorrect"):
        return f"its first line says {expected!r}, not correct or incorrect"
    claim = statement(lean, name)
    if claim is None:
        return "no theorem of its name"
    if claim.startswith("¬") != (expected == "incorrect") or not re.match(r"¬?\s*(Refines|Run\.le)\b", claim):
        return f"the theorem doesn't state that it's {expected}: {' '.join(claim.split())}"
    source, target = functions(text)
    if source is None or target is None:
        return "no @src or no @tgt"
    paths = [os.path.join(work, f"{name}.{side}.ll") for side in ("src", "tgt")]
    for path, function in zip(paths, (source, target), strict=True):
        with open(path, "w") as f:
            f.write(function)
    try:
        r = subprocess.run(
            ["alive-tv", "--smt-to=20000", *paths],
            text=True,
            capture_output=True,
            timeout=TIMEOUT_SECONDS,
            check=False,
        )
        output = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        output = f"alive-tv didn't finish in {TIMEOUT_SECONDS} s"
    got = alive.verdict(output)
    if got != expected:
        return f"Alive2 says {got}:\n{output[-1500:]}"
    return None


def main():
    with open(TESTS) as f:
        lean = f.read()
    names = sorted(n.removesuffix(".ll") for n in os.listdir(CASES) if n.endswith(".ll"))
    if not names:
        sys.exit(f"no cases in {CASES}")
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        for name in names:
            problem = check(name, lean, work)
            if problem is None:
                print(f"ok    Alive2 agrees: {name}")
            else:
                print(f"FAIL  {name}: {problem}")
                failed += 1
    print(f"{len(names) - failed} of {len(names)} rewrites: Alive2 and the theorem agree")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
