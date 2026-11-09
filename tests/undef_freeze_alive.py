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
a failure, not agreement. Run by tests/undef_freeze.sh.

With `--model FILE`, it checks the model's `freeze` instead: each rewrite in tests/freeze, and each here
with a `freeze` and no `undef`, which the model keeps out, against the theorem of its name in FILE, with
Alive2's `undef` inputs off, since an argument of the model is a value or poison. Run by tests/freeze.sh."""

import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alive

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
from irlean import proc  # noqa: E402

CASES = os.path.join(ROOT, "tests", "undef_freeze", "alive2")
FREEZE_CASES = os.path.join(ROOT, "tests", "freeze")
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


def model_cases():
    """The rewrites the model's `freeze` is checked on: tests/freeze's, and those in CASES with a `freeze`
    and no `undef`. `noundef` isn't `undef`."""
    paths = []
    for directory in (CASES, FREEZE_CASES):
        for n in sorted(os.listdir(directory)):
            if not n.endswith(".ll"):
                continue
            path = os.path.join(directory, n)
            with open(path) as f:
                text = f.read()
            if directory == FREEZE_CASES or ("freeze" in text and not re.search(r"\bundef\b", text)):
                paths.append(path)
    return paths


def check(path, lean, work, alive_options=()):
    """None if Alive2 and the theorem agree with the case's verdict, and otherwise why not."""
    name = os.path.basename(path).removesuffix(".ll")
    with open(path) as f:
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
    r = proc.run(["alive-tv", "--smt-to=20000", *alive_options, *paths], timeout=TIMEOUT_SECONDS)
    output = f"alive-tv didn't finish in {TIMEOUT_SECONDS} s" if r.limit == "time_limit" else r.out + r.err
    got = alive.verdict(output)
    if got != expected:
        return f"Alive2 says {got}:\n{output[-1500:]}"
    return None


def main():
    model = sys.argv[2] if sys.argv[1:2] == ["--model"] and len(sys.argv) == 3 else None
    if len(sys.argv) > 1 and model is None:
        sys.exit("usage: tests/undef_freeze_alive.py [--model THEOREMS.lean]")
    with open(model or TESTS) as f:
        lean = f.read()
    if model:
        paths, options = model_cases(), ["--disable-undef-input"]
    else:
        paths, options = [os.path.join(CASES, n) for n in sorted(os.listdir(CASES)) if n.endswith(".ll")], []
    names = [os.path.basename(p).removesuffix(".ll") for p in paths]
    if not names:
        sys.exit(f"no cases in {CASES}")
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        for path, name in zip(paths, names, strict=True):
            problem = check(path, lean, work, options)
            if problem is None:
                print(f"ok    Alive2 agrees: {name}")
            else:
                print(f"FAIL  {name}: {problem}")
                failed += 1
    print(f"{len(names) - failed} of {len(names)} rewrites: Alive2 and the theorem agree")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
