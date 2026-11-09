#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Alive2's verdict on each rewrite in tests/float, against the one its name says: `_right` has to be proved
and `_wrong` refuted. Anything else, such as a timeout or an approximation, is a failure, not agreement.
Alive2 runs with `undef` inputs off, since an argument of the model is a value or poison, one process at a
time, on two files, so that it prints the summary tests/alive.py reads. Run by tests/float.sh.

usage: tests/float_alive.py CASE.ll ..."""

import os
import re
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alive


def main() -> int:
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        for path in sys.argv[1:]:
            name = os.path.basename(path)[: -len(".ll")]
            with open(path) as f:
                text = f.read()
            decls = "".join(line + "\n" for line in text.splitlines() if line.startswith("declare "))
            found = {
                m.group(1): m.group(0).replace(f"@{m.group(1)}(", "@f(", 1)
                for m in re.finditer(r"^define [^@]*@(src|tgt)\(.*?^\}\n", text, flags=re.M | re.S)
            }
            if set(found) != {"src", "tgt"}:
                print(f"FAIL  {path} doesn't define @src and @tgt")
                failed = 1
                continue
            got = alive.verdict(alive.run(decls + found["src"], decls + found["tgt"], work))
            want = "incorrect" if name.endswith("_wrong") else "correct"
            if got == want:
                print(f"ok    alive2: {name} is {got}")
            else:
                print(f"FAIL  alive2 says {name} is {got}, and its theorem says {want}")
                failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main())
