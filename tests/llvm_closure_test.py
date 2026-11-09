#!/usr/bin/env python3
"""BIND-02's closure for `simplifyAddInst`, checked against the pinned build: its files hash as recorded,
clang is the one it was derived with, and compiled again, every function in it has the same IR. Then a closure
with one file's hash changed, and one with one function's IR changed, each have to fail. See
docs/llvm-closure.md.

usage: tests/llvm_closure_test.py [--jobs N]
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc  # noqa: E402

CLOSURE = ROOT / "tests" / "llvm_scope" / "closure"
TOOL = CLOSURE / "closure.py"


def check(path: Path, jobs: int, reuse: bool) -> proc.Ran:
    argv = [str(TOOL), "check", "simplifyAddInst", "--path", str(path), "--jobs", str(jobs), "--rebuild"]
    return proc.run([*argv, "--reuse"] if reuse else argv, timeout=3600)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--jobs", type=int, default=4)
    args = ap.parse_args()
    good = CLOSURE / "simplifyAddInst.json"
    closure = json.loads(good.read_text())
    failures = []
    # The recorded closure, compiled afresh: then each broken one against that same build.
    r = check(good, args.jobs, reuse=False)
    print(r.stdout.decode(errors="replace"), end="")
    if r.exit != 0:
        failures.append("the recorded closure doesn't check against the pinned build")
    with tempfile.TemporaryDirectory() as tmp:
        for name, change in [
            ("a file's hash changed", lambda c: c["files"].update({next(iter(c["files"])): "0" * 64})),
            ("a function's IR changed", lambda c: c["functions"][0].update({"ir_sha256": "0" * 64})),
        ]:
            bad = json.loads(json.dumps(closure))
            change(bad)
            path = Path(tmp) / "closure.json"
            path.write_text(json.dumps(bad))
            r = check(path, args.jobs, reuse=True)
            caught = r.exit == 1 and r.limit is None and "FAIL" in r.stdout.decode(errors="replace")
            print(f"{'ok  ' if caught else 'FAIL'} {name}: the check fails")
            if not caught:
                failures.append(f"{name}: the check didn't fail")
    for f in failures:
        print(f"FAIL {f}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
