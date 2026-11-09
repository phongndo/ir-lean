#!/usr/bin/env python3
"""BIND-02's closure for `simplifyAddInst`, checked against the pinned build: its files hash as recorded,
clang is the one it was derived with, and compiled again, every function in it, and every other copy of an
inline one, has the same IR. Then a closure with one file's hash changed, one function's IR changed, or one
other copy's IR changed each has to fail, and a function's IR hash has to cover its attribute groups and
metadata, not their numbering. See docs/llvm-closure.md.

usage: tests/llvm_closure_test.py [--jobs N]
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc  # noqa: E402

CLOSURE = ROOT / "tests" / "llvm_scope" / "closure"
TOOL = CLOSURE / "closure.py"

# closure.py is a script in a directory of data, so it's loaded by its path.
_spec = importlib.util.spec_from_file_location("closure", TOOL)
assert _spec is not None and _spec.loader is not None
closure = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(closure)

# A function with an attribute group and a `!range`, and the same function with each changed, or renumbered.
IR = """define i32 @f(ptr %p) #{a} {{
  %v = load i32, ptr %p, align 4, !range !{m}
  ret i32 %v
}}

attributes #{a} = {{ {attrs} }}

!{m} = !{{i32 0, i32 {hi}}}
"""


def ir_hash(tmp: Path, a: int = 0, attrs: str = "nounwind", m: int = 0, hi: int = 10) -> str:
    ll = tmp / "f.ll"
    ll.write_text(IR.format(a=a, attrs=attrs, m=m, hi=hi))
    return closure.parse(ll)["defs"]["f"]["ir_sha256"]


def hashing_cases(tmp: Path) -> list[str]:
    """A function's IR hash covers the attribute groups and metadata it refers to, and not their numbers."""
    base = ir_hash(tmp)
    failures = []
    for name, got, same in [
        ("an attribute group changed", ir_hash(tmp, attrs="noreturn"), False),
        ("a !range payload changed", ir_hash(tmp, hi=11), False),
        ("the attribute group and metadata renumbered", ir_hash(tmp, a=3, m=7), True),
    ]:
        ok = (got == base) == same
        print(f"{'ok  ' if ok else 'FAIL'} {name}: the IR hash {'stays' if same else 'changes'}")
        if not ok:
            failures.append(f"{name}: the IR hash {'changed' if same else 'stayed the same'}")
    return failures


def check(path: Path, jobs: int, reuse: bool) -> proc.Ran:
    argv = [str(TOOL), "check", "simplifyAddInst", "--path", str(path), "--jobs", str(jobs), "--rebuild"]
    return proc.run([*argv, "--reuse"] if reuse else argv, timeout=3600)


def change_copy(c: dict) -> None:
    f = next(f for f in c["functions"] if f["copies"])
    f["copies"][next(iter(f["copies"]))] = "0" * 64


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
        failures += hashing_cases(Path(tmp))
        for name, change in [
            ("a file's hash changed", lambda c: c["files"].update({next(iter(c["files"])): "0" * 64})),
            ("a function's IR changed", lambda c: c["functions"][0].update({"ir_sha256": "0" * 64})),
            ("another copy of an inline function changed", change_copy),
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
