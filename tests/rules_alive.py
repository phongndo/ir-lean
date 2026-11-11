#!/usr/bin/env python3
"""Asks Alive2 about each rewrite the rule search certified, as a second opinion and never as acceptance.

For each kept result under the directories given, which `tools/rules/rules.py search` or `survey` wrote, it
gives `alive-tv` the slice before and after, with `undef` inputs off, as tests/alive.py runs it. A certificate
is Lean's. What this adds is a disagreement: a rewrite Lean certified that Alive2 finds incorrect is a gap in
the model, the emitter or the gate, and fails. No verdict from Alive2, a timeout or a failure to prove, is
counted and isn't a failure. docs/rule-search.md has what it found.

usage: tests/rules_alive.py DIR...
"""

from __future__ import annotations

import concurrent.futures
import json
import sys
import tempfile
from pathlib import Path

import alive

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))

from irlean import schemas  # noqa: E402


def pairs(directories: list[Path]) -> list[tuple[str, Path]]:
    """Each certified result's name and directory."""
    out = []
    for directory in directories:
        for results in sorted(directory.rglob("results.json")):
            record = schemas.read(results, schemas.RULE_SEARCH)
            for f in record["functions"]:
                for r in f["results"]:
                    if r["kept"] and r["slice"]["status"] == "certified":
                        where = results.parent / r["directory"]
                        out.append((f"{record['input']['name']} @{f['function']} {r['root']}", where))
    return out


def ask(where: Path, work: str) -> str:
    """What Alive2 says of one result's slice: `correct`, `incorrect` or `unknown`."""
    before, after = (where / "slice-before.ll").read_text(), (where / "slice-after.ll").read_text()
    return alive.verdict(alive.run(before, after, work))


def check(directories: list[Path]) -> dict[str, list[str]]:
    found = pairs(directories)
    said: dict[str, list[str]] = {"correct": [], "incorrect": [], "unknown": []}
    with tempfile.TemporaryDirectory() as work, concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for (name, _), verdict in zip(found, pool.map(lambda p: ask(p[1], work), found), strict=True):
            said[verdict].append(name)
    return said


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    said = check([Path(a) for a in sys.argv[1:]])
    total = sum(len(v) for v in said.values())
    print(json.dumps({"certified": total, **{k: len(v) for k, v in said.items()}}))
    for name in said["unknown"]:
        print(f"no verdict from Alive2: {name}")
    for name in said["incorrect"]:
        print(f"FAIL  Lean certified it and Alive2 finds it incorrect: {name}")
    return 1 if said["incorrect"] else 0


if __name__ == "__main__":
    sys.exit(main())
