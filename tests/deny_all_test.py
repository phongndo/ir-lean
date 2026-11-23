#!/usr/bin/env python3
"""docs/verdicts.md's invariant 1, deny-all: each public entry point runs its smallest input that grants
twice, as a reader runs it. Once as it is, which has to grant, and once with IRLEAN_DENY_ALL=1, whose exit
code, output, every file it writes and every record nested in them hold no grant, in any form the design's
claim lists: a grant's word, a field such as `proved: true`, a count of grants, a verdict nested in another
record, an `ok` line, or an exit code that means one. The first run has to show a grant this sees.

Each entry point not on its grants yet is on PENDING, with the pull request that moves it, and PENDING can
only shrink. tools/verify_claims.py runs under its own switch, in tests/verify_claims_test.py.

usage: tests/deny_all_test.py path/to/ir-lean
"""

import argparse
import contextlib
import importlib.util
import json
import os
import re
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc, schemas, verdict  # noqa: E402


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Every word a grant is reported as, as the lint in tests/verdict_test.py knows them, and tests/verify.py's
# inputs.
WORDS: set[str] = load("verdict_under_test", ROOT / "tests" / "verdict_test.py").words()
VERIFY_TEST = load("verify_cases", ROOT / "tests" / "verify.py")
TIMING_TEST = load("timing_cases", ROOT / "tests" / "timing_test.py")
OK_LINE = re.compile(r"^\s*ok\b", re.M)

# Each entry point docs/verdicts.md's test 1 names.
ALL = {
    "tools/verify.py check",
    "tools/prooftest/prooftest.py run",
    "tools/prooftest/bench.py",
    "tools/rules/rules.py proved",
    "tools/rules/rules.py certify",
    "tools/rules/rules.py search",
    "tools/store/store.py add",
    "tools/store/store.py check",
    "tools/store/store.py lookup",
    "tools/binding.py",
    "bench/instcombine/stage1.py",
    "bench/kernels/pairs.py --check",
    "tests/peephole.py, the scorer",
    "tools/irlean/check.py",
    "the smallest shell test",
    "bench/kernels/timing.py read",
    "the results board",
}
# Those not on their grants yet, each with the pull request of docs/verdicts.md's migration that moves it, and
# adds it to ENTRY_POINTS. It can only shrink.
PENDING = {
    "tools/prooftest/prooftest.py run": "PR 6",
    "tools/prooftest/bench.py": "PR 6",
    "tools/rules/rules.py proved": "PR 8",
    "tools/rules/rules.py certify": "PR 8",
    "tools/rules/rules.py search": "PR 8",
    "tools/store/store.py add": "PR 7",
    "tools/store/store.py check": "PR 7",
    "tools/store/store.py lookup": "PR 7",
    "tools/binding.py": "PR 9",
    "bench/instcombine/stage1.py": "PR 9",
    "bench/kernels/pairs.py --check": "PR 6",
    "tests/peephole.py, the scorer": "PR 10",
    "tools/irlean/check.py": "PR 4",
    "the smallest shell test": "PR 4",
    "the results board": "once it's built on bench/kernels/timing.py",
}


def grants_in(value: Any, where: str = "") -> list[str]:
    """Where `value`, a record, holds a grant: a grant's word as any value in it; a key that's a grant's word,
    `granted`, or ends with one, such as `slices_certified`, whose value is true, a count above 0, or a record
    of one; and either inside any record nested in it. A string under such a key, such as a witness's
    `instance`, the statement at it, is what the key names, not a grant."""
    found = []
    if isinstance(value, str) and value in WORDS:
        found.append(f"{where or 'it'} is {value!r}")
    elif isinstance(value, dict):
        for key, inner in value.items():
            named = {str(key), str(key).rsplit("_", 1)[-1]} & (WORDS | {"granted"})
            said = (
                inner is True
                or (type(inner) is int and inner > 0)
                or (isinstance(inner, dict | list) and inner)
            )
            if named and said:
                found.append(f"{where}.{key} is {json.dumps(inner)[:100]}")
            found += grants_in(inner, f"{where}.{key}")
    elif isinstance(value, list):
        for i, inner in enumerate(value):
            found += grants_in(inner, f"{where}[{i}]")
    return found


def grants_in_text(text: str, where: str) -> list[str]:
    """Where `text`, which a run printed or wrote, holds a grant: as a record, if it's JSON, or each JSON line
    of it, or an `ok` line."""
    try:
        return grants_in(json.loads(text), where)
    except json.JSONDecodeError:
        pass
    found = [f"{where} has an ok line" for _ in OK_LINE.finditer(text)]
    for i, line in enumerate(text.splitlines()):
        if line.lstrip().startswith(("{", "[")):
            with contextlib.suppress(json.JSONDecodeError):
                found += grants_in(json.loads(line), f"{where}:{i + 1}")
    return found


def written(directory: Path) -> list[str]:
    """The grants in each file under `directory` that's text."""
    found = []
    for path in sorted(p for p in directory.rglob("*") if p.is_file() and not p.is_symlink()):
        try:
            text = path.read_text()
        except UnicodeDecodeError:
            continue
        found += grants_in_text(text, str(path.relative_to(directory)))
    return found


def run_twice(
    name: str, argv: Callable[[Path], list[str]], scratch: Path, exits: set[int], wanted: str
) -> list[str]:
    """Runs an entry point as a reader does, once as it is and once with IRLEAN_DENY_ALL=1, and returns what's
    wrong: the first has to say `wanted` and exit with one of `exits`, the grants' exit codes, and the
    second has to hold no grant anywhere."""
    problems = []
    plain = {k: v for k, v in os.environ.items() if k != verdict.DENY_ALL}
    for denied, env in ((False, plain), (True, {**plain, verdict.DENY_ALL: "1"})):
        work = scratch / f"{name}-{'denied' if denied else 'plain'}"
        ran = proc.run(argv(work), timeout=600, cwd=ROOT, env=env)
        found = grants_in_text(ran.out, "stdout") + grants_in_text(ran.err, "stderr") + written(work)
        if ran.exit in exits:
            found.append(f"exit {ran.exit}")
        if not denied:
            record = json.loads(ran.out) if ran.out.strip().startswith("{") else {}
            # As it is, it says the grant's word and ends with one of the grants' exit codes.
            if record.get("status") != wanted or not found or ran.exit not in exits:
                problems.append(f"didn't grant {wanted} as it is: exit {ran.exit}, {ran.out[:500]}")
        elif found:
            problems.append(f"with {verdict.DENY_ALL}=1, grants: {'; '.join(found[:10])}")
    return problems


def verify(tool: Path, scratch: Path) -> list[tuple[str, list[str]]]:
    """tools/verify.py's smallest inputs that grant proved and counterexample."""
    exits = {g.exit for g in verdict.GRANTS.values() if g.schema == schemas.VERIFY}
    out = []
    for name, wanted, request, files in (
        ("verify_proved", "proved", VERIFY_TEST.proof("ok", "inc_ok"), VERIFY_TEST.files_for("ok")),
        (
            "verify_counterexample",
            "counterexample",
            VERIFY_TEST.small(statement=VERIFY_TEST.INC_OR, witnesses=[{"x": "1#32"}]),
            {"Small.ll": VERIFY_TEST.SMALL_LL},
        ),
    ):
        inputs = scratch / name
        inputs.mkdir()
        for file, text in files.items():
            (inputs / file).write_text(text)
        (inputs / "request.json").write_text(json.dumps(request, ensure_ascii=False))

        def argv(work: Path, inputs: Path = inputs) -> list[str]:
            check = [str(ROOT / "tools" / "verify.py"), "check", str(inputs / "request.json")]
            return [*check, "--tool", str(tool), "--work-dir", str(work)]

        out.append((name, run_twice(name, argv, scratch, exits, wanted)))
    return out


def timing(tool: Path, scratch: Path) -> list[tuple[str, list[str]]]:
    """bench/kernels/timing.py's smallest inputs that are read as faster and as slower: two confirmation
    sessions by the protocol of each of a project's two workloads, as records tests/timing_test.py makes.
    Nothing is timed. `read` writes nothing, so its directories of sessions have to be as they were after
    each run: a grant written beside them would be one no other check here sees."""
    del tool
    exits = {g.exit for g in verdict.GRANTS.values() if g.schema == schemas.KERNELS_READING}
    out = []
    for name, wanted, ratio in (("timing_faster", "faster", 1.01), ("timing_slower", "slower", 0.98)):
        sessions = scratch / f"{name}-sessions"
        for _ in range(2):
            mine = TIMING_TEST.protocol_session(sessions / "argon2id", ratio)
            theirs = TIMING_TEST.protocol_session(sessions / "secretstream", 1.0, "secretstream")

        def held(sessions: Path = sessions) -> dict[str, bytes]:
            files = sorted(p for p in sessions.rglob("*") if p.is_file())
            return {str(p.relative_to(sessions)): p.read_bytes() for p in files}

        def argv(work: Path, mine: Path = mine, theirs: Path = theirs) -> list[str]:
            del work
            return [str(ROOT / "bench" / "kernels" / "timing.py"), "read", str(mine), "--other", str(theirs)]

        before = held()
        problems = run_twice(name, argv, scratch, exits, wanted)
        if held() != before:
            problems.append("it changed its directories of sessions, which it only reads")
        out.append((name, problems))
    return out


# Each entry point on its grants, and how to run it.
ENTRY_POINTS = {"tools/verify.py check": verify, "bench/kernels/timing.py read": timing}


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    args = parser.parse_args()
    failed = False
    if set(ENTRY_POINTS) | set(PENDING) != ALL or set(ENTRY_POINTS) & set(PENDING):
        print(f"FAIL  entry points: run {sorted(ENTRY_POINTS)} and pending {sorted(PENDING)} aren't test 1's")
        failed = True
    with tempfile.TemporaryDirectory() as temporary:
        for entry, run in ENTRY_POINTS.items():
            for name, problems in run(args.tool.resolve(), Path(temporary)):
                for problem in problems:
                    print(f"FAIL  {entry}, {name}: {problem}")
                failed |= bool(problems)
                if not problems:
                    print(f"ok    {entry}, {name}: no grant with {verdict.DENY_ALL}=1")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
