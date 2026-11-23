#!/usr/bin/env python3
"""What a variant is: a build of libsodium for the kernel corpus that may be measured. docs/kernels.md.

`realize NAME` builds one of bench/kernels/variants.nix's derivations, the baseline or a candidate, and
answers with its store path only where irlean.verdict grants `kernels.variant`: the repository was archived
at a commit, the derivation evaluated and was realized, each object its table names was made from its IR
once, every object of a unit it touches is in the table, each known-answers check wrote its result afresh and
each workload's run ended, and the results and outputs are the expected ones. A build that's whole in all
that, where a result or an output is another one, is `kernels.rejected`. Anything else is `unknown` or
`error`.

It reads nothing from the checkout once it's archived: it refuses a checkout whose tracked files differ from
HEAD, archives HEAD's commit to the Nix store, and runs itself again from that copy.

usage: bench/kernels/variants.py realize NAME [--pretty]
NAME is `baseline`, or one of the builds under `tests`, such as `tests.roundtrip`.
exit codes: 0 a variant, 2 a wrong answer, 3 unknown, 1 an error
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(HERE))
import kernels  # noqa: E402
from irlean import hashing, proc, schemas, verdict  # noqa: E402
from irlean.verdict import Evidence, Step  # noqa: E402

PROJECT = "libsodium"
NAME = re.compile(r"[a-z][a-z0-9-]*(?:\.[a-z][a-z0-9-]*)*")
COMMIT = re.compile(r"[0-9a-f]{40}")
SHA256 = re.compile(r"[0-9a-f]{64}")
# The seconds a question of git or Nix, archiving the repository, and realizing a derivation may take.
QUERY_SECONDS, ARCHIVE_SECONDS, BUILD_SECONDS = 300, 1800, 7200
# What the processor has to have for a check to run the units the tests replace: tests/variants_builds.py.
FEATURES = ("avx2", "avx512f")
EXIT_CODES = {"variant": 0, "wrong_answer": 2, "unknown": 3, "error": 1}
# Each reason this gives, with its status and what it means. The two grants' are irlean.verdict's to give.
REASONS: dict[str, tuple[str, str]] = {
    "built_and_checked": ("variant", "Every requirement of `kernels.variant` was observed"),
    "answer_differs": (
        "wrong_answer",
        "The build is whole, and a check's result or a run's output is another",
    ),
    "time_limit": ("unknown", "A command ran out of time"),
    "resource_limit": ("unknown", "A command ran past a limit on memory"),
    "killed": ("unknown", "A command was killed"),
    "invalid_request": ("error", "NAME isn't a build's name"),
    "checkout_dirty": ("error", "Tracked files differ from HEAD: commit them first"),
    "snapshot_failed": ("error", "The repository couldn't be archived at its commit"),
    "not_the_snapshot": ("error", "This isn't running from the archive of the commit it was given"),
    "manifest_invalid": ("error", "The snapshot's manifest doesn't pass kernels.validate"),
    "evaluation_failed": ("error", "The derivation didn't evaluate"),
    "build_failed": ("error", "The build didn't end whole: configure, make or a workload's build failed"),
    "evidence_malformed": ("error", "What the build wrote down isn't its schema's"),
    "tool_failed": ("error", "A tool crashed or answered in a way this doesn't understand"),
    "snapshot": ("error", "Archiving didn't end cleanly"),
    "evaluate": ("error", "Evaluating didn't end cleanly"),
    "realize": ("error", "Realizing didn't end cleanly"),
    "replaced_once": ("error", "The objects made from IR aren't the table's, each once"),
    "units_whole": ("error", "The table has some of a unit's objects and not all"),
    "checks_completed": ("error", "A known-answers check didn't write its result afresh, or didn't end"),
    "runs_completed": ("error", "A workload's run is missing, or didn't end"),
    "answers_match": ("error", "A check's result isn't the expected one, or one of its commands failed"),
    "outputs_match": ("error", "A run failed, or its output isn't the manifest's"),
    "contradiction": ("error", "The same evidence gives both grants"),
    "internal_error": ("error", "A bug in this tool"),
    "denied": ("error", "IRLEAN_DENY_ALL is set, which takes every grant away"),
}
TABLE = {reason: (status, EXIT_CODES[status]) for reason, (status, _) in REASONS.items()}
# What the build writes down, bench/kernels/builder.py's, and what variants.nix plans: exactly these keys and
# types. A list is of its one element, a tuple is any of its members, and `{str: T}` is any keys.
ENDED = {"argv": [str], "exit": int, "limit": (str, None)}
EVIDENCE = {
    "schema": str,
    "replaced": {str: str},
    "compiled": {str: str},
    "checks": [
        {
            "workload": str,
            "commands": [ENDED],
            "expected": str,
            "expected_sha256": (str, None),
            "result": str,
            "result_before": bool,
            "result_sha256": (str, None),
        }
    ],
    "runs": [{"workload": str, "env": {str: str}, **ENDED, "stdout_sha256": str}],
}
PLANNED = {"table": [str], "workloads": [{"name": str, "known_answers": int, "outputs": [str]}]}


class Refused(Exception):
    """A refusal of this tool's own, with a reason of REASONS."""

    def __init__(self, reason: str, detail: str) -> None:
        super().__init__(detail)
        self.reason, self.detail = reason, detail


def fits(value: Any, shape: Any, where: str = "it") -> None:
    """Raises Refused unless `value` is exactly `shape`: a type, with a bool never an int; None; a tuple of
    alternatives; a list of one shape; a dict of any keys to one shape; or a dict of exactly its keys."""
    if isinstance(shape, tuple):
        for alternative in shape:
            try:
                return fits(value, alternative, where)
            except Refused:
                pass
        ok = False
    elif shape is None:
        ok = value is None
    elif isinstance(shape, type):
        ok = type(value) is shape
    elif isinstance(shape, list):
        ok = type(value) is list
        for i, inner in enumerate(value if ok else []):
            fits(inner, shape[0], f"{where}[{i}]")
    elif list(shape) == [str]:
        ok = type(value) is dict and all(type(k) is str for k in value)
        for key, inner in (value if ok else {}).items():
            fits(inner, shape[str], f"{where}.{key}")
    else:
        ok = type(value) is dict and set(value) == set(shape)
        for key, inner in shape.items() if ok else []:
            fits(value[key], inner, f"{where}.{key}")
    if not ok:
        raise Refused(
            "evidence_malformed", f"{where} is {json.dumps(value, default=str)[:120]}, not its schema's"
        )


def ask(argv: list[str], seconds: int) -> proc.Ran:
    """A question this tool can't go on without an answer to. Raises Refused unless it ended cleanly."""
    ran = proc.run(argv, timeout=seconds)
    if ran.limit is not None:
        raise Refused(
            ran.limit if ran.limit in REASONS else "time_limit", f"{argv[0]} {argv[1]}: {ran.limit}"
        )
    if not ran.ok:
        raise Refused("tool_failed", f"{' '.join(argv[:4])} exited {ran.exit}: {ran.err[-400:]}")
    return ran


def parsed(text: str, what: str) -> Any:
    try:
        return json.loads(text)
    except ValueError as error:
        raise Refused("tool_failed", f"{what} isn't JSON: {error}") from error


def commit_of(repo: Path) -> str:
    """HEAD's commit, of a checkout whose tracked files are HEAD's."""
    dirty = ask(["git", "-C", str(repo), "status", "--porcelain", "--untracked-files=no"], QUERY_SECONDS)
    if dirty.stdout.strip():
        raise Refused("checkout_dirty", f"{repo}'s tracked files differ from HEAD")
    commit = ask(
        ["git", "-C", str(repo), "rev-parse", "--verify", "HEAD^{commit}"], QUERY_SECONDS
    ).out.strip()
    if not COMMIT.fullmatch(commit):
        raise Refused("tool_failed", f"git gave {commit[:80]!r} for HEAD's commit")
    return commit


def archive(repo: Path, commit: str) -> tuple[proc.Ran, Path | None]:
    """Archives `repo` at `commit` to the Nix store, forbidding any change to its lock, and says where. A
    checkout with one commit's history, as CI's is, archives to the same path as one with all of it."""
    reference = f"git+file://{repo}?rev={commit}&shallow=1"
    ran = proc.run(
        ["nix", "flake", "archive", "--json", "--no-update-lock-file", reference], timeout=ARCHIVE_SECONDS
    )
    path = parsed(ran.out, "nix flake archive's answer").get("path") if ran.ok else None
    return ran, Path(path) if isinstance(path, str) and path.startswith("/nix/store/") else None


def nar_hash(path: Path) -> str:
    """The hash Nix registered for a store path."""
    info = parsed(ask(["nix", "path-info", "--json", str(path)], QUERY_SECONDS).out, "nix path-info's answer")
    found = info.get(str(path)) if isinstance(info, dict) else next(iter(info), None)
    if not isinstance(found, dict) or not isinstance(found.get("narHash"), str):
        raise Refused("tool_failed", f"nix path-info gave no narHash for {path}")
    return found["narHash"]


def exited(ran: dict[str, Any]) -> bool:
    """Whether a command the build wrote down ran to an exit of its own."""
    return ran["limit"] is None and ran["exit"] >= 0


def judge(planned: dict[str, Any], e: dict[str, Any]) -> dict[str, bool]:
    """Each check `kernels.variant` and `kernels.rejected` need, of what variants.nix planned against what the
    build wrote down. Raises Refused where a check's command or a run was stopped, which decides nothing."""
    for stopped in [k for c in e["checks"] for k in c["commands"]] + e["runs"]:
        if not exited(stopped):
            limit = stopped["limit"]
            raise Refused(
                limit if limit in REASONS else "killed", f"{' '.join(stopped['argv'][:3])} was stopped"
            )
    hashes = [h for c in e["checks"] for h in (c["expected_sha256"], c["result_sha256"])]
    for found in [*hashes, *e["replaced"].values(), *(r["stdout_sha256"] for r in e["runs"])]:
        if found is not None and not SHA256.fullmatch(found):
            raise Refused("evidence_malformed", f"{found[:80]!r} isn't a SHA-256")
    table = sorted(planned["table"])
    by_name = {w["name"]: w for w in planned["workloads"]}
    touched = {e["compiled"].get(key) for key in table}
    known = sorted(w["name"] for w in planned["workloads"] for _ in range(w["known_answers"]))
    completed = sorted(c["workload"] for c in e["checks"]) == known and all(
        c["result_before"] is False
        and c["result_sha256"] is not None
        and c["expected_sha256"] is not None
        and bool(c["commands"])
        for c in e["checks"]
    )
    each_ran = len(by_name) == len(planned["workloads"]) and sorted(
        r["workload"] for r in e["runs"]
    ) == sorted(by_name)
    answers = [c["result_sha256"] == c["expected_sha256"] for c in e["checks"]]
    outputs = [
        r["stdout_sha256"] == want
        for r in e["runs"]
        for want in by_name.get(r["workload"], {}).get("outputs", [])
    ]
    return {
        "replaced_once": sorted(e["replaced"]) == table,
        # Every object the build compiled from a unit the table touches is in the table.
        "units_whole": None not in touched
        and all(key in table for key, unit in e["compiled"].items() if unit in touched),
        "checks_completed": completed,
        "runs_completed": each_ran,
        "answers_match": all(answers) and all(k["exit"] == 0 for c in e["checks"] for k in c["commands"]),
        "outputs_match": all(outputs) and all(r["exit"] == 0 for r in e["runs"]),
        "an_answer_differs": completed and each_ran and not all([*answers, *outputs]),
    }


def said(d: verdict.Decision | None, reason: str | None, detail: str, **more: Any) -> dict[str, Any]:
    """This tool's answer: the status, reason and exit code irlean.verdict.status gives."""
    status, reason, code = verdict.status(d, TABLE, reason)
    return {
        "schema": schemas.KERNELS_VARIANT,
        "status": status,
        "reason": reason,
        "detail": detail,
        "exit_code": code,
        **more,
    }


def answer_of(
    planned: Any, evidence: Any, steps: dict[str, Step], **more: Any
) -> tuple[dict[str, Any], bool]:
    """The answer about a build: what variants.nix planned, what the build wrote down, and how archiving,
    evaluating and realizing each ended. And whether it's `kernels.variant` that was granted."""
    fits(planned, PLANNED, "the plan")
    fits(evidence, EVIDENCE, "the evidence")
    checks = judge(planned, evidence)
    e = Evidence(steps=steps, checks=checks)
    more = {**more, "table": sorted(planned["table"]), "checks": checks}
    whole = verdict.decide("kernels.variant", e)
    if whole.granted:
        return said(whole, "built_and_checked", whole.detail, **more), True
    wrong = verdict.decide("kernels.rejected", e)
    if wrong.granted:
        return said(wrong, "answer_differs", wrong.detail, **more), False
    refusal = wrong if wrong.reason == "denied" else whole
    return said(refusal, None, refusal.detail, **more), False


def realize(name: str, repo: Path, commit: str) -> dict[str, Any]:
    """The answer about one build, from the archive of `repo` at `commit`, which this has to run from."""
    if not NAME.fullmatch(name):
        raise Refused("invalid_request", f"{name!r} isn't a build's name")
    snapshot, path = archive(repo, commit)
    if not snapshot.ok or path is None:
        raise Refused("snapshot_failed", f"nix flake archive ended with {snapshot.exit}, {snapshot.limit}")
    if path != ROOT:
        raise Refused(
            "not_the_snapshot", f"{commit} of {repo} is archived at {path}, and this runs from {ROOT}"
        )
    if problems := kernels.validate(kernels.load(HERE / "manifest.toml")):
        raise Refused("manifest_invalid", "; ".join(problems)[:500])
    attribute = f"path:{ROOT}#kernels.{PROJECT}.{name}"
    flags = ["--json", "--no-update-lock-file"]
    evaluate = proc.run(["nix", "eval", *flags, f"{attribute}.planned"], timeout=QUERY_SECONDS)
    if not evaluate.ok:
        raise Refused("evaluation_failed" if evaluate.limit is None else "time_limit", evaluate.err[-600:])
    build = proc.run(["nix", "build", *flags, "--no-link", attribute], timeout=BUILD_SECONDS)
    if not build.ok:
        raise Refused("build_failed" if build.limit is None else "time_limit", build.err[-600:])
    built = parsed(build.out, "nix build's answer")
    out = built[0].get("outputs", {}).get("out") if isinstance(built, list) and len(built) == 1 else None
    if not isinstance(out, str) or not out.startswith("/nix/store/"):
        raise Refused("tool_failed", f"nix build named no output: {build.out[:200]}")
    try:
        evidence = schemas.read(Path(out) / "evidence" / "evidence.json", schemas.KERNELS_EVIDENCE)
    except (OSError, schemas.SchemaError) as error:
        raise Refused("evidence_malformed", str(error)) from error
    ended = (("snapshot", snapshot), ("evaluate", evaluate), ("realize", build))
    answer, granted = answer_of(
        parsed(evaluate.out, "the derivation's plan"),
        evidence,
        {step: Step(step, ran.exit, ran.limit) for step, ran in ended},
        name=name,
        commit=commit,
        snapshot={"path": str(ROOT), "nar_hash": nar_hash(ROOT)},
    )
    # Only a variant has a path here: nothing else is to be measured.
    return {**answer, "path": out, "nar_hash": nar_hash(Path(out))} if granted else answer


def objects(root: Path) -> dict[str, str]:
    """The SHA-256 of each object file under `root`, by its path there."""
    return {
        str(p.relative_to(root)): hashing.sha256_file(p)
        for p in sorted(root.rglob("*.o"))
        if p.is_file() and not p.is_symlink()
    }


def section(obj: Path, name: str) -> bytes:
    """A section's bytes, through a file. One that's missing or empty is an error, never equal to one."""
    with tempfile.TemporaryDirectory() as scratch:
        out = Path(scratch) / "section"
        ran = proc.run(
            ["llvm-objcopy", f"--dump-section={name}={out}", str(obj), os.devnull], timeout=QUERY_SECONDS
        )
        if not ran.ok or not out.is_file() or out.stat().st_size == 0:
            raise RuntimeError(
                f"{obj} has no bytes for {name}: llvm-objcopy exited {ran.exit}, {ran.err[-200:]}"
            )
        return out.read_bytes()


def missing_features() -> list[str]:
    """Which of FEATURES this processor lacks."""
    flags = set(Path("/proc/cpuinfo").read_text().split())
    return sorted(f for f in FEATURES if f not in flags)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("command", choices=["realize"])
    parser.add_argument("name")
    parser.add_argument("--pretty", action="store_true")
    # This tool's own, for when it runs itself again from the archive.
    parser.add_argument("--repo", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--commit", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        if args.repo is None or args.commit is None:
            commit = commit_of(ROOT)
            snapshot, path = archive(ROOT, commit)
            if snapshot.limit is not None or not snapshot.ok or path is None:
                raise Refused(
                    "snapshot_failed", f"nix flake archive ended with {snapshot.exit}, {snapshot.limit}"
                )
            again = [
                str(path / "bench" / "kernels" / "variants.py"),
                *sys.argv[1:],
                "--repo",
                str(ROOT),
                "--commit",
                commit,
            ]
            os.execv(sys.executable, [sys.executable, *again])
        answer = realize(args.name, args.repo, args.commit)
    except Refused as refused:
        answer = said(None, refused.reason, refused.detail, name=args.name)
    print(json.dumps(answer, indent=2 if args.pretty else None, sort_keys=True))
    return answer["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
