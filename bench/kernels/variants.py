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
HEAD, archives HEAD's commit to the Nix store, and runs itself again from that copy, isolated, so no module of
the checkout's can stand in for the copy's.

What the build wrote down has to follow what variants.nix planned, word for word: each step of the build, each
check's commands and files, and each run's environment and program, whose real path has to be in the build.

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
sys.path[:0] = [str(ROOT / "tools"), str(HERE)]
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
    "missing_features": ("unknown", "The builder could not dispatch to both corpus implementations"),
    "dispatch_failed": ("error", "The builder could not query the compiled library"),
    "launch_failed": ("error", "A planned executable could not be started"),
    "killed": ("unknown", "A command was killed"),
    "invalid_request": ("error", "The command line isn't this tool's, or NAME isn't a build's name"),
    "not_the_plan": ("error", "What the build wrote down doesn't follow what variants.nix planned"),
    "checkout_dirty": ("error", "Tracked files differ from HEAD: commit them first"),
    "snapshot_failed": ("error", "The repository couldn't be archived at its commit"),
    "not_the_snapshot": ("error", "This isn't running from the archive of the commit it was given"),
    "manifest_invalid": ("error", "The snapshot's manifest doesn't pass kernels.validate"),
    "evaluation_failed": ("error", "The derivation didn't evaluate"),
    "build_failed": (
        "error",
        "The build didn't end whole: Nix failed, or configure, make or a workload's build",
    ),
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
    "out": str,
    "attempt": str,
    "dispatch": {str: bool},
    "build": [ENDED],
    "replaced": {str: str},
    "compiled": {str: str},
    "checks": [
        {
            "workload": str,
            "commands": [ENDED],
            "comparison": (str, None),
            "expected": str,
            "expected_sha256": (str, None),
            "expected_size": (int, None),
            "result": str,
            "result_before": bool,
            "result_sha256": (str, None),
            "result_size": (int, None),
        }
    ],
    "runs": [
        {
            "workload": str,
            "env": {str: str},
            "program": str,
            **ENDED,
            "stdout_sha256": str,
            "stdout_size": int,
        }
    ],
}
LAUNCH = {"env": {str: str}, "argv": [str]}
PLANNED = {
    "out": str,
    "table": [str],
    "replace": {str: str},
    "attempt": str,
    "build": [[str]],
    "workloads": [
        {
            "name": str,
            "run": LAUNCH,
            "checks": [{"run": [[str]], "expected": str, "result": str}],
            "outputs": [str],
        }
    ],
}


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


def stopped_or(ran: proc.Ran, reason: str, detail: str) -> Refused:
    """How a process that didn't end cleanly is answered: by the limit that stopped it, as killed if a
    signal did, and otherwise as `reason`."""
    if ran.limit is not None:
        return Refused(ran.limit if ran.limit in REASONS else "time_limit", f"{ran.argv[0]}: {ran.limit}")
    if isinstance(ran.exit, int) and ran.exit < 0:
        return Refused("killed", f"{ran.argv[0]} died of signal {-ran.exit}")
    return Refused(reason, detail)


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


def unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """A JSON object's keys, each once: a key given twice is refused, not taken as its last value."""
    keys = [key for key, _ in pairs]
    if len(set(keys)) != len(keys):
        raise ValueError(f"a key is given twice, among {sorted(keys)[:8]}")
    return dict(pairs)


def parsed(text: str, what: str, reason: str = "tool_failed") -> Any:
    try:
        return json.loads(text, object_pairs_hook=unique)
    except ValueError as error:
        raise Refused(reason, f"{what} isn't JSON this reads: {error}") from error


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


def filled(planned: Any, out: str, path: str) -> Any:
    """`planned` with the output's placeholder, `out`, made the path realized."""
    if isinstance(planned, str):
        return planned.replace(out, path)
    if isinstance(planned, list):
        return [filled(p, out, path) for p in planned]
    return {k: filled(v, out, path) for k, v in planned.items()} if isinstance(planned, dict) else planned


def require_exit(ran: dict[str, Any]) -> None:
    step = Step(str(ran["argv"][:3]), ran["exit"], ran["limit"])
    reason = verdict.limit_of(step)
    if reason or not 0 <= ran["exit"] < 128:
        raise Refused(
            reason if reason in REASONS else "killed", f"{step.name} was stopped: {step.exit}, {step.limit}"
        )


def verify_file(path: Path, digest: str | None, size: int | None) -> None:
    if digest is None or size is None:
        if path.exists() or digest is not None or size is not None:
            raise Refused("evidence_malformed", f"inconsistent file observation for {path}")
    elif not path.is_file() or path.stat().st_size != size or hashing.sha256_file(path) != digest:
        raise Refused("evidence_malformed", f"size or digest differs from {path}")


def verify_artifacts(plan: dict[str, Any], e: dict[str, Any]) -> bool:
    """Re-read immutable files. A differing Argon2 result needs a computed known-answer vector."""
    out = Path(e["out"])
    logs = out / "logs"
    for key, digest in e["replaced"].items():
        if key in plan["replace"] and hashing.sha256_file(Path(plan["replace"][key])) != digest:
            raise Refused("evidence_malformed", f"replacement differs from the planned IR for {key}")
    for run in e["runs"]:
        program = Path(run["argv"][0]).resolve(strict=True)
        if not program.is_relative_to(out) or program != Path(run["program"]) or not program.is_file():
            raise Refused("not_the_plan", f"workload program differs from {program}")
        verify_file(logs / f"run-{run['workload']}.stdout", run["stdout_sha256"], run["stdout_size"])
    index: dict[str, int] = {}
    witnessed = True
    for check in e["checks"]:
        expected, result = Path(check["expected"]), Path(check["result"])
        for path, kind in ((expected, "expected"), (result, "result")):
            verify_file(path, check[f"{kind}_sha256"], check[f"{kind}_size"])
        name = check["workload"]
        i = index.get(name, 0)
        index[name] = i + 1
        marker = logs / f"check-{name}-{i}.comparison"
        recorded = marker.read_text().strip() if marker.is_file() else None
        if recorded != check["comparison"]:
            raise Refused("evidence_malformed", "comparison differs from the native test's observation")
        if recorded == "different":
            # The pinned test's first line is tv[0]: one hex encoding on success, an error message on failure.
            # Even if the test ran to completion, a resource-dependent diagnostic is not a computed answer.
            with expected.open("rb") as want, result.open("rb") as got:
                reference, actual = want.readline().rstrip(b"\n"), got.readline().rstrip(b"\n")
            witnessed &= bool(
                name == "argon2id"
                and len(reference) == len(actual) == 310
                and re.fullmatch(b"[0-9a-f]+", reference)
                and re.fullmatch(b"[0-9a-f]+", actual)
                and reference != actual
            )
    return witnessed


def judge(planned: dict[str, Any], e: dict[str, Any]) -> dict[str, bool]:
    """Each check `kernels.variant` and `kernels.rejected` need, of what variants.nix planned against what
    the build wrote down. Raises Refused where the evidence doesn't follow the plan, the build didn't end
    whole, or a command was stopped, none of which decides anything."""
    plan = filled(planned, planned["out"], e["out"])
    for found in [
        *(c[k] for c in e["checks"] for k in ("expected_sha256", "result_sha256")),
        *e["replaced"].values(),
        *(r["stdout_sha256"] for r in e["runs"]),
    ]:
        if found is not None and not SHA256.fullmatch(found):
            raise Refused("evidence_malformed", f"{found[:80]!r} isn't a SHA-256")
    # The build: a prefix of the plan's steps, which stops only where a step failed.
    built = [b["argv"] for b in e["build"]]
    if built != plan["build"][: len(built)]:
        raise Refused("not_the_plan", "the build's steps aren't the plan's")
    for b in e["build"]:
        require_exit(b)
    if built != plan["build"] or any(b["exit"] != 0 for b in e["build"]):
        raise Refused("build_failed", "The observed build steps were incomplete or failed")
    if plan["attempt"] != e["attempt"] or sorted(plan["table"]) != sorted(plan["replace"]):
        raise Refused("not_the_plan", "attempt or replacement plan differs")
    if set(e["dispatch"]) != set(FEATURES):
        raise Refused("dispatch_failed", "missing runtime feature observations")
    if not all(e["dispatch"].values()):
        raise Refused("missing_features", str(e["dispatch"]))
    for observed in [k for c in e["checks"] for k in c["commands"]] + e["runs"]:
        require_exit(observed)
    # Each check and run as planned, in the plan's order, each once.
    want = [(w["name"], c["run"], c["expected"], c["result"]) for w in plan["workloads"] for c in w["checks"]]
    got = [
        (c["workload"], [k["argv"] for k in c["commands"]], c["expected"], c["result"]) for c in e["checks"]
    ]
    launches = [(w["name"], w["run"]["env"], w["run"]["argv"]) for w in plan["workloads"]]
    if got != want or [(r["workload"], r["env"], r["argv"]) for r in e["runs"]] != launches:
        raise Refused("not_the_plan", "a check's commands or files, or a run's launch, aren't the plan's")
    if outside := [r["program"] for r in e["runs"] if not r["program"].startswith(e["out"] + "/")]:
        raise Refused("not_the_plan", f"a run's program leads outside the build: {outside[0][:120]}")
    try:
        witnessed = verify_artifacts(plan, e)
    except (OSError, UnicodeError) as error:
        raise Refused("evidence_malformed", str(error)) from error
    table = sorted(planned["table"])
    outputs = {w["name"]: w["outputs"] for w in plan["workloads"]}
    touched = {e["compiled"].get(key) for key in table}
    # A result is an answer only if it's fresh and has bytes, and so is what it's compared with.
    completed = witnessed and all(
        all(k["exit"] == 0 for k in c["commands"])
        and c["comparison"] == ("equal" if c["expected_sha256"] == c["result_sha256"] else "different")
        and c["result_before"] is False
        and None not in (c["result_sha256"], c["expected_sha256"])
        and (c["result_size"] or 0) > 0
        and (c["expected_size"] or 0) > 0
        for c in e["checks"]
    )
    # A run is an answer only if it exited 0, with output where the manifest has its hash.
    each_ran = all(r["exit"] == 0 and (r["stdout_size"] > 0 or not outputs[r["workload"]]) for r in e["runs"])
    answers = [c["result_sha256"] == c["expected_sha256"] for c in e["checks"]]
    matched = [r["stdout_sha256"] == want for r in e["runs"] for want in outputs[r["workload"]]]
    return {
        "replaced_once": sorted(e["replaced"]) == table,
        # Every object the build compiled from a unit the table touches is in the table.
        "units_whole": None not in touched
        and all(key in table for key, unit in e["compiled"].items() if unit in touched),
        "checks_completed": completed,
        "runs_completed": each_ran,
        "answers_match": all(answers),
        "outputs_match": all(matched),
        "an_answer_differs": completed and each_ran and not all([*answers, *matched]),
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


def realize(name: str, repo: Path, commit: str, attempt: str = "default") -> dict[str, Any]:
    """The answer about one build, from the archive of `repo` at `commit`, which this has to run from."""
    if not NAME.fullmatch(name):
        raise Refused("invalid_request", f"{name!r} isn't a build's name")
    snapshot, path = archive(repo, commit)
    if not snapshot.ok or path is None:
        raise stopped_or(snapshot, "snapshot_failed", f"nix flake archive ended with {snapshot.exit}")
    if path != ROOT:
        raise Refused(
            "not_the_snapshot", f"{commit} of {repo} is archived at {path}, and this runs from {ROOT}"
        )
    if problems := kernels.validate(kernels.load(HERE / "manifest.toml")):
        raise Refused("manifest_invalid", "; ".join(problems)[:500])
    if not re.fullmatch(r"[a-zA-Z0-9_-]+", attempt):
        raise Refused("invalid_request", "invalid attempt label")
    attribute = f"path:{ROOT}#kernels.{PROJECT}.{name}"
    target = [attribute]
    plan = [f"{attribute}.planned"]
    if attempt != "default":
        expression = (
            f'let f = builtins.getFlake "path:{ROOT}"; '
            f'in (f.legacyPackages.x86_64-linux.kernels.forAttempt "{attempt}").{PROJECT}.{name}'
        )
        target = ["--impure", "--expr", expression]
        plan = ["--impure", "--expr", f"({expression}).planned"]
    flags = ["--json", "--no-update-lock-file"]
    evaluate = proc.run(["nix", "eval", *flags, *plan], timeout=QUERY_SECONDS)
    if not evaluate.ok:
        raise stopped_or(evaluate, "evaluation_failed", evaluate.err[-600:])
    build = proc.run(["nix", "build", *flags, "--no-link", *target], timeout=BUILD_SECONDS)
    if not build.ok:
        raise stopped_or(build, "build_failed", build.err[-600:])
    built = parsed(build.out, "nix build's answer")
    out = built[0].get("outputs", {}).get("out") if isinstance(built, list) and len(built) == 1 else None
    if not isinstance(out, str) or not out.startswith("/nix/store/"):
        raise Refused("tool_failed", f"nix build named no output: {build.out[:200]}")
    try:
        text = (Path(out) / "evidence" / "evidence.json").read_text()
    except OSError as error:
        raise Refused("evidence_malformed", str(error)) from error
    evidence = parsed(text, "the evidence", "evidence_malformed")
    if not isinstance(evidence, dict) or evidence.get("schema") != schemas.KERNELS_EVIDENCE:
        raise Refused("evidence_malformed", f"the evidence isn't {schemas.KERNELS_EVIDENCE}")
    if evidence.get("attempt") != attempt:
        raise Refused("not_the_plan", "evidence belongs to another attempt")
    if evidence.get("out") != out:
        raise Refused("not_the_plan", f"the evidence is of {str(evidence.get('out'))[:80]}, not {out}")
    ended = (("snapshot", snapshot), ("evaluate", evaluate), ("realize", build))
    answer, granted = answer_of(
        parsed(evaluate.out, "the derivation's plan"),
        evidence,
        {step: Step(step, ran.exit, ran.limit) for step, ran in ended},
        name=name,
        attempt=attempt,
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
    try:
        flags = set(Path("/proc/cpuinfo").read_text().split())
    except OSError:
        # Not Linux: nothing here says what the processor has, so it's taken to have none of them.
        return list(FEATURES)
    return sorted(f for f in FEATURES if f not in flags)


class Parser(argparse.ArgumentParser):
    """argparse, but a command line that isn't this tool's is `invalid_request`, exit 1, and never the exit
    code of a grant."""

    def error(self, message: str) -> Any:
        print(json.dumps(said(None, "invalid_request", message)))
        sys.exit(TABLE["invalid_request"][1])


def main() -> int:
    parser = Parser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["realize"])
    parser.add_argument("name")
    parser.add_argument("--attempt", default="default", help="Nix cache identity for this evidence attempt")
    parser.add_argument("--pretty", action="store_true")
    # This tool's own, for when it runs itself again from the archive.
    parser.add_argument("--repo", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--commit", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        if args.repo is None or args.commit is None:
            commit = commit_of(ROOT)
            snapshot, path = archive(ROOT, commit)
            if not snapshot.ok or path is None:
                raise stopped_or(snapshot, "snapshot_failed", f"nix flake archive ended with {snapshot.exit}")
            entry = path / "bench" / "kernels" / "variants.py"
            if not entry.is_file() or not os.access(entry, os.R_OK):
                raise Refused("snapshot_failed", f"{commit} has no readable bench/kernels/variants.py")
            again = [
                str(entry),
                *sys.argv[1:],
                "--repo",
                str(ROOT),
                "--commit",
                commit,
            ]
            # Isolated: no PYTHONPATH, user site or current directory, so every module is the copy's.
            try:
                os.execve(
                    sys.executable,
                    [sys.executable, "-I", *again],
                    {k: v for k, v in os.environ.items() if not k.startswith("PYTHON")},
                )
            except OSError as error:
                raise Refused("snapshot_failed", f"could not launch {entry}: {error}") from error
        answer = realize(args.name, args.repo, args.commit, args.attempt)
    except Refused as refused:
        answer = said(None, refused.reason, refused.detail, name=args.name)
    except OSError as error:
        answer = said(None, "tool_failed", str(error), name=args.name)
    print(json.dumps(answer, indent=2 if args.pretty else None, sort_keys=True))
    return answer["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
