#!/usr/bin/env python3
"""Checks that wrong, unknown and stale verification results are never counted as proof.

Each case in tests/verification_negative/cases/ is a pair of LLVM functions, `src` before an optimization
and `tgt` after, with a claim that `tgt` is a correct replacement, and what has to come of checking it. Most
of the rewrites are wrong, or right only outside what the model covers. A few are right, and have to be
certified, so the rest can't pass by everything failing.

A result counts as a certificate only if `gate` accepts it, which is this file's own reading of what
tools/verify.py printed: proved, by every check, for the claim and the files the case names, with the
toolchain it would run now. Everything else is not certified, whatever the reason: a counterexample, an
unsupported function, a timeout, a crash, a result for other files, or one that doesn't parse.
docs/llvm-negative-verification.md has the cases, the reasons, what this trusts, and how CI runs it.

usage: tests/verify_negative.py [--tier static|live|all] [--tool PATH] [--only ID ...] [--out DIR]
                                [--case-timeout S] [--case-memory-mb MB] [--min-available-mb MB]
                                [--list] [--write-fixture]

`static` needs only Python: it checks the gate on a stored result and on broken ones, and the runner on
checkers that hang, crash or print nonsense. `live` runs tools/verify.py on each case, one at a time, and
needs the dev shell, `lake build` and build/ir-lean. The exit code is 0 if every case came out as expected,
1 if any didn't, 2 for a usage or manifest error, and 3 if a case couldn't run, such as without the
toolchain or enough memory.
"""

import argparse
import contextlib
import copy
import hashlib
import importlib.util
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "tests" / "verification_negative"
CASES = CORPUS / "cases"
STUBS = CORPUS / "stubs"
FIXTURE = CORPUS / "fixtures" / "control_result.json"
FIXTURE_CASE = "control_mul2_to_shl1"
# The result and the precondition probe of a control with a precondition, for the probe's static cases.
PROBE_FIXTURE = CORPUS / "fixtures" / "precondition_envelope.json"
PROBE_CASE = "control_precondition_sufficient"
RUNS = ROOT / "build" / "verify-negative"
RUNS_KEPT = 5
VERIFY = ROOT / "tools" / "verify.py"
# What decides a verdict besides the inputs. A stored result checked by other versions of these is stale.
CHECKER_FILES = ["tools/verify.py", "tools/verify_check.lean", "tests/check_axioms.lean"]

CASE_SCHEMA = "ir-lean.verification-negative.case/1"
ENVELOPE_SCHEMA = "ir-lean.verification-negative.envelope/1"
REPORT_SCHEMA = "ir-lean.verification-negative.report/1"
RESULT_SCHEMA = "ir-lean.verify/1"
CASE_FIELDS = {
    "schema",
    "category",
    "summary",
    "llvm_verdict",
    "why",
    "model_limitation",
    "claim",
    "pin_override",
    "names",
    "precondition_witness",
    "request",
    "stale",
    "expect",
}
CATEGORIES = {
    "control",
    "wrong_transformation",
    "poison",
    "freeze",
    "precondition",
    "unsupported",
    "artifact_mismatch",
    "artifact_malformed",
    "resource",
    "stale",
}
VERDICTS = {"valid", "invalid", "n/a"}
PIN_MATCHES = {"syntactic", "reducible_defeq"}
# What "tgt refines src" says for one input, for functions from integers to an integer: undefined behavior
# in src allows anything; a src that never finishes needs a tgt that never finishes; a poison src result
# allows any result; a value allows only itself. Anything else, a model stop in src above all, allows
# nothing, since the model doesn't know what LLVM does there. Equality isn't this: it lets a stop in tgt
# match the same stop in src.
#
# It names only Lean, IRLean and the generated module, so a statement can pin it: a `match` would make an
# auxiliary definition in the proof module, which tools/verify.py never lets a pinned statement name. It's
# decidable, so a witness can be decided by running it. The reasons are listed rather than the model stops,
# so a reason added to IRLean.UB later makes the claim stricter, never weaker.
UB_REASONS = (
    "branchOnPoison switchOnPoison assumeFailed unreachable divByZero divByPoison divOverflow "
    "noundefPoison badAccess misaligned poisonPointer writeToConstant overlappingCopy badFree "
    "forbiddenWrite forbiddenAccess expiredProvenance forbiddenFree"
).split()
RETURNS = "IRLean.andThen ({0}) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()"
REFINES = " ∨ ".join(
    [
        "(∃ r ∈ [" + ", ".join(f"IRLean.UB.{r}" for r in UB_REASONS) + "], {src} = IRLean.Outcome.ub r)",
        "({src} = Option.none ∧ {tgt} = Option.none)",
        "({src} = IRLean.Outcome.ok Option.none ∧ " + RETURNS.format("{tgt}") + ")",
        "({src} ≠ IRLean.Outcome.ok Option.none ∧ " + RETURNS.format("{src}") + " ∧ {tgt} = {src})",
    ]
)
CLAIM_FIELDS = {"binders", "hypotheses", "src", "tgt"}

# Every reason the gate can give for not certifying. A new one goes in the doc's table too.
DENIALS = {
    "harness_timeout": "The runner's watchdog killed the checker",
    "harness_killed": "The checker was killed, as the OOM killer does",
    "harness_crash": "The checker died with another signal",
    "result_unreadable": "The checker printed no JSON object",
    "result_malformed": "The result is JSON, without the fields or types a result has",
    "schema_mismatch": "The result's schema isn't ir-lean.verify/1",
    "not_proved": "The status isn't proved with reason kernel_checked",
    "exit_mismatch": "The exit code doesn't match the status, or the process's exit doesn't match it",
    "contract_violation": "tools/verify.py's own assert_contract rejects the result",
    "check_missing": "A check tools/verify.py defines is missing from the result",
    "check_duplicate": "A check appears twice",
    "check_not_passed": "A required check didn't pass, or an optional one failed",
    "witness_failed": "A witness made the claim false, or there's a counterexample",
    "no_proof": "The request had no proof or no theorem",
    "wrong_target": "The result is about another function, or its claim doesn't name the target",
    "unpinned": "The request didn't pin a statement, so nothing ties the theorem to the claim",
    "pin_mismatch": "The pinned statement isn't the case's claim, or the theorem doesn't match it",
    "claim_missing_function": "The claim doesn't name every function the case's claim is about",
    "hypotheses_undeclared": "The theorem's hypotheses aren't the preconditions the case declares",
    "hypotheses_unwitnessed": "No input was shown to meet the preconditions, so the theorem may say nothing",
    "artifact_roles_mismatch": "The result hashed other inputs than the case has",
    "stale_input": "The IR or C it checked isn't the case's IR now",
    "stale_proof": "The proof it checked isn't the case's proof now",
    "stale_support": "A support module it checked isn't the case's now",
    "stale_library": "The IRLean library it used isn't the one built now",
    "stale_tool": "The ir-lean binary it used isn't the one there now",
    "stale_emitter": "The emitter's commit isn't the one checked out now",
    "dirty_emitter": "The emitter had uncommitted changes, so no commit says what it was",
    "stale_lean": "The Lean it used isn't the one on PATH now",
    "stale_checker": "tools/verify.py, tools/verify_check.lean or tests/check_axioms.lean changed since",
}


class ManifestError(Exception):
    pass


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checker_hashes() -> dict[str, str]:
    return {name: sha256_file(ROOT / name) for name in CHECKER_FILES}


def load_verify() -> Any:
    spec = importlib.util.spec_from_file_location("verify_tool", VERIFY)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# Cases


@dataclass
class Case:
    id: str
    directory: Path
    manifest: dict[str, Any]

    @property
    def request(self) -> dict[str, Any]:
        return self.manifest["request"]

    @property
    def expect(self) -> dict[str, Any]:
        return self.manifest["expect"]


def load_case(directory: Path) -> Case:
    path = directory / "case.json"
    try:
        manifest = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise ManifestError(f"{path}: {error}") from error
    where = directory.name

    def need(condition: bool, message: str) -> None:
        if not condition:
            raise ManifestError(f"{where}: {message}")

    need(isinstance(manifest, dict), "not a JSON object")
    need(set(manifest) <= CASE_FIELDS, f"unknown fields {sorted(set(manifest) - CASE_FIELDS)}")
    need(manifest.get("schema") == CASE_SCHEMA, f"schema isn't {CASE_SCHEMA}")
    need(manifest.get("category") in CATEGORIES, f"category {manifest.get('category')!r}")
    need(manifest.get("llvm_verdict") in VERDICTS, f"llvm_verdict {manifest.get('llvm_verdict')!r}")
    for key in ("summary", "why"):
        need(isinstance(manifest.get(key), str) and manifest[key], f"{key} is missing")
    request = manifest.get("request")
    need(
        isinstance(request, dict) and isinstance(request.get("function"), str), "request.function is missing"
    )
    need("namespace" in request, "request.namespace is missing: the gate needs the Lean constant")
    claim = manifest.get("claim", "missing")
    need(
        claim is None or (isinstance(claim, dict) and set(claim) == CLAIM_FIELDS),
        f"claim needs {CLAIM_FIELDS}",
    )
    need(
        claim is None
        or all("r" not in group.split() for group in re.findall(r"[({\[]([^:(){}\[\]]*):", claim["binders"])),
        "a claim can't bind r, which the template binds",
    )
    need("statement" not in request, "the runner writes request.statement: use claim, or pin_override")
    override = manifest.get("pin_override")
    need(override is None or (isinstance(override, dict) and set(override) == {"statement"}), "pin_override")
    need(claim is not None or override is not None, "a case without a claim has to say what it pins")
    need(isinstance(manifest.get("names"), list), "names is missing")
    expect = manifest.get("expect")
    need(isinstance(expect, dict) and isinstance(expect.get("certified"), bool), "expect.certified")
    need(set(expect) <= {"certified", "verify", "gate"}, f"unknown expect fields {sorted(expect)}")
    need(isinstance(expect.get("verify"), list) and expect["verify"], "expect.verify lists no outcome")
    need(set(expect.get("gate", [])) <= set(DENIALS), f"unknown denials in {expect.get('gate')}")
    need(
        expect["certified"] == (not expect.get("gate")),
        "a case is certified exactly when it expects no denial",
    )
    need(
        not expect["certified"] or expect["verify"] == ["proved/kernel_checked"],
        "a certified case can only expect proved/kernel_checked",
    )
    stale = manifest.get("stale")
    if stale is not None:
        need(manifest["category"] == "stale", "only stale cases edit their files")
        need(set(stale) == {"file", "old", "new"}, "stale needs file, old and new")
    need(
        ("precondition_witness" in manifest) == bool(claim and claim["hypotheses"]),
        "a claim with hypotheses needs a precondition_witness, and only then",
    )
    inputs = [request.get("input", {}).get("ir") or request.get("input", {}).get("c")]
    inputs += [request.get("proof"), *request.get("support", [])]
    for name in filter(None, inputs):
        need((directory / name).is_file(), f"{name} doesn't exist")
    return Case(directory.name, directory, manifest)


def load_cases(only: list[str] | None) -> list[Case]:
    cases = [load_case(d) for d in sorted(CASES.iterdir()) if d.is_dir()]
    names = {c.id for c in cases}
    if only:
        unknown = set(only) - names - {s.id for s in static_cases()}
        if unknown:
            raise ManifestError(f"no such case: {', '.join(sorted(unknown))}")
        cases = [c for c in cases if c.id in only]
    return cases


# Running the checker


@dataclass
class Harness:
    exit: int | None
    signal: int | None
    timed_out: bool
    seconds: float
    peak_rss_mb: int
    stdout: str
    stderr: str


def run_checker(argv: list[str], timeout: float, logs: Path) -> Harness:
    """Runs one checker in its own process group, with a watchdog that kills the whole group, and measures the
    peak memory of the largest process in it that was waited for."""
    logs.mkdir(parents=True, exist_ok=True)
    out_path, err_path = logs / "stdout.txt", logs / "stderr.txt"
    started = time.monotonic()
    with out_path.open("w") as out, err_path.open("w") as err:
        process = subprocess.Popen(
            argv, stdout=out, stderr=err, stdin=subprocess.DEVNULL, cwd=ROOT, start_new_session=True
        )
        fired = threading.Event()

        def kill() -> None:
            fired.set()
            kill_group(process.pid)

        watchdog = threading.Timer(timeout, kill)
        watchdog.start()
        try:
            _, status, usage = os.wait4(process.pid, 0)
        finally:
            watchdog.cancel()
            # Whatever the checker left behind goes with it.
            kill_group(process.pid)
        process.returncode = os.waitstatus_to_exitcode(status)
    code = process.returncode
    return Harness(
        exit=code if code >= 0 else None,
        signal=-code if code < 0 else None,
        timed_out=fired.is_set(),
        seconds=round(time.monotonic() - started, 2),
        peak_rss_mb=usage.ru_maxrss // 1024,
        stdout=out_path.read_text(errors="replace"),
        stderr=err_path.read_text(errors="replace"),
    )


def kill_group(pid: int) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(pid, signal.SIGKILL)


def parse_result(stdout: str) -> Any:
    try:
        return json.loads(stdout)
    except json.JSONDecodeError:
        return None


def envelope_for(harness: Harness, checkers: dict[str, str], probe: dict[str, Any] | None) -> dict[str, Any]:
    return {
        "schema": ENVELOPE_SCHEMA,
        "result": parse_result(harness.stdout),
        "harness": {
            "exit": harness.exit,
            "signal": harness.signal,
            "timed_out": harness.timed_out,
            "seconds": harness.seconds,
            "peak_rss_mb": harness.peak_rss_mb,
        },
        "checker_sha256": checkers,
        "probe": probe,
    }


# The gate


def canonical(claim: dict[str, Any]) -> str:
    """The statement a certificate for this claim has to pin."""
    hypotheses = "".join(f"{h} → " for h in claim["hypotheses"])
    return f"∀ {claim['binders']}, {hypotheses}{REFINES.format(src=claim['src'], tgt=claim['tgt'])}"


def pinned_statement(case: Case) -> str | None:
    """What the request pins: the canonical claim, unless the case is about pinning something else."""
    override = case.manifest.get("pin_override")
    return override["statement"] if override is not None else canonical(case.manifest["claim"])


def precondition_of(case: Case) -> dict[str, Any] | None:
    claim = case.manifest.get("claim")
    if not claim or not claim["hypotheses"]:
        return None
    return {
        "binders": claim["binders"],
        "hypotheses": claim["hypotheses"],
        "subject": claim["tgt"],
        "witness": case.manifest["precondition_witness"],
    }


def probe_statement(pre: dict[str, Any]) -> str:
    """A statement that's false exactly where every precondition holds, so a witness refuting it is an input
    meeting them. Its subject names the target, which tools/verify.py needs before it evaluates anything."""
    chain = " → ".join(pre["hypotheses"])
    return f"∀ {pre['binders']}, {chain} → {pre['subject']} ≠ {pre['subject']}"


def gate(envelope: Any, expected: dict[str, Any], v: Any) -> list[str]:
    """Why this envelope doesn't certify the expected claim, or nothing if it does. Anything unexpected about
    the envelope's shape is a reason, never a pass."""
    denials: list[str] = []

    def deny(code: str) -> None:
        assert code in DENIALS, code
        if code not in denials:
            denials.append(code)

    try:
        _gate(envelope, expected, v, deny)
    except (AttributeError, KeyError, TypeError, ValueError, IndexError):
        deny("result_malformed")
    return denials


def _gate(envelope: Any, expected: dict[str, Any], v: Any, deny: Callable[[str], None]) -> None:
    if not isinstance(envelope, dict) or envelope.get("schema") != ENVELOPE_SCHEMA:
        deny("result_malformed")
        return
    harness = envelope.get("harness")
    if not isinstance(harness, dict):
        deny("result_malformed")
        return
    if harness.get("timed_out") is not False:
        deny("harness_timeout")
    if harness.get("signal") == signal.SIGKILL and not harness.get("timed_out"):
        deny("harness_killed")
    elif harness.get("signal") not in (None, signal.SIGKILL):
        deny("harness_crash")
    result = envelope.get("result")
    if result is None:
        deny("result_unreadable")
        return
    if not isinstance(result, dict):
        deny("result_malformed")
        return
    if result.get("schema") != RESULT_SCHEMA:
        deny("schema_mismatch")
    if result.get("status") != "proved" or result.get("reason") != "kernel_checked":
        deny("not_proved")
    # Exactly ints: in Python, false == 0.
    exit_code, process_exit = result.get("exit_code"), harness.get("exit")
    if (
        type(exit_code) is not int
        or type(process_exit) is not int
        or exit_code != v.EXIT_CODES.get(result.get("status"))
        or process_exit != exit_code
    ):
        deny("exit_mismatch")
    # It raises KeyError, not AssertionError, for a result missing a check, so any exception counts.
    try:
        v.assert_contract(result)
    except Exception:
        deny("contract_violation")

    checks = result["checks"]
    if not isinstance(checks, list) or not all(isinstance(c, dict) for c in checks):
        raise TypeError("checks")
    names = [c["name"] for c in checks]
    if len(set(names)) != len(names):
        deny("check_duplicate")
    if {n for n, _ in v.CHECKS} - set(names):
        deny("check_missing")
    found = {c["name"]: c["result"] for c in checks}
    if any(found.get(name) != "pass" for name in v.REQUIRED) or any(
        c["result"] == "fail" for c in checks if c["name"] in v.OPTIONAL
    ):
        deny("check_not_passed")
    witnesses = result.get("witnesses") or []
    if result.get("counterexample") is not None or any(w.get("result") == "fails" for w in witnesses):
        deny("witness_failed")

    request = result["request"]
    if not isinstance(request, dict) or "proof" not in request or "theorem" not in request:
        deny("no_proof")
    target = result.get("target") or {}
    claim = result.get("claim") or {}
    if (
        target.get("function") != expected["function"]
        or target.get("lean_constant") != f"{expected['namespace']}.{expected['function']}"
        or claim.get("mentions_target") is not True
    ):
        deny("wrong_target")
    if claim.get("pinned") is None:
        deny("unpinned")
    elif claim["pinned"] != expected["pin"] or claim.get("pin_match") not in PIN_MATCHES:
        deny("pin_mismatch")
    if set(expected["names"]) - set(claim.get("generated_constants") or []):
        deny("claim_missing_function")

    hypotheses = [b["type"] for b in claim.get("binders") or [] if b.get("hypothesis")]
    declared = (expected.get("precondition") or {}).get("hypotheses", [])
    if hypotheses != declared:
        deny("hypotheses_undeclared")
    if hypotheses and not probe_witnessed(envelope.get("probe"), expected):
        deny("hypotheses_unwitnessed")

    files = (result.get("artifacts") or {}).get("files")
    if not isinstance(files, dict):
        raise TypeError("artifacts.files")
    if set(files) != set(expected["files"]):
        deny("artifact_roles_mismatch")
    for role, digest in expected["files"].items():
        if (files.get(role) or {}).get("sha256") != digest:
            deny("stale_input" if role == "input" else "stale_proof" if role == "proof" else "stale_support")
    versions = result.get("versions") or {}
    want = expected["versions"]
    if versions.get("irlean_library_sha256") != want["irlean_library_sha256"]:
        deny("stale_library")
    if versions.get("ir_lean_binary_sha256") != want["ir_lean_binary_sha256"]:
        deny("stale_tool")
    emitter = str(versions.get("ir_lean"))
    # A result made in this run is about the tree as it is, uncommitted changes and all. A stored one has to
    # name a commit, or nothing says what checked it.
    dirty = emitter.endswith("with local changes") and not expected.get("this_run")
    if dirty or emitter == "unknown":
        deny("dirty_emitter")
    if emitter != want["ir_lean"]:
        deny("stale_emitter")
    if versions.get("lean") != want["lean"]:
        deny("stale_lean")
    if envelope.get("checker_sha256") != expected["checker_sha256"]:
        deny("stale_checker")


def probe_witnessed(probe: Any, expected: dict[str, Any]) -> bool:
    """The probe is the runner's own: the statement it built from the case's preconditions, refuted at a
    witness, for the same IR, by a checker that exited as a counterexample does."""
    if not isinstance(probe, dict) or not isinstance(probe.get("result"), dict):
        return False
    result = probe["result"]
    pre = expected.get("precondition")
    files = (result.get("artifacts") or {}).get("files") or {}
    found = result.get("counterexample")
    counterexample = 2
    return (
        pre is not None
        and result.get("status") == "counterexample"
        and result.get("exit_code") == counterexample
        and probe.get("exit") == counterexample
        and probe.get("signal") is None
        and probe.get("timed_out") is False
        and isinstance(found, dict)
        and found.get("result") == "fails"
        and (result.get("request") or {}).get("statement") == probe_statement(pre)
        and (files.get("input") or {}).get("sha256") == expected["files"].get("input")
    )


# Expectations


def current_versions(v: Any, tool: Path) -> dict[str, str]:
    lean = subprocess.run(["lean", "--version"], capture_output=True, text=True, check=False)
    return {
        "irlean_library_sha256": v.library_hash(),
        "ir_lean_binary_sha256": sha256_file(tool) if tool.is_file() else "missing",
        "ir_lean": v.emitter_commit(),
        "lean": ((lean.stdout + lean.stderr).strip().splitlines() or ["unknown"])[0],
    }


def expected_for(
    case: Case, files_dir: Path, versions: dict[str, str], this_run: bool = False
) -> dict[str, Any]:
    request = case.request
    files = {"input": sha256_file(files_dir / (request["input"].get("ir") or request["input"]["c"]))}
    if "proof" in request:
        files["proof"] = sha256_file(files_dir / request["proof"])
        for i, support in enumerate(request.get("support", [])):
            files[f"support[{i}]"] = sha256_file(files_dir / support)
    return {
        "function": request["function"],
        "namespace": request["namespace"],
        # No claim means the model has none to certify, and nothing can match None.
        "pin": canonical(case.manifest["claim"]) if case.manifest.get("claim") else None,
        "names": case.manifest["names"],
        "precondition": precondition_of(case),
        "files": files,
        "versions": versions,
        "checker_sha256": checker_hashes(),
        "this_run": this_run,
    }


# Outcomes


@dataclass
class Outcome:
    id: str
    tier: str
    category: str
    outcome: str  # pass, fail, not_run or blocked
    certified: bool = False
    verify: str | None = None
    denials: list[str] = field(default_factory=list)
    problems: list[str] = field(default_factory=list)
    seconds: float = 0.0
    peak_rss_mb: int = 0
    note: str = ""

    def line(self) -> str:
        tag = {"pass": "ok   ", "fail": "FAIL ", "not_run": "SKIP ", "blocked": "BLOCK"}[self.outcome]
        verdict = "certified" if self.certified else "not certified"
        detail = "never certified" if self.outcome == "blocked" else f"{self.verify or '-'}; {verdict}"
        if self.denials:
            detail += f" ({', '.join(self.denials)})"
        if self.problems:
            detail += f": {'; '.join(self.problems)}"
        elif self.note:
            detail += f": {self.note}"
        return f"{tag} {self.tier:6} {self.id}: {detail}"


def judge(outcome: Outcome, expect: dict[str, Any], result: Any) -> None:
    """Whether the case came out as it has to. A not-certified case also has to fail for its own reason, so a
    broken toolchain can't pass every negative case at once."""
    if isinstance(result, dict) and "status" in result:
        outcome.verify = f"{result.get('status')}/{result.get('reason')}"
    outcome.certified = not outcome.denials
    problems = outcome.problems
    if outcome.certified != expect["certified"]:
        problems.append("certified, and mustn't be" if outcome.certified else "not certified, and has to be")
    if "verify" in expect and outcome.verify not in expect["verify"]:
        problems.append(f"tools/verify.py said {outcome.verify}, not {' or '.join(expect['verify'])}")
    missing = [d for d in expect.get("gate", []) if d not in outcome.denials]
    if missing:
        problems.append(f"the gate didn't give {', '.join(missing)}")
    outcome.outcome = "fail" if problems else "pass"


# Live cases


@dataclass
class Live:
    v: Any
    tool: Path
    out: Path
    versions: dict[str, str]
    case_timeout: float
    case_memory_mb: int
    min_available_mb: int


def available_mb() -> int | None:
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) // 1024
    except OSError:
        return None
    return None


def live_prerequisites(tool: Path, v: Any) -> list[str]:
    missing = [f"{p} on PATH" for p in ("lean", "opt", "leanchecker") if shutil.which(p) is None]
    if not os.access(tool, os.X_OK):
        missing.append(f"ir-lean at {tool}")
    if not (v.LIBRARY / "IRLean.olean").exists():
        missing.append("the IRLean library: run `lake build`")
    return missing


def capped(request: dict[str, Any], live: Live) -> dict[str, Any]:
    """The case's request with the runner's limits, which a case can lower and never raise."""
    request = copy.deepcopy(request)
    limits = request.setdefault("limits", {})
    limits["timeout_seconds"] = min(limits.get("timeout_seconds", live.case_timeout), live.case_timeout)
    limits["memory_mb"] = min(limits.get("memory_mb", live.case_memory_mb), live.case_memory_mb)
    return request


def check_request(
    live: Live, request: dict[str, Any], files: Path, name: str, logs: Path
) -> tuple[Harness, dict[str, str]]:
    path = files / f"{name}.json"
    path.write_text(json.dumps(request, ensure_ascii=False, indent=2) + "\n")
    checkers = checker_hashes()
    argv = [sys.executable, str(VERIFY), "check", str(path), "--tool", str(live.tool)]
    argv += ["--work-dir", str(logs / "work")]
    # tools/verify.py stops itself at its limit. The watchdog is for when it doesn't.
    harness = run_checker(argv, request["limits"]["timeout_seconds"] + 60, logs)
    return harness, checkers


def run_live(case: Case, live: Live) -> Outcome:
    outcome = Outcome(case.id, "live", case.manifest["category"], "fail")
    free = available_mb()
    if free is not None and free < live.min_available_mb:
        outcome.outcome = "not_run"
        outcome.note = f"{free} MB available, under --min-available-mb {live.min_available_mb}"
        return outcome
    directory = live.out / "cases" / case.id
    files = directory / "files"
    shutil.copytree(case.directory, files, ignore=shutil.ignore_patterns("case.json"))
    request = capped(case.request, live)
    statement = pinned_statement(case)
    if statement is not None:
        request["statement"] = statement
    harness, checkers = check_request(live, request, files, "request", directory / "check")
    outcome.seconds, outcome.peak_rss_mb = harness.seconds, harness.peak_rss_mb
    probe = None
    pre = precondition_of(case)
    result = parse_result(harness.stdout)
    if pre is not None and isinstance(result, dict) and result.get("status") == "proved":
        probe_request = {
            "input": request["input"],
            "namespace": request["namespace"],
            "function": request["function"],
            "statement": probe_statement(pre),
            "witnesses": [pre["witness"]],
            "limits": request["limits"],
        }
        ran, _ = check_request(live, probe_request, files, "probe", directory / "probe")
        probe = {
            "result": parse_result(ran.stdout),
            "exit": ran.exit,
            "signal": ran.signal,
            "timed_out": ran.timed_out,
        }
        outcome.seconds += ran.seconds
        outcome.peak_rss_mb = max(outcome.peak_rss_mb, ran.peak_rss_mb)
    envelope = envelope_for(harness, checkers, probe)
    (directory / "envelope.json").write_text(json.dumps(envelope, indent=2, ensure_ascii=False) + "\n")
    expected = expected_for(case, files, live.versions, this_run=True)
    outcome.denials = live_denials = gate(envelope, expected, live.v)

    stale = case.manifest.get("stale")
    if stale is not None:
        if live_denials:
            outcome.problems.append(f"the result wasn't certified before the edit: {', '.join(live_denials)}")
        edited = files / stale["file"]
        text = edited.read_text()
        if text.count(stale["old"]) != 1:
            raise ManifestError(f"{case.id}: {stale['old']!r} isn't in {stale['file']} exactly once")
        edited.write_text(text.replace(stale["old"], stale["new"]))
        outcome.denials = gate(envelope, expected_for(case, files, live.versions, this_run=True), live.v)
        outcome.note = f"edited {stale['file']} after the run"
    judge(outcome, case.expect, result)
    budget = live.case_memory_mb * 5 // 4 + 512
    if outcome.peak_rss_mb > budget:
        outcome.problems.append(f"peak memory {outcome.peak_rss_mb} MB, over the budget of {budget} MB")
        outcome.outcome = "fail"
    return outcome


# Static cases: the gate on a stored result, and the runner on checkers that misbehave


def fixture_envelope(path: Path = FIXTURE) -> dict[str, Any]:
    stored = json.loads(path.read_text())
    result, probe = (stored["result"], stored["probe"]) if path == PROBE_FIXTURE else (stored, None)
    return {
        "schema": ENVELOPE_SCHEMA,
        "result": result,
        "harness": {"exit": 0, "signal": None, "timed_out": False, "seconds": 1.0, "peak_rss_mb": 1},
        "checker_sha256": checker_hashes(),
        "probe": probe,
    }


def fixture_expected(case: Case, path: Path = FIXTURE) -> dict[str, Any]:
    """What a stored control result has to match: the case's files as they are now, and the versions it
    recorded, since those are of the machine that made it."""
    result = fixture_envelope(path)["result"]
    return expected_for(case, case.directory, dict(result["versions"]))


Mutation = Callable[[dict[str, Any]], Any]


def mutate_result(change: Callable[[dict[str, Any]], None]) -> Mutation:
    def apply(envelope: dict[str, Any]) -> dict[str, Any]:
        change(envelope["result"])
        return envelope

    return apply


def set_check(name: str, value: str) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        for c in result["checks"]:
            if c["name"] == name:
                c["result"] = value

    return change


def status(value: str, reason: str, exit_code: int) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        result.update(status=value, reason=reason, exit_code=exit_code)

    return change


def hashed(role: str) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        result["artifacts"]["files"][role]["sha256"] = "0" * 64

    return change


def version(key: str, value: str) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        result["versions"][key] = value

    return change


def with_harness(**fields: Any) -> Mutation:
    def apply(envelope: dict[str, Any]) -> dict[str, Any]:
        envelope["harness"].update(fields)
        return envelope

    return apply


def truncated(envelope: dict[str, Any]) -> dict[str, Any]:
    text = json.dumps(envelope["result"])
    envelope["result"] = parse_result(text[: len(text) // 2])
    return envelope


def drop_check(name: str) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        result["checks"] = [c for c in result["checks"] if c["name"] != name]

    return change


def duplicate_check(result: dict[str, Any]) -> None:
    result["checks"].append({"name": "axioms", "result": "fail"})


def other_function(result: dict[str, Any]) -> None:
    result["target"].update(function="src", lean_constant="Opt.src")


def extra_hypothesis(result: dict[str, Any]) -> None:
    result["claim"]["binders"].append(
        {"binder": "explicit", "hypothesis": True, "name": "h", "type": "False"}
    )


def drop_name(result: dict[str, Any]) -> None:
    result["claim"]["generated_constants"] = ["Opt.tgt"]


def extra_role(result: dict[str, Any]) -> None:
    result["artifacts"]["files"]["support[0]"] = {"sha256": "0" * 64}


def claim_field(key: str, value: Any) -> Callable[[dict[str, Any]], None]:
    def change(result: dict[str, Any]) -> None:
        result["claim"][key] = value

    return change


def stale_checker(envelope: dict[str, Any]) -> dict[str, Any]:
    envelope["checker_sha256"] = {**envelope["checker_sha256"], "tools/verify.py": "0" * 64}
    return envelope


@dataclass
class Static:
    id: str
    run: Callable[["StaticContext"], tuple[Any, dict[str, Any]]]
    expect: dict[str, Any]
    note: str


@dataclass
class StaticContext:
    v: Any
    out: Path
    case: Case


def probe_case(name: str, change: Callable[[dict[str, Any]], None], denials: list[str], note: str) -> Static:
    """The stored control with a precondition, its probe changed. Without a change it's certified."""

    def run(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        envelope = fixture_envelope(PROBE_FIXTURE)
        change(envelope["probe"])
        return envelope, fixture_expected(load_case(CASES / PROBE_CASE), PROBE_FIXTURE)

    return Static(name, run, {"certified": not denials, "gate": denials}, note)


def mutation(name: str, change: Mutation, denials: list[str], note: str) -> Static:
    def run(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        return change(fixture_envelope()), fixture_expected(ctx.case)

    return Static(name, run, {"certified": False, "gate": denials}, note)


def support_differs(name: str) -> Static:
    """A support module the case has, and the result hashed in another version."""

    def run(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        envelope, expected = fixture_envelope(), fixture_expected(ctx.case)
        envelope["result"]["artifacts"]["files"]["support[0]"] = {"sha256": "0" * 64}
        expected["files"]["support[0]"] = "1" * 64
        return envelope, expected

    return Static(name, run, {"certified": False, "gate": ["stale_support"]}, "a support module changed")


def dirty_this_run(name: str) -> Static:
    """A result made in this run, in a tree with uncommitted changes, is about that tree, and certified."""

    def run(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        envelope, expected = fixture_envelope(), fixture_expected(ctx.case)
        dirty = envelope["result"]["versions"]["ir_lean"] + " with local changes"
        envelope["result"]["versions"]["ir_lean"] = dirty
        expected["versions"]["ir_lean"], expected["this_run"] = dirty, True
        return envelope, expected

    return Static(name, run, {"certified": True, "gate": []}, "uncommitted changes, checked in this run")


def stub(name: str, script: str, timeout: float, denials: list[str], note: str) -> Static:
    def run(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        harness = run_checker([str(STUBS / script)], timeout, ctx.out / "stubs" / name)
        return envelope_for(harness, checker_hashes(), None), fixture_expected(ctx.case)

    return Static(name, run, {"certified": False, "gate": denials}, note)


def static_cases() -> list[Static]:
    def control(ctx: StaticContext) -> tuple[Any, dict[str, Any]]:
        return fixture_envelope(), fixture_expected(ctx.case)

    m = mutation
    return [
        Static(
            "static_control",
            control,
            {"certified": True, "gate": []},
            "the stored control result, unchanged, is certified, so the gate isn't refusing everything",
        ),
        m("result_truncated", truncated, ["result_unreadable"], "half the JSON"),
        m("result_not_object", lambda e: {**e, "result": ["proved"]}, ["result_malformed"], "a list"),
        m("checks_not_list", mutate_result(lambda r: r.update(checks="all pass")), ["result_malformed"], ""),
        m(
            "schema_bumped",
            mutate_result(lambda r: r.update(schema="ir-lean.verify/2")),
            ["schema_mismatch"],
            "",
        ),
        m("status_timeout", mutate_result(status("timeout", "time_limit", 4)), ["not_proved"], "timeout"),
        m(
            "status_unsupported",
            mutate_result(status("unsupported", "function_unsupported", 3)),
            ["not_proved"],
            "",
        ),
        m("status_error", mutate_result(status("error", "proof_failed", 1)), ["not_proved"], ""),
        m("status_capitalized", mutate_result(status("Proved", "kernel_checked", 0)), ["not_proved"], ""),
        m(
            "reason_mismatch",
            mutate_result(status("proved", "witness_falsifies", 0)),
            ["not_proved", "contract_violation"],
            "proved, for a counterexample's reason",
        ),
        m("exit_code_mismatch", mutate_result(lambda r: r.update(exit_code=1)), ["exit_mismatch"], ""),
        m("process_exit_mismatch", with_harness(exit=1), ["exit_mismatch"], "the process exited 1"),
        m(
            "exit_code_bool",
            mutate_result(lambda r: r.update(exit_code=False)),
            ["exit_mismatch"],
            "false for 0, which Python calls equal",
        ),
        m("process_exit_bool", with_harness(exit=False), ["exit_mismatch"], "the process's exit as false"),
        m(
            "required_check_failed",
            mutate_result(set_check("kernel_replay", "fail")),
            ["check_not_passed", "contract_violation"],
            "kernel_replay failed, status still proved",
        ),
        m(
            "required_check_skipped",
            mutate_result(set_check("axioms", "skip")),
            ["check_not_passed", "contract_violation"],
            "",
        ),
        m("required_check_missing", mutate_result(drop_check("axioms")), ["check_missing"], ""),
        m("check_duplicated", mutate_result(duplicate_check), ["check_duplicate"], "axioms twice"),
        m("optional_check_failed", mutate_result(set_check("witnesses", "fail")), ["check_not_passed"], ""),
        m(
            "counterexample_attached",
            mutate_result(lambda r: r.update(counterexample={"result": "fails"})),
            ["witness_failed"],
            "",
        ),
        m("other_function", mutate_result(other_function), ["wrong_target"], "a result about src"),
        m("unpinned", mutate_result(claim_field("pinned", None)), ["unpinned"], ""),
        m("pin_weakened", mutate_result(claim_field("pinned", "True")), ["pin_mismatch"], ""),
        m("pin_unmatched", mutate_result(claim_field("pin_match", "mismatch")), ["pin_mismatch"], ""),
        m("claim_drops_src", mutate_result(drop_name), ["claim_missing_function"], ""),
        m(
            "hypothesis_added",
            mutate_result(extra_hypothesis),
            ["hypotheses_undeclared", "hypotheses_unwitnessed"],
            "",
        ),
        m("input_hash_differs", mutate_result(hashed("input")), ["stale_input"], ""),
        m("proof_hash_differs", mutate_result(hashed("proof")), ["stale_proof"], ""),
        support_differs("support_hash_differs"),
        m(
            "proof_removed",
            mutate_result(lambda r: r["request"].pop("proof")),
            ["no_proof", "contract_violation"],
            "proved, for a request with only a statement",
        ),
        m(
            "extra_artifact",
            mutate_result(extra_role),
            ["artifact_roles_mismatch"],
            "a support module it never had",
        ),
        m(
            "library_differs",
            mutate_result(version("irlean_library_sha256", "0" * 64)),
            ["stale_library"],
            "",
        ),
        m("tool_differs", mutate_result(version("ir_lean_binary_sha256", "0" * 64)), ["stale_tool"], ""),
        m("emitter_differs", mutate_result(version("ir_lean", "0" * 40)), ["stale_emitter"], ""),
        m(
            "emitter_dirty",
            mutate_result(
                lambda r: r["versions"].update(ir_lean=r["versions"]["ir_lean"] + " with local changes")
            ),
            ["dirty_emitter", "stale_emitter"],
            "",
        ),
        dirty_this_run("emitter_dirty_this_run"),
        m("lean_differs", mutate_result(version("lean", "Lean (version 4.0.0)")), ["stale_lean"], ""),
        m("checker_differs", stale_checker, ["stale_checker"], "tools/verify.py changed since the run"),
        probe_case("probe_control", lambda p: None, [], "a precondition an input meets, certified"),
        probe_case("probe_missing", lambda p: p.clear(), ["hypotheses_unwitnessed"], "no probe"),
        probe_case("probe_exit_mismatch", lambda p: p.update(exit=0), ["hypotheses_unwitnessed"], ""),
        probe_case("probe_crashed", lambda p: p.update(signal=11), ["hypotheses_unwitnessed"], ""),
        probe_case("probe_timed_out", lambda p: p.update(timed_out=True), ["hypotheses_unwitnessed"], ""),
        probe_case(
            "probe_result_exit_mismatch",
            lambda p: p["result"].update(exit_code=0),
            ["hypotheses_unwitnessed"],
            "",
        ),
        probe_case(
            "probe_status_not_counterexample",
            lambda p: p["result"].update(status="error"),
            ["hypotheses_unwitnessed"],
            "",
        ),
        probe_case(
            "probe_without_counterexample",
            lambda p: p["result"].update(counterexample=None),
            ["hypotheses_unwitnessed"],
            "",
        ),
        probe_case(
            "probe_witness_holds",
            lambda p: p["result"]["counterexample"].update(result="holds"),
            ["hypotheses_unwitnessed"],
            "",
        ),
        probe_case(
            "probe_other_statement",
            lambda p: p["result"]["request"].update(statement="True"),
            ["hypotheses_unwitnessed"],
            "",
        ),
        probe_case(
            "probe_other_input",
            lambda p: p["result"]["artifacts"]["files"]["input"].update(sha256="0" * 64),
            ["hypotheses_unwitnessed"],
            "",
        ),
        m(
            "watchdog_fired",
            with_harness(timed_out=True),
            ["harness_timeout"],
            "a proved result, after the kill",
        ),
        stub("stub_hang", "hang.sh", 2, ["harness_timeout", "result_unreadable"], "killed by the watchdog"),
        stub("stub_segv", "segv.sh", 30, ["harness_crash", "result_unreadable"], ""),
        stub("stub_killed", "killed.sh", 30, ["harness_killed", "result_unreadable"], "as by the OOM killer"),
        stub("stub_garbage", "garbage.sh", 30, ["result_unreadable"], ""),
        stub("stub_empty", "empty.sh", 30, ["result_unreadable"], "exit 0, no output"),
        stub("stub_proved_exit1", "proved_exit1.sh", 30, ["exit_mismatch"], "a proved result, exit 1"),
    ]


def denials_covered(cases: list[Case]) -> Outcome:
    """Every reason the gate can give is one some case has to get, so none of them is untested."""
    expected = {d for c in cases for d in c.expect.get("gate", [])}
    expected |= {d for s in static_cases() for d in s.expect.get("gate", [])}
    outcome = Outcome("denials_covered", "static", "gate", "pass", note=f"all {len(DENIALS)} reasons")
    missing = sorted(set(DENIALS) - expected)
    if missing:
        outcome.outcome = "fail"
        outcome.problems.append(f"no case expects {', '.join(missing)}")
    outcome.certified = False
    return outcome


def run_static(item: Static, ctx: StaticContext) -> Outcome:
    outcome = Outcome(item.id, "static", "gate", "fail", note=item.note)
    envelope, expected = item.run(ctx)
    outcome.denials = gate(envelope, expected, ctx.v)
    result = envelope.get("result") if isinstance(envelope, dict) else None
    judge(outcome, item.expect, result)
    return outcome


# Fixture


def write_fixture(live: Live) -> int:
    """Runs the two controls the static tier reads and stores their results, with machine paths taken out."""
    for name, path in ((FIXTURE_CASE, FIXTURE), (PROBE_CASE, PROBE_FIXTURE)):
        case = load_case(CASES / name)
        outcome = run_live(case, live)
        if not outcome.certified:
            print(outcome.line())
            return 1
        envelope = json.loads((live.out / "cases" / case.id / "envelope.json").read_text())
        stored = (
            {"result": envelope["result"], "probe": envelope["probe"]}
            if path == PROBE_FIXTURE
            else envelope["result"]
        )
        text = json.dumps(stored, indent=2, ensure_ascii=False) + "\n"
        text = text.replace(str(live.out), "<run>").replace(str(ROOT), "<repo>")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        print(f"wrote {path.relative_to(ROOT)}")
    return 0


# Main


def prune_runs() -> None:
    """Keeps the last few runs this made under build/, as tools/verify.py does with its own."""
    if not RUNS.is_dir():
        return
    runs = sorted((p for p in RUNS.iterdir() if p.is_dir() and p.name[:8].isdigit()), key=lambda p: p.name)
    for old in runs[: max(0, len(runs) - RUNS_KEPT + 1)]:
        shutil.rmtree(old, ignore_errors=True)


def blocked() -> list[Outcome]:
    data = json.loads((CORPUS / "blocked.json").read_text())
    return [
        Outcome(c["id"], "-", "integration", "blocked", note="blocked on " + "; ".join(c["blocked_on"]))
        for c in data["cases"]
    ]


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--tier", choices=["static", "live", "all"], default="all")
    parser.add_argument("--tool", type=Path, default=ROOT / "build" / "ir-lean")
    parser.add_argument("--only", nargs="*", default=None)
    parser.add_argument("--out", type=Path, help="a new directory for this run. Default: under build/")
    parser.add_argument("--case-timeout", type=float, default=120, help="seconds per check, at most")
    parser.add_argument("--case-memory-mb", type=int, default=4000, help="Lean's memory per check, at most")
    parser.add_argument(
        "--min-available-mb", type=int, default=6000, help="don't start a live case with less memory free"
    )
    parser.add_argument("--list", action="store_true", help="list the cases and exit")
    parser.add_argument("--write-fixture", action="store_true", help="rerun the control and store its result")
    args = parser.parse_args()

    try:
        cases = load_cases(args.only)
    except ManifestError as error:
        print(f"manifest error: {error}", file=sys.stderr)
        return 2
    statics = [s for s in static_cases() if not args.only or s.id in args.only]
    if args.list:
        for case in cases:
            print(f"live    {case.id}: {case.manifest['summary']}")
        for s in statics:
            print(f"static  {s.id}: {s.note}")
        for b in blocked():
            print(f"blocked {b.id}: {b.note}")
        return 0

    if args.out is None:
        prune_runs()
    stamp = f"{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}-{os.getpid()}"
    out = args.out or RUNS / stamp
    if out.exists() and any(out.iterdir()):
        print(f"{out} isn't empty", file=sys.stderr)
        return 2
    out.mkdir(parents=True, exist_ok=True)
    out = out.resolve()
    v = load_verify()
    tool = args.tool.resolve()
    outcomes: list[Outcome] = []

    if args.tier in ("live", "all") or args.write_fixture:
        missing = live_prerequisites(tool, v)
        live = None
        if not missing:
            live = Live(
                v,
                tool,
                out,
                current_versions(v, tool),
                args.case_timeout,
                args.case_memory_mb,
                args.min_available_mb,
            )
        if args.write_fixture:
            if live is None:
                print(f"can't run the control: missing {'; '.join(missing)}", file=sys.stderr)
                return 3
            return write_fixture(live)
        for case in cases:
            if live is None:
                outcome = Outcome(case.id, "live", case.manifest["category"], "not_run")
                outcome.note = "missing " + "; ".join(missing)
            else:
                outcome = run_live(case, live)
            print(outcome.line(), flush=True)
            outcomes.append(outcome)

    if args.tier in ("static", "all"):
        ctx = StaticContext(v, out, load_case(CASES / FIXTURE_CASE))
        for item in statics:
            outcome = run_static(item, ctx)
            print(outcome.line(), flush=True)
            outcomes.append(outcome)

    if not args.only:
        outcomes.append(denials_covered(cases))
        print(outcomes[-1].line())
        for outcome in blocked():
            print(outcome.line())
            outcomes.append(outcome)

    counts = {k: sum(o.outcome == k for o in outcomes) for k in ("pass", "fail", "not_run", "blocked")}
    certified = [o.id for o in outcomes if o.certified and o.outcome != "blocked"]
    report = {
        "schema": REPORT_SCHEMA,
        "counts": counts,
        "certified": certified,
        "cases": [o.__dict__ for o in outcomes],
    }
    (out / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(
        f"\n{counts['pass']} as expected, {counts['fail']} not, {counts['not_run']} not run, "
        f"{counts['blocked']} blocked. Certified: {', '.join(certified) or 'none'}."
    )
    print(f"Report: {out / 'report.json'}")
    if counts["fail"]:
        return 1
    return 3 if counts["not_run"] else 0


if __name__ == "__main__":
    sys.exit(main())
