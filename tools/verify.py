#!/usr/bin/env python3
"""Checks one claim about one function in LLVM IR, and answers with a JSON result an agent can act on.

The answer's `status` is one of five, and only `proved` says the claim holds:

  proved          a kernel-checked theorem, about the function ir-lean generated from this IR, resting only on
                  the axioms tests/check_axioms.lean allows, and replayed by leanchecker. The proof's own code
                  runs only while Lean compiles it: everything after reads it as data
  counterexample  concrete inputs on which Lean, running the model's compiled code, finds the claim false
  unsupported     the emitter refuses the function, or no witness could be evaluated
  timeout         a time, memory, heartbeat, recursion or stack limit stopped it before a verdict
  error           no verdict: the request, a tool, or the proof failed, or nothing was proved or refuted

`reason` is a stable code saying which case it is. docs/verify.md has the contract, what each result rests on,
and a worked example. Run `tools/verify.py capabilities` for the same, as JSON.

usage: tools/verify.py check REQUEST.json [--tool PATH] [--work-dir DIR] [--pretty]
       tools/verify.py check --ir FILE.ll | --c FILE.c  --function NAME
                             (--proof FILE.lean --theorem NAME | --statement TEXT) [options]
       tools/verify.py capabilities [--pretty]

The exit code is 0 for proved, 2 for counterexample, 3 for unsupported, 4 for timeout, and 1 for error.
"""

import argparse
import contextlib
import hashlib
import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, NoReturn

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
DYLIB = (
    ROOT / ".lake" / "build" / "lib" / f"libir_x2dlean_IRLean.{'dylib' if sys.platform == 'darwin' else 'so'}"
)
CHECK_TEMPLATE = ROOT / "tools" / "verify_check.lean"
DEFAULT_TOOL = ROOT / "build" / "ir-lean"
RUNS = ROOT / "build" / "verify"
# Runs kept under build/verify when no --work-dir is given. An explicit one is never deleted.
RUNS_KEPT = 20

SCHEMA = "ir-lean.verify/1"
REQUEST_SCHEMA = "ir-lean.verify.request/1"
DEFAULT_TIMEOUT = 600
DEFAULT_MEMORY_MB = 4000
# What tests/proofs.sh compiles proof targets with, after PROOF_CFLAGS. The emitter refuses `tbaa`.
DEFAULT_CFLAGS = ["-O2", "-fno-strict-aliasing"]

STATUSES = {
    "proved": "The claim is a kernel-checked theorem about the generated function. Read `claim.statement` "
    "and "
    "`assumptions` for what that does and doesn't say",
    "counterexample": "On the inputs in `counterexample`, the model's compiled code says the claim is false",
    "unsupported": "The emitter refuses the function, or no witness could be evaluated. Nothing was decided",
    "timeout": "A resource limit stopped it before a verdict. `limit` says which. More may help",
    "error": "No verdict. The request, a tool or the proof failed, or nothing was proved or refuted",
}
EXIT_CODES = {"proved": 0, "error": 1, "counterexample": 2, "unsupported": 3, "timeout": 4}

# Every reason, and the status it gives. A new one goes at the end of its status, and keeps its meaning.
REASONS: dict[str, tuple[str, str]] = {
    "kernel_checked": ("proved", "Every check passed"),
    "witness_falsifies": ("counterexample", "A witness makes the claim false"),
    "function_unsupported": ("unsupported", "The emitter left the function out, for the reason given"),
    "witness_unsupported": ("unsupported", "No witness could be decided, and nothing else settled the claim"),
    "time_limit": ("timeout", "`limits.timeout_seconds` ran out"),
    "memory_limit": ("timeout", "Lean ran past `limits.memory_mb`"),
    "heartbeat_limit": ("timeout", "Lean ran out of heartbeats: `maxHeartbeats` in the proof"),
    "recursion_limit": ("timeout", "Lean hit `maxRecDepth`"),
    "stack_limit": ("timeout", "Lean ran out of stack"),
    "solver_limit": ("timeout", "`bv_decide`'s SAT solver ran out of time: its `timeout` in the proof"),
    "step_limit": ("timeout", "`simp` ran out of steps: its `maxSteps` in the proof"),
    "invalid_request": ("error", "The request is malformed. `detail` says how"),
    "input_not_found": ("error", "A file the request names doesn't exist"),
    "toolchain_missing": ("error", "ir-lean, Lean, the IRLean library, clang or leanchecker isn't there"),
    "tool_failed": ("error", "A tool crashed or answered in a way this doesn't understand"),
    "compile_failed": ("error", "clang couldn't compile the C input"),
    "ir_invalid": ("error", "LLVM couldn't read the IR"),
    "function_not_found": ("error", "The module has no such function"),
    "generated_module_failed": ("error", "Lean rejected what ir-lean generated, which is a bug in ir-lean"),
    "support_failed": ("error", "A support module didn't compile"),
    "proof_failed": ("error", "The proof didn't check. `diagnostics` has Lean's errors"),
    "artifacts_modified": ("error", "A checked file changed while Lean ran the proof's code"),
    "theorem_not_found": ("error", "The proof module has no such declaration"),
    "not_a_theorem": ("error", "The declaration isn't a theorem of a proposition"),
    "statement_invalid": ("error", "The given statement doesn't elaborate"),
    "statement_not_about_target": ("error", "The statement doesn't name the generated function itself"),
    "statement_mismatch": ("error", "The theorem doesn't state what `statement` pinned"),
    "disallowed_axiom": ("error", "The theorem or module rests on an axiom outside the allowed ones"),
    "kernel_replay_failed": ("error", "leanchecker's replay through the kernel rejected a declaration"),
    "evaluation_contradicts_proof": ("error", "The kernel accepted the proof, and compiled code refutes it"),
    "not_proved": (
        "error",
        "Nothing was proved: no proof was given, and no witness made the statement false",
    ),
    "internal_error": ("error", "A bug in this tool"),
}

# In order. `proved` needs every one of REQUIRED to pass, and none of the others to fail.
CHECKS: list[tuple[str, str]] = [
    ("request", "The request is well formed"),
    ("toolchain", "The tools it needs are there"),
    ("inputs", "The files it names exist, and are copied and hashed"),
    ("compile_c", "clang compiled the C input to IR, if the input is C"),
    ("ir_valid", "LLVM's verifier accepts the IR, which ir-lean doesn't run itself"),
    ("translate", "ir-lean translated the function"),
    ("generate", "ir-lean wrote the Lean module"),
    ("compile_generated", "Lean checked the generated module"),
    ("compile_support", "Lean checked each support module"),
    ("compile_proof", "Lean checked the proof"),
    ("claim", "Lean read the theorem and the statement"),
    ("theorem", "The theorem exists in the proof module, and is a theorem of a proposition"),
    ("mentions_target", "The statement names the function from the generated module"),
    ("statement", "The theorem states exactly what `statement` pinned, if it was given"),
    ("axioms", "Every axiom in the proof and support modules is one tests/check_axioms.lean allows"),
    ("kernel_replay", "leanchecker replays the generated, support and proof modules through the kernel"),
    (
        "artifacts_unchanged",
        "The IR, generated module and library are as they were before the proof's code ran",
    ),
    ("witnesses", "Witnesses were decided by running the model's compiled code"),
]
REQUIRED = [
    "request",
    "toolchain",
    "inputs",
    "ir_valid",
    "translate",
    "generate",
    "compile_generated",
    "compile_proof",
    "claim",
    "theorem",
    "mentions_target",
    "axioms",
    "kernel_replay",
    "artifacts_unchanged",
]
# Checks that never stand in the way of a proof unless they fail outright.
OPTIONAL = {"compile_c", "compile_support", "statement", "witnesses"}

REQUEST_FIELDS = {
    "schema": f'Optional. "{REQUEST_SCHEMA}"',
    "input": 'Required. {"ir": PATH} for .ll or .bc, or {"c": PATH, "cflags": [...]}',
    "function": "Required. The LLVM name of the function, without @",
    "namespace": "Optional. The Lean namespace and module the proof imports. Defaults to the input's name",
    "proof": "Optional. A Lean file with the theorem",
    "theorem": "With `proof`. The theorem's name, or its last components",
    "support": "Optional. Lean files the proof imports, compiled in this order",
    "lean_root": "Optional. The directory module names of `proof` and `support` are relative to",
    "statement": "Optional. A Lean proposition. Pins the theorem, or stands alone with witnesses",
    "witnesses": 'Optional. A list of {"binder": "Lean term"}, or "#0", "#1", ... for binders by position',
    "limits": '{"timeout_seconds": 600, "memory_mb": 4000} by default',
}

# Module names Lean, its libraries or this repo already use, which a request can't take.
TAKEN_MODULES = {"Init", "Lean", "Std", "Lake", "IRLean", "LeanChecker", "LeanExport", "LeanIR", "Leanc"}
LEAN_KEYWORDS = set(
    "abbrev axiom by calc class def deriving do else end example export extends for fun have if import in "
    "inductive infix instance let local macro match mutual namespace notation open partial prefix private "
    "protected section set_option show structure syntax then theorem universe variable where with".split()
)
IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_]*")
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*")

LEAN_MESSAGE = re.compile(
    r"^(?P<file>.+?):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning|info)(?:\([^)]*\))?: (?P<text>.*)$"
)
LIMITS = [
    ("memory_limit", re.compile(r"excessive memory consumption|out of memory", re.I)),
    ("heartbeat_limit", re.compile(r"maximum number of heartbeats|\(deterministic\) timeout")),
    ("recursion_limit", re.compile(r"maximum recursion depth has been reached")),
    ("stack_limit", re.compile(r"deep recursion was detected|stack overflow", re.I)),
    ("solver_limit", re.compile(r"SAT solver timed out")),
    ("step_limit", re.compile(r"maximum number of steps exceeded")),
]
BV_COUNTEREXAMPLE = re.compile(r"found a (potentially spurious )?counterexample", re.I)
BV_ASSIGNMENT = re.compile(r"^\s*([^\s=]+) = (\S.*?)\s*$")

TRUNCATE = 4000
DIAGNOSTICS_KEPT = 50


class Stop(Exception):
    """Ends a run early, with a reason from REASONS."""

    def __init__(self, reason: str, detail: str, check: str | None = None) -> None:
        super().__init__(detail)
        self.reason = reason
        self.detail = detail
        self.check = check


@dataclass
class Ran:
    argv: list[str]
    returncode: int
    stdout: str
    stderr: str
    seconds: float
    timed_out: bool

    @property
    def output(self) -> str:
        return self.stdout + self.stderr


@dataclass
class Run:
    """Everything a run finds out, from which the result is built."""

    request: dict[str, Any]
    work: Path
    tool: Path
    deadline: float
    started: float
    checks: dict[str, dict[str, Any]] = field(
        default_factory=lambda: {name: {"name": name, "result": "not_run"} for name, _ in CHECKS}
    )
    commands: list[dict[str, Any]] = field(default_factory=list)
    diagnostics: list[dict[str, Any]] = field(default_factory=list)
    artifacts: dict[str, Any] = field(default_factory=dict)
    versions: dict[str, str] = field(default_factory=dict)
    target: dict[str, Any] = field(default_factory=dict)
    scope: dict[str, Any] = field(default_factory=dict)
    claim: dict[str, Any] = field(default_factory=dict)
    witnesses: list[dict[str, Any]] = field(default_factory=list)
    candidates: list[dict[str, Any]] = field(default_factory=list)
    path_map: dict[str, str] = field(default_factory=dict)
    stop: Stop | None = None
    proof_failure: str | None = None
    check_template: str = ""
    target_ir: str = ""
    input_path: Path = Path()
    # Hashes from before the proof's code ran, compared at the end.
    before: dict[str, str] | None = None

    def check(self, name: str, result: str, detail: Any = None, seconds: float | None = None) -> None:
        entry = self.checks[name]
        entry["result"] = result
        if detail is not None:
            entry["detail"] = detail
        if seconds is not None:
            entry["seconds"] = round(seconds, 2)

    def diagnose(self, severity: str, source: str, text: str, **where: Any) -> None:
        if len(self.diagnostics) < DIAGNOSTICS_KEPT:
            self.diagnostics.append(
                {"severity": severity, "source": source, **where, "message": unmap(self, text)[:TRUNCATE]}
            )

    def remaining(self) -> float:
        return self.deadline - time.monotonic()

    def run(
        self,
        argv: list[str],
        env: dict[str, str] | None = None,
        stdin: str | None = None,
        step: str = "",
        cwd: Path = ROOT,
    ) -> Ran:
        """Runs a command in its own process group, within what's left of the time limit, and kills the whole
        group if that runs out, so nothing it started is left running."""
        remaining = self.remaining()
        if remaining <= 0:
            raise Stop("time_limit", f"the time limit ran out before {step or argv[0]}", step or None)
        started = time.monotonic()
        try:
            process = subprocess.Popen(
                argv,
                stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                cwd=cwd,
                env=env,
                start_new_session=True,
            )
        except FileNotFoundError as error:
            raise Stop("toolchain_missing", f"can't run {argv[0]}: {error}", step or None) from error
        except PermissionError as error:
            raise Stop("toolchain_missing", f"can't run {argv[0]}: {error}", step or None) from error
        timed_out = False
        try:
            stdout, stderr = process.communicate(stdin, timeout=remaining)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_group(process.pid)
            stdout, stderr = process.communicate()
        kill_group(process.pid)
        ran = Ran(argv, process.returncode, stdout or "", stderr or "", time.monotonic() - started, timed_out)
        self.commands.append(
            {
                "step": step,
                "argv": argv,
                "cwd": str(cwd),
                "env": {k: v for k, v in (env or {}).items() if k in ("LEAN_PATH", "IRLEAN_VERIFY_CONFIG")},
                "exit": ran.returncode,
                "seconds": round(ran.seconds, 2),
                "timed_out": timed_out,
            }
        )
        return ran


def kill_group(pid: int) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(pid, signal.SIGKILL)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unmap(run: Run, text: str) -> str:
    """Names the requester's files instead of the copies Lean read."""
    for copy, original in run.path_map.items():
        text = text.replace(copy, original)
    return text


def lean_messages(run: Run, output: str, source: str) -> list[dict[str, Any]]:
    """Lean's errors and warnings, each with the lines that continue it."""
    messages: list[dict[str, Any]] = []
    for line in output.splitlines():
        m = LEAN_MESSAGE.match(line)
        if m:
            messages.append(
                {
                    "severity": m["severity"],
                    "source": source,
                    "file": unmap(run, m["file"]),
                    "line": int(m["line"]),
                    "column": int(m["column"]),
                    "message": m["text"],
                }
            )
        elif messages and line.strip():
            messages[-1]["message"] += "\n" + line
    for message in messages:
        message["message"] = unmap(run, message["message"])[:TRUNCATE]
    return [m for m in messages if m["severity"] != "info"]


def limit_of(text: str) -> str | None:
    for reason, pattern in LIMITS:
        if pattern.search(text):
            return reason
    return None


def classify_lean(ran: Ran, messages: list[dict[str, Any]]) -> str | None:
    """The resource limit a failed Lean run hit first, if it hit one before any other error. What fails
    after a limit often fails because of it, as later declarations lose what they need, so only the first
    error says whether more resources could help."""
    if ran.timed_out:
        return "time_limit"
    errors = [m for m in messages if m["severity"] == "error"]
    if errors:
        return limit_of(errors[0]["message"])
    return limit_of(ran.output)


# Requests


def fail_request(detail: str) -> Stop:
    return Stop("invalid_request", detail, "request")


def load_request(raw: Any, base: Path) -> dict[str, Any]:
    """Checks a request and makes its paths absolute. Anything it doesn't know is an error, so a misspelled
    field can't be ignored quietly."""
    if not isinstance(raw, dict):
        raise fail_request("the request must be a JSON object")
    unknown = sorted(set(raw) - set(REQUEST_FIELDS))
    if unknown:
        raise fail_request(f"unknown fields: {', '.join(unknown)}. Known: {', '.join(REQUEST_FIELDS)}")
    if raw.get("schema", REQUEST_SCHEMA) != REQUEST_SCHEMA:
        raise fail_request(f"schema must be {REQUEST_SCHEMA!r}, not {raw.get('schema')!r}")

    def path(value: Any, what: str) -> str:
        if not isinstance(value, str) or not value:
            raise fail_request(f"{what} must be a path")
        return str((base / value).resolve())

    source = raw.get("input")
    if not isinstance(source, dict) or len({"ir", "c"} & set(source)) != 1:
        raise fail_request('input must be {"ir": PATH} or {"c": PATH, "cflags": [...]}')
    extra = set(source) - {"ir", "c", "cflags"} - ({"cflags"} if "c" in source else set())
    if extra or ("ir" in source and "cflags" in source):
        raise fail_request(f"input can't have {', '.join(sorted(extra | ({'cflags'} & set(source))))}")
    request: dict[str, Any] = {"schema": REQUEST_SCHEMA}
    if "ir" in source:
        request["input"] = {"ir": path(source["ir"], "input.ir")}
    else:
        cflags = source.get("cflags", None)
        if cflags is not None and (
            not isinstance(cflags, list) or not all(isinstance(f, str) for f in cflags)
        ):
            raise fail_request("input.cflags must be a list of strings")
        request["input"] = {"c": path(source["c"], "input.c"), "cflags": cflags}

    function = raw.get("function")
    if not isinstance(function, str) or not function.strip().lstrip("@"):
        raise fail_request("function must be the LLVM name of a function")
    request["function"] = function.strip().lstrip("@")

    stem = Path(next(iter(request["input"].values()))).stem
    namespace = raw.get("namespace", default_namespace(stem))
    if not isinstance(namespace, str) or not IDENTIFIER.fullmatch(namespace):
        raise fail_request(f"namespace must be a Lean identifier, such as Real, not {namespace!r}")
    if namespace in TAKEN_MODULES or namespace in LEAN_KEYWORDS:
        raise fail_request(f"namespace {namespace!r} is taken by Lean or this repo")
    request["namespace"] = namespace

    proof, statement = raw.get("proof"), raw.get("statement")
    if proof is None and statement is None:
        raise fail_request("give a proof and a theorem, or a statement to refute with witnesses, or both")
    if proof is not None:
        request["proof"] = path(proof, "proof")
        theorem = raw.get("theorem")
        if not isinstance(theorem, str) or not theorem.strip():
            raise fail_request("theorem must name the theorem in proof")
        request["theorem"] = theorem.strip()
    elif "theorem" in raw:
        raise fail_request("theorem needs a proof")
    if statement is not None:
        if not isinstance(statement, str) or not statement.strip():
            raise fail_request("statement must be a Lean proposition")
        request["statement"] = statement.strip()

    support = raw.get("support", [])
    if not isinstance(support, list):
        raise fail_request("support must be a list of paths")
    if support and proof is None:
        raise fail_request("support needs a proof")
    request["support"] = [path(s, "support") for s in support]
    if "lean_root" in raw:
        request["lean_root"] = path(raw["lean_root"], "lean_root")
    elif proof is not None:
        request["lean_root"] = str(Path(request["proof"]).parent)

    witnesses = raw.get("witnesses", [])
    if not isinstance(witnesses, list) or not all(
        isinstance(w, dict) and w and all(isinstance(k, str) and isinstance(v, str) for k, v in w.items())
        for w in witnesses
    ):
        raise fail_request('witnesses must be a list of non-empty {"binder": "Lean term"} objects')
    request["witnesses"] = witnesses

    limits = raw.get("limits", {})
    if not isinstance(limits, dict) or set(limits) - {"timeout_seconds", "memory_mb"}:
        raise fail_request("limits can only have timeout_seconds and memory_mb")
    timeout, memory = (
        limits.get("timeout_seconds", DEFAULT_TIMEOUT),
        limits.get("memory_mb", DEFAULT_MEMORY_MB),
    )
    if not isinstance(timeout, int | float) or isinstance(timeout, bool) or not 1 <= timeout <= 86400:
        raise fail_request("limits.timeout_seconds must be between 1 and 86400")
    if not isinstance(memory, int) or isinstance(memory, bool) or not 64 <= memory <= 1048576:
        raise fail_request("limits.memory_mb must be a whole number between 64 and 1048576")
    request["limits"] = {"timeout_seconds": timeout, "memory_mb": memory}
    return request


def default_namespace(stem: str) -> str:
    """What ir-lean would pick, for the name a proof imports."""
    name = "".join(c if c.isalnum() else "_" for c in stem)
    if not name or not name[0].isalpha() or name in TAKEN_MODULES or name in LEAN_KEYWORDS:
        name = "M" + name
    return name


def module_name(path: Path, root: Path, what: str) -> str:
    try:
        relative = path.relative_to(root)
    except ValueError as error:
        raise fail_request(f"{what} {path} isn't under lean_root {root}") from error
    if relative.suffix != ".lean":
        raise fail_request(f"{what} {path} isn't a .lean file")
    name = ".".join(relative.with_suffix("").parts)
    if not MODULE_NAME.fullmatch(name):
        raise fail_request(
            f"{what} {path} gives module name {name!r}, which must look like Proof or Spec.Adler"
        )
    if name.split(".")[0] in TAKEN_MODULES:
        raise fail_request(f"{what} {path} would be module {name}, which Lean or this repo already has")
    return name


# Steps


def preflight(run: Run) -> None:
    request = run.request
    missing = []
    if not os.access(run.tool, os.X_OK):
        missing.append(f"ir-lean at {run.tool}: build it with cmake and ninja")
    if not (LIBRARY / "IRLean.olean").exists():
        missing.append(f"the IRLean library in {LIBRARY}: run `lake build`")
    for program in ["lean", "opt"] + (["clang"] if "c" in request["input"] else []):
        if shutil.which(program) is None:
            missing.append(f"{program} on PATH: run this inside `nix develop`")
    if "proof" in request and shutil.which("leanchecker") is None:
        missing.append("leanchecker on PATH: it comes with Lean, inside `nix develop`")
    if request["witnesses"] and not DYLIB.exists():
        missing.append(f"{DYLIB}: run `lake build`")
    if missing:
        raise Stop("toolchain_missing", "missing " + "; ".join(missing), "toolchain")
    run.check("toolchain", "pass")


def copy_inputs(run: Run) -> None:
    """Copies every input into the run's directory, so the run can be repeated from there, and hashes it."""
    request = run.request
    inputs = run.work / "inputs"
    lean_dir = run.work / "lean"
    inputs.mkdir(parents=True)
    lean_dir.mkdir()
    files: dict[str, Any] = {}

    def take(path_text: str, role: str, destination: Path) -> Path:
        path = Path(path_text)
        if not path.is_file():
            raise Stop("input_not_found", f"{role} {path} doesn't exist or isn't a file", "inputs")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        run.path_map[str(destination)] = str(path)
        files[role] = {"original": str(path), "copy": str(destination), "sha256": sha256(destination)}
        return destination

    source = request["input"].get("ir") or request["input"]["c"]
    run.input_path = take(source, "input", inputs / Path(source).name)
    if "proof" in request:
        root = Path(request["lean_root"])
        names = [module_name(Path(s), root, "support") for s in request["support"]]
        name = module_name(Path(request["proof"]), root, "proof")
        every = [request["namespace"], *names, name]
        if len(set(every)) != len(every):
            raise fail_request(f"a module name is used twice in {every}: rename a file or the namespace")
        for i, (support, module) in enumerate(zip(request["support"], names, strict=True)):
            take(support, f"support[{i}]", module_path(run, module, ".lean"))
        take(request["proof"], "proof", module_path(run, name, ".lean"))
        run.artifacts["proof_module"] = name
        run.artifacts["support_modules"] = names
    run.artifacts["files"] = files
    run.check("inputs", "pass", {role: f["sha256"] for role, f in files.items()})


def module_path(run: Run, module: str, suffix: str) -> Path:
    return (run.work / "lean" / Path(*module.split("."))).with_suffix(suffix)


def compile_c(run: Run) -> Path:
    request = run.request
    source = run.input_path
    if "c" not in request["input"]:
        run.check("compile_c", "skip")
        return source
    proof_cflags = os.environ.get("PROOF_CFLAGS", "").split()
    cflags = request["input"]["cflags"]
    flags = [*proof_cflags, *(DEFAULT_CFLAGS if cflags is None else cflags)]
    ll = run.work / f"{request['namespace']}.ll"
    # From the source's directory, by its bare name, so the IR names no directory, and a replay makes the same
    # bytes.
    argv = ["clang", *flags, "-S", "-emit-llvm", "-fno-discard-value-names", "-o", str(ll), source.name]
    ran = run.run(argv, step="compile_c", cwd=source.parent)
    run.versions["clang"] = first_line(run, ["clang", "--version"])
    if ran.timed_out:
        raise Stop("time_limit", "clang didn't finish in time", "compile_c")
    if ran.returncode != 0:
        run.diagnose("error", "clang", ran.stderr)
        reason = "compile_failed" if ran.returncode > 0 else "tool_failed"
        raise Stop(reason, f"clang exited with {ran.returncode}", "compile_c")
    run.check(
        "compile_c",
        "pass",
        {"flags": flags, "proof_cflags_from_shell": bool(proof_cflags)},
        ran.seconds,
    )
    if not proof_cflags:
        run.diagnose(
            "warning",
            "verify",
            "PROOF_CFLAGS isn't set, so clang compiled for this host, not the pinned target",
        )
    run.artifacts["ir"] = {"path": str(ll), "sha256": sha256(ll)}
    return ll


def verify_ir(run: Run, ll: Path) -> None:
    """ir-lean reads IR without LLVM's verifier, which clang's output always passes and hand-written or
    generated IR may not. What the verifier rejects has no meaning to translate."""
    ran = run.run(["opt", "-passes=verify", "-disable-output", str(ll)], step="ir_valid")
    if ran.timed_out:
        raise Stop("time_limit", "opt didn't finish in time", "ir_valid")
    if ran.returncode < 0:
        raise Stop("tool_failed", f"opt died with signal {-ran.returncode}", "ir_valid")
    if ran.returncode != 0:
        run.diagnose("error", "opt", ran.output)
        raise Stop(
            "ir_invalid",
            f"LLVM's verifier rejects the IR: {unmap(run, ran.output.strip())[:500]}",
            "ir_valid",
        )
    run.check("ir_valid", "pass", seconds=ran.seconds)


def translate(run: Run, ll: Path) -> None:
    """Asks ir-lean what it can translate, and stops if it isn't the function."""
    ran = run.run([str(run.tool), str(ll), "--report"], step="translate")
    if ran.timed_out:
        raise Stop("time_limit", "ir-lean --report didn't finish in time", "translate")
    if ran.returncode == 1 and re.search(r":\d+:\d+: error: ", ran.stderr):
        run.diagnose("error", "ir-lean", ran.stderr)
        raise Stop(
            "ir_invalid", f"ir-lean couldn't read the IR: {unmap(run, ran.stderr.strip())[:500]}", "translate"
        )
    if ran.returncode != 0:
        run.diagnose("error", "ir-lean", ran.output or f"exit {ran.returncode}")
        raise Stop("tool_failed", f"ir-lean --report exited with {ran.returncode}", "translate")
    functions: dict[str, dict[str, Any]] = {}
    for line in ran.stdout.splitlines():
        parts = line.split("\t")
        if parts[0] == "ok" and len(parts) == 7:
            functions[parts[1]] = {
                "lean_name": parts[2],
                "signature": parts[3],
                "blocks": int(parts[4]),
                "instructions": int(parts[5]),
                "uses_memory": parts[6] == "memory",
            }
        elif parts[0] == "unsupported" and len(parts) == 3:
            functions[parts[1]] = {"unsupported": parts[2]}
        elif not re.fullmatch(r"translated \d+/\d+", line):
            raise Stop(
                "tool_failed",
                f"ir-lean --report printed a line this doesn't understand: {line!r}",
                "translate",
            )
    left_out = {name: f["unsupported"] for name, f in functions.items() if "unsupported" in f}
    run.scope["functions_in_module"] = len(functions)
    run.scope["left_out"] = left_out
    name = run.request["function"]
    if name not in functions:
        known = ", ".join(sorted(functions)[:20]) or "none"
        raise Stop("function_not_found", f"the module has no function @{name}. It has: {known}", "translate")
    found = functions[name]
    if "unsupported" in found:
        run.target = {"function": name, "unsupported": found["unsupported"]}
        raise Stop("function_unsupported", f"ir-lean leaves out @{name}: {found['unsupported']}", "translate")
    run.target = {
        "function": name,
        "lean_constant": f"{run.request['namespace']}.{found['lean_name']}",
        **found,
    }
    run.check("translate", "pass", {"left_out_elsewhere": len(left_out)}, ran.seconds)
    if left_out:
        run.diagnose(
            "info",
            "ir-lean",
            f"{len(left_out)} other function(s) left out, which @{name} doesn't call: "
            + ", ".join(f"@{n}" for n in sorted(left_out)[:10]),
        )


def ir_facts(run: Run, ll: Path) -> None:
    """What the IR says about its target, and the promises the model trusts instead of checking."""
    text = None
    if ll.suffix == ".ll":
        text = ll.read_text(errors="replace")
    elif shutil.which("llvm-dis"):
        ran = run.run(["llvm-dis", "-o", "-", str(ll)], step="ir_facts")
        text = ran.stdout if ran.returncode == 0 else None
    if text is None:
        run.target.update({"triple": None, "datalayout": None})
        return
    triple = re.search(r'^target triple = "([^"]*)"', text, re.M)
    layout = re.search(r'^target datalayout = "([^"]*)"', text, re.M)
    run.target["triple"] = triple[1] if triple else None
    run.target["datalayout"] = layout[1] if layout else None
    name = re.escape(run.request["function"])
    body = re.search(rf'^define [^\n]*@(?:{name}|"{name}")\(([^\n]*)\n(.*?)^}}', text, re.M | re.S)
    trusted: set[str] = set()
    if body:
        header = body[1]
        groups = set(re.findall(r"#(\d+)", header))
        words = set(header.split())
        for group in groups:
            attributes = re.search(rf"^attributes #{group} = {{([^\n]*)}}", text, re.M)
            if attributes:
                words |= set(attributes[1].split())
        trusted |= {w for w in ("mustprogress", "willreturn") if w in words}
        if "!llvm.loop" in body[2] and "llvm.loop.mustprogress" in text:
            trusted.add("llvm.loop.mustprogress")
    run.target["trusted_promises"] = sorted(trusted)


def generate(run: Run, ll: Path) -> Path:
    namespace = run.request["namespace"]
    lean = run.work / "lean" / f"{namespace}.lean"
    # Witnesses run compiled code, so the module needs code then. Otherwise it checks faster without.
    no_code = [] if run.request["witnesses"] or run.request.get("statement") else ["--no-code"]
    ran = run.run(
        [str(run.tool), str(ll), "--namespace", namespace, "-o", str(lean), *no_code], step="generate"
    )
    if ran.timed_out:
        raise Stop("time_limit", "ir-lean didn't finish in time", "generate")
    if ran.returncode not in (0, 3) or not lean.exists():
        run.diagnose("error", "ir-lean", ran.output or f"exit {ran.returncode}")
        raise Stop("tool_failed", f"ir-lean exited with {ran.returncode}", "generate")
    run.check("generate", "pass", {"code": not no_code}, ran.seconds)
    run.artifacts["generated"] = {"path": str(lean), "sha256": sha256(lean), "code": not no_code}
    return lean


def link_library(run: Run) -> None:
    """IRLean alone, for LEAN_PATH. The repo's other libraries are built next to it, and leanchecker checks
    every module there whose name starts with one it's given: the repo's own `Real.popcount`, for `Real`."""
    library = run.work / "library"
    library.mkdir()
    for entry in LIBRARY.iterdir():
        if entry.name == "IRLean" or entry.name.startswith("IRLean."):
            (library / entry.name).symlink_to(entry)


def lean_env(run: Run) -> dict[str, str]:
    return {**os.environ, "LEAN_PATH": f"{run.work / 'lean'}{os.pathsep}{run.work / 'library'}"}


def lean_argv(run: Run, *args: str) -> list[str]:
    # As tests/llvm.py runs it: a memory limit, and 64 MB thread stacks so bv_decide's fork doesn't run out.
    return ["lean", "-M", str(run.request["limits"]["memory_mb"]), "-s", "65536", *args]


def compile_module(run: Run, source: Path, check: str, failure: str) -> bool:
    """Compiles one module next to its source. Returns whether it compiled, stopping the run if it didn't
    and `failure` isn't `proof_failed`."""
    olean = source.with_suffix(".olean")
    ran = run.run(
        lean_argv(run, "-R", str(run.work / "lean"), "-o", str(olean), str(source)), lean_env(run), step=check
    )
    messages = lean_messages(run, ran.output, "lean")
    for message in messages:
        if len(run.diagnostics) < DIAGNOSTICS_KEPT:
            run.diagnostics.append(message)
    if ran.returncode == 0 and not ran.timed_out and olean.exists():
        return True
    limit = classify_lean(ran, messages)
    detail = f"lean exited with {ran.returncode} on {unmap(run, str(source))}"
    if not messages and not limit and ran.output.strip():
        run.diagnose("error", "lean", ran.output)
    if failure == "proof_failed":
        run.check(check, "fail", detail, ran.seconds)
        run.proof_failure = limit or (
            "tool_failed" if ran.returncode < 0 and not messages else "proof_failed"
        )
        candidates_from(run, messages)
        return False
    if limit:
        raise Stop(limit, f"{detail}: {limit.replace('_', ' ')}", check)
    if ran.returncode < 0 and not messages:
        raise Stop(
            "tool_failed", f"lean died with signal {-ran.returncode} on {unmap(run, str(source))}", check
        )
    raise Stop(failure, detail, check)


def candidates_from(run: Run, messages: list[dict[str, Any]]) -> None:
    """Assignments bv_decide printed when it found a counterexample to some goal. They only count once they
    make the claim itself false."""
    for message in messages:
        if message["severity"] != "error" or not BV_COUNTEREXAMPLE.search(message["message"]):
            continue
        assignment = {}
        for line in message["message"].splitlines()[1:]:
            m = BV_ASSIGNMENT.match(line)
            if m:
                assignment[m[1]] = m[2]
        if assignment:
            run.candidates.append(
                {
                    "assignment": assignment,
                    "line": message.get("line"),
                    "possibly_spurious": "spurious" in message["message"],
                }
            )


def snapshot(run: Run) -> dict[str, str]:
    """Hashes of the files the checks trust, which the proof's code could change while Lean compiles it."""
    paths = [Path(run.target_ir), Path(run.artifacts["generated"]["path"])]
    paths += [Path(run.artifacts["generated"]["path"]).with_suffix(".olean")]
    paths += sorted(LIBRARY.glob("IRLean*.olean")) + sorted((LIBRARY / "IRLean").glob("*.olean"))
    if run.request["witnesses"]:
        paths.append(DYLIB)
    return {str(p): sha256(p) if p.exists() else "missing" for p in paths}


def library_hash() -> str:
    digest = hashlib.sha256()
    for path in sorted(LIBRARY.glob("IRLean*.olean")) + sorted((LIBRARY / "IRLean").glob("*.olean")):
        digest.update(path.name.encode() + b"\0" + path.read_bytes())
    return digest.hexdigest()


def run_check_file(
    run: Run, mode: str, witnesses: list[list[list[str]]], source: str
) -> tuple[Ran, list[Any]]:
    """Runs tools/verify_check.lean in one mode, and returns the answers it printed with this run's nonce. It
    imports nothing of the proof's, so none of the proof's code runs: it reads the proof's modules as data."""
    request = run.request
    nonce = secrets.token_hex(16)
    imports = ["Lean", "IRLean", request["namespace"]]
    proof_compiled = run.checks["compile_proof"]["result"] == "pass"
    modules = [*run.artifacts["support_modules"], run.artifacts["proof_module"]] if proof_compiled else []
    directory = run.work / "check"
    directory.mkdir(exist_ok=True)
    lean = directory / f"{mode.capitalize()}.lean"
    header = "".join(f"import {m}\n" for m in imports) + f"open IRLean {request['namespace']}\n\n"
    lean.write_text(header + run.check_template)
    config = directory / f"{mode}.json"
    config.write_text(
        json.dumps(
            {
                "nonce": nonce,
                "mode": mode,
                "target": run.target["lean_constant"],
                "generated": request["namespace"],
                "modules": modules,
                "proof_module": run.artifacts.get("proof_module") if proof_compiled else None,
                "theorem": request.get("theorem") if proof_compiled else None,
                "statement": request.get("statement"),
                "witness_source": source,
                "witnesses": witnesses,
            },
            ensure_ascii=False,
        )
    )
    env = {**lean_env(run), "IRLEAN_VERIFY_CONFIG": str(config)}
    native = []
    if mode == "witness":
        # A panic in compiled code returns a default value and carries on, which could pass for an answer.
        env["LEAN_ABORT_ON_PANIC"] = "1"
        native = [f"--load-dynlib={DYLIB}", "-Dinterpreter.prefer_native=true"]
    ran = run.run(lean_argv(run, *native, str(lean)), env, step=f"claim:{mode}")
    marker = f"IRLEAN_VERIFY {nonce} "
    answers = []
    for line in ran.stdout.splitlines():
        if line.startswith(marker):
            try:
                answers.append(json.loads(line[len(marker) :]))
            except json.JSONDecodeError as error:
                raise Stop(
                    "internal_error", f"tools/verify_check.lean printed bad JSON: {error}", "claim"
                ) from error
    return ran, answers


def check_claim(run: Run) -> None:
    """Reads the theorem and the statement in Lean, and decides the checks that depend only on them."""
    request = run.request
    ran, answers = run_check_file(run, "check", [], "none")
    checks = [a for a in answers if a.get("kind") == "check"]
    if len(checks) != 1:
        messages = lean_messages(run, ran.output, "lean")
        limit = classify_lean(ran, messages)
        if limit:
            raise Stop(limit, f"reading the claim hit a limit: {limit.replace('_', ' ')}", "claim")
        run.diagnose("error", "verify", ran.output or f"exit {ran.returncode}")
        raise Stop("internal_error", "tools/verify_check.lean gave no answer", "claim")
    answer = checks[0]
    if not answer.get("ok"):
        raise Stop("internal_error", f"tools/verify_check.lean: {answer.get('error')}", "claim")
    run.check("claim", "pass", seconds=ran.seconds)
    theorem, statement = answer.get("theorem"), answer.get("statement")
    run.claim = {"theorem": theorem, "statement": statement, "axiom_policy": answer.get("axiom_policy")}

    if statement is not None and not statement.get("elaborated"):
        run.check("statement", "fail", statement.get("error"))
    if "proof" in request and run.checks["compile_proof"]["result"] == "pass":
        if not theorem or not theorem.get("found"):
            run.check("theorem", "fail", (theorem or {}).get("error", "not found"))
        elif theorem["kind"] != "theorem" or not theorem["is_prop"]:
            run.check(
                "theorem", "fail", f"{theorem['name']} is a {theorem['kind']}, not a theorem of a proposition"
            )
        else:
            run.check("theorem", "pass", theorem["name"])
            run.check(
                "mentions_target",
                "pass" if theorem["mentions_target"] else "fail",
                {
                    "target": run.target["lean_constant"],
                    "generated_constants": theorem["generated_constants"],
                },
            )
            if statement is not None and statement.get("elaborated"):
                matched = statement.get("match")
                run.check("statement", "fail" if matched == "mismatch" else "pass", {"match": matched})
    if "statement" not in request:
        run.check("statement", "skip")
    elif "proof" not in request and statement.get("elaborated"):
        run.check("statement", "pass", "elaborated")
        run.check(
            "mentions_target",
            "pass" if statement["mentions_target"] else "fail",
            {"target": run.target["lean_constant"], "generated_constants": statement["generated_constants"]},
        )


def check_axioms(run: Run) -> None:
    """tests/check_axioms.lean's policy on every module the proof brought, as tools/verify_check.lean
    applied it without running their code. It reran each bv_decide axiom with the toolchain's checker."""
    policy = run.claim.get("axiom_policy") or {}
    if not policy.get("ok"):
        run.check("axioms", "fail", unmap(run, str(policy.get("error", "no answer")))[:TRUNCATE])
        return
    theorem = run.claim.get("theorem") or {}
    run.check(
        "axioms",
        "pass",
        {"bv_decide_rechecked": policy.get("bv_decide"), "theorem": theorem.get("axioms", [])},
    )


def kernel_replay(run: Run) -> None:
    """Replays each module's declarations through the kernel. Lean code in a proof can add a declaration
    without the kernel checking it, with `debug.skipKernelTC`, and nothing else here would notice."""
    modules = [run.request["namespace"], *run.artifacts["support_modules"], run.artifacts["proof_module"]]
    ran = run.run(["leanchecker", *modules], lean_env(run), step="kernel_replay")
    if ran.timed_out:
        raise Stop("time_limit", "leanchecker didn't finish in time", "kernel_replay")
    if ran.returncode != 0:
        run.diagnose("error", "leanchecker", ran.output or f"exit {ran.returncode}")
        limit = limit_of(ran.output)
        if limit:
            raise Stop(limit, f"leanchecker hit a limit: {limit.replace('_', ' ')}", "kernel_replay")
        run.check("kernel_replay", "fail", unmap(run, ran.output.strip())[:TRUNCATE], ran.seconds)
        return
    run.check("kernel_replay", "pass", {"modules": modules}, ran.seconds)


def evaluate_witnesses(run: Run) -> None:
    """Decides the claim at each witness by running compiled code. Only a witness Lean finds false counts as
    a counterexample, and only against a statement that names the target."""
    request = run.request
    theorem, statement = run.claim.get("theorem"), run.claim.get("statement")
    if statement and statement.get("elaborated"):
        source, described = "statement", statement
    elif run.checks["theorem"]["result"] == "pass" and theorem:
        source, described = "theorem", theorem
    else:
        source, described = None, None
    witnesses: list[dict[str, Any]] = [{"source": "request", "assignment": w} for w in request["witnesses"]]
    for candidate in run.candidates:
        witnesses.append(
            {
                "source": "bv_decide",
                "assignment": candidate["assignment"],
                "possibly_spurious": candidate["possibly_spurious"],
            }
        )
    if not witnesses:
        run.check("witnesses", "skip")
        return
    if source is None or described is None or not described.get("mentions_target"):
        why = "no statement that names the target to evaluate them against"
        for w in witnesses:
            w.update({"result": "unsupported", "error": why})
        run.witnesses = witnesses
        run.check("witnesses", "inconclusive", why)
        return
    pairs = [[[k, v] for k, v in w["assignment"].items()] for w in witnesses]
    try:
        ran, answers = run_check_file(run, "witness", pairs, source)
    except Stop as stop:
        if stop.reason != "time_limit":
            raise
        # No time was left to start. That's the same as running out partway: the witnesses time out, and
        # whatever the proof showed stands.
        ran, answers = Ran([], -9, "", "", 0.0, True), []
    results = {a["index"]: a for a in answers if a.get("kind") == "witness"}
    started = any(a.get("kind") == "witness_start" for a in answers)
    trouble = next((a["error"] for a in answers if a.get("kind") == "witness_error"), None)
    for i, w in enumerate(witnesses):
        w["against"] = source
        if i in results:
            w["result"] = results[i]["result"]
            for key in ("instance", "error"):
                if key in results[i]:
                    w[key] = unmap(run, results[i][key])[:TRUNCATE]
        elif ran.timed_out:
            w["result"] = "timeout"
            w["error"] = (
                "evaluation didn't finish within the time limit, which is what a run that never ends does"
            )
        elif trouble:
            w["result"] = "unsupported"
            w["error"] = unmap(run, trouble)[:TRUNCATE]
        else:
            w["result"] = "aborted"
            w["error"] = f"evaluation stopped with exit {ran.returncode} before this witness"
            limit = limit_of(ran.output)
            if limit:
                w["result"] = "timeout"
                w["error"] = f"evaluation hit a limit: {limit.replace('_', ' ')}"
    if not started and not ran.timed_out and not trouble:
        run.diagnose("error", "lean", ran.output or f"exit {ran.returncode}")
    run.witnesses = witnesses
    outcomes = {w["result"] for w in witnesses}
    if "fails" in outcomes:
        run.check("witnesses", "fail", "a witness makes the statement false", ran.seconds)
    elif outcomes == {"holds"}:
        run.check("witnesses", "pass", f"all {len(witnesses)} hold", ran.seconds)
    else:
        run.check("witnesses", "inconclusive", sorted(outcomes), ran.seconds)


def first_line(run: Run, argv: list[str]) -> str:
    try:
        ran = run.run(argv, step="versions")
    except Stop:
        return "unknown"
    return (ran.output.strip().splitlines() or ["unknown"])[0]


def emitter_commit() -> str:
    try:
        commit = subprocess.run(
            ["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
        ).stdout.strip()
        dirty = subprocess.run(
            [
                "git",
                "-C",
                str(ROOT),
                "status",
                "--porcelain",
                "src",
                "IRLean",
                "tools",
            ],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"
    return commit + (" with local changes" if dirty else "")


# Results


def decide(run: Run) -> tuple[str, str, str]:
    """The status, reason and a one-line detail, in this order of precedence:

    1. A checked file that changed while the proof's code ran makes everything after it suspect.
    2. A run that stopped early answers with why it stopped.
    3. A witness that makes the claim false is a counterexample, unless the proof passed every check for
       that same statement, when one of the two is wrong and neither can be reported.
    4. With a proof, the first check it failed. `proved` only comes after every required check passed.
    5. With only a statement, nothing can be proved: whatever the witnesses showed, short of a refutation.
    """
    if run.checks["artifacts_unchanged"]["result"] == "fail":
        return "error", "artifacts_modified", f"changed: {run.checks['artifacts_unchanged'].get('detail')}"
    if run.stop is not None:
        return REASONS[run.stop.reason][0], run.stop.reason, run.stop.detail
    has_proof = "proof" in run.request
    falsified = [w for w in run.witnesses if w.get("result") == "fails"]
    if falsified:
        proof_stands = has_proof and all(run.checks[c]["result"] == "pass" for c in REQUIRED)
        if proof_stands and run.checks["statement"]["result"] in ("pass", "skip"):
            return (
                "error",
                "evaluation_contradicts_proof",
                "the kernel accepted the proof, but compiled code finds the statement false at "
                f"{falsified[0]['assignment']}. Lean's compiler, an implemented_by or extern, or the kernel "
                "is wrong",
            )
        return (
            "counterexample",
            "witness_falsifies",
            f"the statement is false at {falsified[0]['assignment']}",
        )

    if has_proof:
        if run.proof_failure:
            reason = run.proof_failure
            return REASONS[reason][0], reason, str(run.checks["compile_proof"].get("detail", ""))
        statement = run.claim.get("statement") or {}
        theorem = run.claim.get("theorem") or {}
        gates = [
            ("theorem", "theorem_not_found" if not theorem.get("found") else "not_a_theorem"),
            ("mentions_target", "statement_not_about_target"),
            (
                "statement",
                "statement_invalid" if statement.get("elaborated") is False else "statement_mismatch",
            ),
            ("axioms", "disallowed_axiom"),
            ("kernel_replay", "kernel_replay_failed"),
        ]
        for check, reason in gates:
            if run.checks[check]["result"] == "fail":
                return "error", reason, str(run.checks[check].get("detail", ""))
        unmet = [c for c in REQUIRED if run.checks[c]["result"] != "pass"]
        broken = [c for c in OPTIONAL if run.checks[c]["result"] == "fail"]
        if unmet or broken:
            return "error", "internal_error", f"checks didn't pass: {', '.join(unmet + broken)}"
        return "proved", "kernel_checked", f"{theorem['name']} is a kernel-checked theorem"

    statement = run.claim.get("statement") or {}
    if not statement.get("elaborated"):
        return "error", "statement_invalid", str(statement.get("error", "the statement didn't elaborate"))
    if not statement.get("mentions_target"):
        return "error", "statement_not_about_target", f"it doesn't name {run.target.get('lean_constant')}"
    outcomes = [w.get("result") for w in run.witnesses]
    if "timeout" in outcomes:
        return (
            "timeout",
            "time_limit",
            "evaluating a witness didn't finish, and none made the statement false",
        )
    if outcomes and all(o == "unsupported" for o in outcomes):
        return "unsupported", "witness_unsupported", "no witness could be decided"
    return "error", "not_proved", "no proof was given, and no witness made the statement false"


def assumptions(run: Run, status: str) -> list[dict[str, Any]]:
    """What the answer rests on that it doesn't check, each with where to read about it."""
    request, target = run.request, run.target
    if "input" not in request:
        return []
    found = (run.claim.get("theorem") or {}) if "proof" in request else (run.claim.get("statement") or {})
    out: list[dict[str, Any]] = []

    def add(key: str, text: str, ref: str) -> None:
        out.append({"id": key, "text": text, "see": ref})

    add(
        "scope.modeled_ir",
        "The claim is about the function as this LLVM IR, in IRLean's semantics. Not the source program, not "
        "machine code, and only as faithful as the model",
        "docs/trust.md#what-a-theorem-covers",
    )
    if target.get("triple") or target.get("datalayout"):
        add(
            "scope.target",
            f"Only for target {target.get('triple')} and data layout {target.get('datalayout')}",
            "docs/design.md#targets-and-machine-independence",
        )
    if "c" in request["input"]:
        add(
            "scope.front_end",
            "The IR is clang's output for these flags. Undefined behavior clang used before the IR existed "
            "isn't covered",
            "docs/trust.md#what-a-theorem-covers",
        )
    add(
        "trusted.pipeline",
        "Trusted, unverified: LLVM's IR parser, the emitter, IRLean's semantics, and the Lean kernel",
        "docs/trust.md#trust-boundaries",
    )
    if status == "proved":
        bv = [a for a in found.get("axioms", []) if "bv_decide" in a]
        if bv:
            add(
                "trusted.bv_decide",
                f"{len(bv)} axiom(s) from bv_decide, each rechecked by running the toolchain's bv_decide "
                "checker on the formula and certificate the proof recorded, which trusts Lean's compiled "
                "code for that checker",
                "docs/trust.md#trust-boundaries",
            )
        if "statement" not in request:
            add(
                "statement.unpinned",
                "No statement was pinned, so a person has to read claim.statement to know it says what's "
                "wanted",
                "docs/verify.md#pinning-a-statement",
            )
    hypotheses = [b for b in found.get("binders", []) if b.get("hypothesis")]
    if hypotheses:
        add(
            "statement.hypotheses",
            "Only for inputs meeting: " + "; ".join(f"{h['name']} : {h['type']}" for h in hypotheses),
            "docs/verify.md#reading-a-result",
        )
    shape = found.get("shape")
    if shape and shape not in ("returns_ok", "exists_returns_ok"):
        add(
            "statement.shape",
            "The conclusion isn't `target ... = Outcome.ok _`, so it may allow undefined behavior, a model "
            "stop or a run that never ends. Read it",
            "docs/trust.md#what-the-model-does-at-its-edges",
        )
    promises = target.get("trusted_promises") or []
    if promises:
        effect = (
            "A theorem of this shape rules out spinning, so it isn't affected"
            if shape in ("returns_ok", "exists_returns_ok")
            else "A claim that allows `none` has a hole there"
        )
        add(
            "llvm.mustprogress",
            f"The IR has {', '.join(promises)}, which the model trusts: where LLVM calls spinning undefined, "
            f"the model says `none`. {effect}",
            "docs/trust.md#known-gaps-in-the-model",
        )
    if target.get("uses_memory"):
        add(
            "memory.model",
            "The function uses memory. Theorems hold for every Mem, whose oracles choose addresses and "
            "whether malloc fails, and layout hypotheses in the statement are assumptions. Stack never "
            "overflows",
            "docs/trust.md#known-gaps-in-the-model",
        )
    if "proof" in request:
        add(
            "process.no_sandbox",
            "Lean runs the proof's own code while compiling it, unsandboxed. The checks after read the proof "
            "as data, and the files they rely on are hashed before that code runs, but files elsewhere could "
            "change",
            "docs/verify.md#what-proved-rests-on",
        )
    if status == "counterexample":
        add(
            "evidence.compiled",
            "The counterexample was found by running Lean's compiled code for the model, the trust of "
            "native_decide, not by the kernel",
            "docs/verify.md#counterexamples",
        )
    return out


def assert_contract(result: dict[str, Any]) -> None:
    """The promises every result keeps. Breaking one is a bug here, so it turns the result into an error."""
    status, reason = result["status"], result["reason"]
    checks = {c["name"]: c["result"] for c in result["checks"]}
    problems = []
    if status not in STATUSES or reason not in REASONS or REASONS[reason][0] != status:
        problems.append(f"{status}/{reason} isn't in the contract")
    if result["exit_code"] != EXIT_CODES.get(status):
        problems.append("the exit code doesn't match the status")
    if status == "proved":
        if "proof" not in result["request"]:
            problems.append("proved without a proof")
        problems += [f"proved with {c} {checks[c]}" for c in REQUIRED if checks.get(c) != "pass"]
        problems += [f"proved with {c} failed" for c in OPTIONAL if checks.get(c) == "fail"]
        if result.get("counterexample") is not None:
            problems.append("proved with a counterexample")
    if status == "counterexample":
        counterexample = result.get("counterexample") or {}
        if counterexample.get("result") != "fails":
            problems.append("counterexample without a witness that fails")
    if problems:
        raise AssertionError("; ".join(problems))


def build_result(run: Run) -> dict[str, Any]:
    status, reason, detail = decide(run)
    falsified = next((w for w in run.witnesses if w.get("result") == "fails"), None)
    theorem = run.claim.get("theorem") if "proof" in run.request else None
    statement = run.claim.get("statement")
    claim: dict[str, Any] = {
        "theorem": run.request.get("theorem"),
        "resolved": (theorem or {}).get("name"),
        "statement": (theorem or {}).get("statement") or (statement or {}).get("statement"),
        "pinned": run.request.get("statement"),
        "pin_match": (statement or {}).get("match"),
    }
    source = theorem if theorem and theorem.get("found") else statement
    if status == "counterexample" and falsified and falsified.get("against") == "statement":
        # What was refuted is the pinned statement, which needn't be the theorem.
        source = statement
        claim["statement"] = (statement or {}).get("statement")
    for key in ("binders", "conclusion", "shape", "generated_constants", "mentions_target", "axioms"):
        if source and key in source:
            claim[key] = source[key]
    limit = reason if status == "timeout" else None
    result: dict[str, Any] = {
        "schema": SCHEMA,
        "status": status,
        "reason": reason,
        "detail": unmap(run, detail)[:TRUNCATE],
        "meaning": STATUSES[status],
        "exit_code": EXIT_CODES[status],
        "limit": limit,
        "request": run.request,
        "target": run.target,
        "claim": claim,
        "counterexample": None,
        "witnesses": run.witnesses,
        "assumptions": assumptions(run, status),
        "scope": run.scope,
        "checks": [run.checks[name] for name, _ in CHECKS],
        "diagnostics": run.diagnostics,
        "artifacts": run.artifacts,
        "versions": run.versions,
        "reproduce": {
            "request": str(run.work / "request.json"),
            "command": [str(ROOT / "tools" / "verify.py"), "check", str(run.work / "request.json")],
            "commands": run.commands,
        },
        "seconds": round(time.monotonic() - run.started, 2),
    }
    if status == "counterexample" and falsified:
        result["counterexample"] = {
            **falsified,
            "evidence": "compiled_evaluation",
            "trust": "Lean's compiler and runtime, as for native_decide. Not checked by the kernel",
        }
    try:
        assert_contract(result)
    except AssertionError as error:
        result.update(
            status="error",
            reason="internal_error",
            detail=f"the result broke its own contract: {error}",
            meaning=STATUSES["error"],
            exit_code=EXIT_CODES["error"],
            limit=None,
            counterexample=None,
        )
    return result


def prune_runs() -> None:
    try:
        runs = sorted(
            (p for p in RUNS.iterdir() if p.is_dir() and re.fullmatch(r"[0-9a-f]{12}-\d+", p.name)),
            key=lambda p: p.stat().st_mtime,
            reverse=True,
        )
    except OSError:
        return
    for old in runs[RUNS_KEPT:]:
        shutil.rmtree(old, ignore_errors=True)


def verify(raw: Any, base: Path, tool: Path = DEFAULT_TOOL, work: Path | None = None) -> dict[str, Any]:
    """Checks a request, from a dict as in a request file with paths relative to `base`, and returns the
    result. This is the API: `tools/verify.py check` is a thin layer over it."""
    started = time.monotonic()
    try:
        request = load_request(raw, base)
    except Stop as stop:
        return invalid_result(stop.detail, raw)
    digest = hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest()[:12]
    if work is None:
        RUNS.mkdir(parents=True, exist_ok=True)
        prune_runs()
        work = RUNS / f"{digest}-{time.time_ns()}"
    work = work.resolve()
    deadline = started + request["limits"]["timeout_seconds"]
    run = Run(request, work, tool.resolve(), deadline, started)
    run.check("request", "pass")
    try:
        if work.exists() and any(work.iterdir()):
            raise fail_request(f"work directory {work} isn't empty")
        work.mkdir(parents=True, exist_ok=True)
        run.check_template = CHECK_TEMPLATE.read_text()
        preflight(run)
        link_library(run)
        copy_inputs(run)
        replay = json.loads(json.dumps(request))
        replay["input"] = {
            **replay["input"],
            next(iter(replay["input"])): run.artifacts["files"]["input"]["copy"],
        }
        if "proof" in request:
            replay["proof"] = run.artifacts["files"]["proof"]["copy"]
            replay["support"] = [
                run.artifacts["files"][f"support[{i}]"]["copy"] for i in range(len(request["support"]))
            ]
            replay["lean_root"] = str(work / "lean")
        (work / "request.json").write_text(json.dumps(replay, indent=2, ensure_ascii=False) + "\n")
        run.versions.update(
            {
                "lean": first_line(run, ["lean", "--version"]),
                "ir_lean": emitter_commit(),
                "ir_lean_binary_sha256": sha256(run.tool),
                "irlean_library_sha256": library_hash(),
            }
        )
        ll = compile_c(run)
        run.target_ir = str(ll)
        verify_ir(run, ll)
        translate(run, ll)
        ir_facts(run, ll)
        generated = generate(run, ll)
        if compile_module(run, generated, "compile_generated", "generated_module_failed"):
            run.check("compile_generated", "pass")
            run.artifacts["generated"]["olean_sha256"] = sha256(generated.with_suffix(".olean"))
        # Before any of the proof's code runs, as it does while Lean compiles the support modules and proof.
        run.before = snapshot(run)
        if "proof" in request:
            for name in run.artifacts["support_modules"]:
                compile_module(run, module_path(run, name, ".lean"), "compile_support", "support_failed")
            run.check("compile_support", "pass" if request["support"] else "skip")
            proof = module_path(run, run.artifacts["proof_module"], ".lean")
            if compile_module(run, proof, "compile_proof", "proof_failed"):
                run.check("compile_proof", "pass")
        else:
            for name in ("compile_support", "compile_proof", "theorem", "axioms", "kernel_replay"):
                run.check(name, "skip")
        if "statement" in request or run.checks["compile_proof"]["result"] == "pass":
            check_claim(run)
        if "proof" in request and run.checks["compile_proof"]["result"] == "pass":
            check_axioms(run)
            kernel_replay(run)
        evaluate_witnesses(run)
    except Stop as stop:
        run.stop = stop
        if stop.check and stop.check in run.checks:
            run.check(stop.check, "fail", stop.detail)
    except Exception as error:  # Any bug here has to come back as an error, never as a pass.
        run.stop = Stop("internal_error", f"{type(error).__name__}: {error}")
    finally:
        if run.before is not None:
            after = snapshot(run)
            changed = sorted(p for p, h in run.before.items() if after.get(p) != h)
            run.check(
                "artifacts_unchanged",
                "fail" if changed else "pass",
                {"changed": changed} if changed else None,
            )
    result = build_result(run)
    with contextlib.suppress(OSError):
        (work / "result.json").write_text(
            json.dumps(result, indent=2, ensure_ascii=False, default=str) + "\n"
        )
    return result


def invalid_result(detail: str, raw: Any) -> dict[str, Any]:
    """The answer to a request too malformed to start."""
    started = time.monotonic()
    request = {
        "invalid": raw
        if isinstance(raw, dict | list | str | int | float | bool) or raw is None
        else repr(raw)
    }
    run = Run(request, Path(), Path(), started, started)
    run.check("request", "fail", detail)
    run.stop = Stop("invalid_request", detail, "request")
    result = build_result(run)
    result["reproduce"] = None
    return result


def capabilities() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "request_schema": REQUEST_SCHEMA,
        "statuses": STATUSES,
        "exit_codes": EXIT_CODES,
        "reasons": {code: {"status": s, "meaning": m} for code, (s, m) in REASONS.items()},
        "checks": [{"name": n, "meaning": m, "required_for_proved": n in REQUIRED} for n, m in CHECKS],
        "request_fields": REQUEST_FIELDS,
        "defaults": {
            "timeout_seconds": DEFAULT_TIMEOUT,
            "memory_mb": DEFAULT_MEMORY_MB,
            "cflags": DEFAULT_CFLAGS,
        },
        "scope": {
            "claims": "One theorem or statement about one function in LLVM IR, in IRLean's semantics",
            "modeled": "Integers, pointers, structs, vectors of integers, memory, globals, function "
            "pointers, recursion, and malloc, free and strlen. See docs/design.md#what-the-model-covers",
            "refused": "Floating point, atomics, volatile, exceptions, variadics, most external calls, tbaa "
            "and the other metadata and promises in docs/trust.md#known-gaps-in-the-model. A refused "
            "function comes back unsupported, with ir-lean's reason",
            "counterexamples": "A witness for every binder that isn't a hypothesis, and a statement Lean can "
            "decide: in practice functions without memory, whose results have DecidableEq. A run that never "
            "ends shows up as a timeout, never as a counterexample",
        },
    }


class ArgumentError(Exception):
    pass


class Parser(argparse.ArgumentParser):
    """Raises on bad arguments, where argparse would exit with 2, which means counterexample here."""

    def error(self, message: str) -> NoReturn:
        raise ArgumentError(message)


def main(argv: list[str] | None = None) -> int:
    parser = Parser(
        prog="tools/verify.py", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="command", required=True)
    caps = sub.add_parser("capabilities", help="print the contract as JSON")
    caps.add_argument("--pretty", action="store_true")
    check = sub.add_parser("check", help="check one claim")
    check.add_argument("request_file", nargs="?", type=Path, help="a request as JSON")
    source = check.add_mutually_exclusive_group()
    source.add_argument("--ir", help="LLVM IR, .ll or .bc")
    source.add_argument("--c", help="C source, compiled with clang")
    check.add_argument("--cflags", help="flags for --c, as one string. Default: " + " ".join(DEFAULT_CFLAGS))
    check.add_argument("--function")
    check.add_argument("--namespace")
    check.add_argument("--proof")
    check.add_argument("--theorem")
    check.add_argument("--support", action="append", default=None)
    check.add_argument("--lean-root")
    check.add_argument("--statement")
    check.add_argument("--witness", action="append", default=None, help='JSON, such as {"x": "3#32"}')
    check.add_argument("--timeout", type=float)
    check.add_argument("--memory-mb", type=int)
    check.add_argument("--tool", type=Path, default=DEFAULT_TOOL, help="the ir-lean binary")
    check.add_argument("--work-dir", type=Path, help="an empty or new directory for the run. Kept")
    check.add_argument("--pretty", action="store_true")
    try:
        args = parser.parse_args(argv)
    except ArgumentError as error:
        result = invalid_result(f"bad arguments: {error}", None)
        print(json.dumps(result, ensure_ascii=False))
        return result["exit_code"]

    if args.command == "capabilities":
        print(json.dumps(capabilities(), indent=2 if args.pretty else None, ensure_ascii=False))
        return 0

    flags = [args.ir, args.c, args.function, args.namespace, args.proof, args.theorem, args.support]
    flags += [args.lean_root, args.statement, args.witness, args.timeout, args.memory_mb, args.cflags]
    raw: Any
    base = Path.cwd()
    if args.request_file is not None:
        if any(f is not None for f in flags):
            raw = "a request file and request flags together"
        else:
            base = args.request_file.resolve().parent
            try:
                raw = json.loads(args.request_file.read_text())
            except OSError as error:
                raw = f"can't read {args.request_file}: {error}"
            except json.JSONDecodeError as error:
                raw = f"{args.request_file} isn't JSON: {error}"
    else:
        raw = {}
        if args.ir is not None:
            raw["input"] = {"ir": args.ir}
        elif args.c is not None:
            raw["input"] = {
                "c": args.c,
                **({"cflags": args.cflags.split()} if args.cflags is not None else {}),
            }
        for key in ("function", "namespace", "proof", "theorem", "support", "lean_root", "statement"):
            if getattr(args, key) is not None:
                raw[key] = getattr(args, key)
        if args.witness:
            try:
                raw["witnesses"] = [json.loads(w) for w in args.witness]
            except json.JSONDecodeError as error:
                raw = f"--witness isn't JSON: {error}"
        if isinstance(raw, dict) and (args.timeout is not None or args.memory_mb is not None):
            raw["limits"] = {
                k: v
                for k, v in (("timeout_seconds", args.timeout), ("memory_mb", args.memory_mb))
                if v is not None
            }
    try:
        result = (
            invalid_result(raw, None) if isinstance(raw, str) else verify(raw, base, args.tool, args.work_dir)
        )
        text = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False)
    except Exception as error:  # Even a bug here answers in the contract, as an error.
        result = invalid_result(f"internal error: {type(error).__name__}: {error}", None)
        result.update(reason="internal_error", detail=f"{type(error).__name__}: {error}")
        text = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False, default=str)
    print(text)
    return result["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
