#!/usr/bin/env python3
"""Binds a certificate to what it's about, and checks that binding again from scratch.
docs/llvm-proof-binding.md has the contract, what a `bound` verdict establishes, what it doesn't, and what it
trusts.

A certificate is a Lean theorem about two functions ir-lean generated: the source, as LLVM's `opt` read an
input module, and the target, as one `opt -passes=SPEC` run left it. `record` writes a bundle: the input, both
IR files, both generated Lean modules, the certificate, and a manifest naming each by SHA-256, with the pinned
LLVM commit, the `opt` binary, the pass spec, the triple and data layout, and the toolchain that made them.
`verify` takes a manifest and believes none of it:

- every file is hashed again, and the toolchain on PATH has to be the one recorded, down to each binary's
  hash;
- `opt` is rerun on the input, and has to give both IR files byte for byte;
- ir-lean is rerun on both, and has to give both Lean modules byte for byte;
- Lean compiles them and the certificate in a fresh directory, from source, with no `.olean` from the bundle;
- tools/binding_check.lean builds the expected claim from the claim's kind and the two generated functions,
  and the certificate's theorem has to have exactly that type;
- tests/check_axioms.lean audits the axioms, and `leanchecker` replays the modules through the kernel;
- the IR, the generated modules, the library and these tools hash the same after the certificate's code ran.

It fails closed. Anything it doesn't recognise, can't check or can't finish is not `bound`:

  bound        0  every check passed. This is a per-instance certificate: one function, one input module, one
                  run of `opt` with this pass spec and triple. It says nothing about the pass on any other
                  input, or about its C++
  refused      1  the evidence doesn't match what it claims to be: a hash, the toolchain, a replay, or the
                  theorem's type
  unsupported  3  the claim kind can't be checked by any tool here (all inputs, the C++, or a pipeline),
                  or the model can't judge the function: the emitter refuses it, it uses memory, or the
                  target makes a promise IRLean trusts
  unknown      4  a time or memory limit stopped a step. More may help
  error        5  a tool failed in a way that says nothing about the evidence

Hashes establish identity, not correctness: two files hashing the same are the same file, whatever they mean.

usage: tools/binding.py record --input FILE.ll --passes SPEC [--mtriple T] --function NAME
                               --certificate FILE.lean --theorem NAME --namespace NS [--kind KIND] --out DIR
       tools/binding.py verify MANIFEST.json [--cache DIR] [--work DIR] [--keep] [--timeout S] [--memory MB]
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
import tomllib
from pathlib import Path
from typing import Any, NoReturn

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
TOOL = ROOT / "build" / "ir-lean"
CHECK = ROOT / "tools" / "binding_check.lean"
AXIOMS = ROOT / "tests" / "check_axioms.lean"
PIN = ROOT / "tests" / "llvm" / "targets.toml"
RUNS = ROOT / "build" / "binding" / "runs"

MANIFEST_SCHEMA = "ir-lean.binding.manifest/1"
VERDICT_SCHEMA = "ir-lean.binding.verdict/1"
EXIT = {"bound": 0, "refused": 1, "unsupported": 3, "unknown": 4, "error": 5}
DEFAULT_TIMEOUT = 300
DEFAULT_MEMORY_MB = 3000
# Lean's errors for running out of something, as tests/llvm.py and tests/proofs.sh list them.
LIMIT = re.compile(
    r"maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|"
    r"stack overflow|excessive memory|out of memory|SAT solver timed out|maximum number of steps",
    re.IGNORECASE,
)

# What each kind of claim says, as the Lean the checker builds. Only the first two can be checked: the others
# are the obligations a per-instance certificate leaves open, and are refused as `unsupported` whatever the
# evidence.
KINDS = {
    "ir_instance_equivalence": "Src.f = Tgt.f, and Src.f never stops the model: on every input, poison "
    "included, the two functions as ir-lean generated them have the same outcome in IRLean's semantics, "
    "and it's one the model knows LLVM gives",
    "ir_instance_refinement": "IRLean.Refines Src.f Tgt.f: on every input, the target only does what the "
    "source allows, in IRLean's semantics. Needs an IRLean with IRLean.Refines",
    "rewrite_all_inputs": "The pass's rewrite is correct on every input module it applies to (L3)",
    "pass_implementation": "The pass's compiled C++ makes only proved rewrites, for every input module (L4)",
    "pipeline_composition": "A pipeline of passes, at an optimization level and target, preserves meaning",
}
CHECKABLE = {"ir_instance_equivalence", "ir_instance_refinement"}

ESTABLISHES = [
    "The certificate's theorem has exactly the type the claim kind gives, about the two functions ir-lean "
    "generated, and the kernel accepts it, resting only on the axioms tests/check_axioms.lean allows",
    "The source IR is what this opt read from this input, and the target IR is what this opt -passes=SPEC "
    "made of it, with this triple and data layout",
    "The Lean the claim is about is what this ir-lean binary writes for that IR",
    "Every file and tool here is the one the manifest names, by SHA-256",
]
DOES_NOT_ESTABLISH = [
    "That the pass is correct on any other input module, or on this one under other options, or in a "
    "pipeline",
    "Anything about the pass's C++: one run of a binary built from it produced this output",
    "That the opt binary was built from the pinned llvm-project commit. Nix's derivation is trusted for that",
    "That IRLean's semantics are LLVM's, or that the emitter translates faithfully",
    "Anything about native code, other targets or other data layouts",
    "That a hash says anything about meaning. Equal hashes mean the same bytes",
]
TRUSTED = [
    "Lean's kernel, through leanchecker, and Lean's elaborator for building the expected claim",
    "tests/check_axioms.lean's policy: the standard three axioms, and bv_decide's, rechecked",
    "The ir-lean emitter, unverified, and IRLean's semantics (docs/trust.md)",
    "opt and LLVM's IR parser, for what they printed. Rerunning them shows they do it again, not that it's "
    "right",
    "Nix, for the opt binary coming from the pinned source, and SHA-256",
    "The certificate's own code runs while Lean compiles it, unsandboxed. Files it could change are rehashed "
    "after",
]
OBLIGATION = (
    "Implementation correspondence is open: no theorem here relates LLVM's C++ for any pass to the rewrites "
    "it makes. A bound verdict is translation validation of one run, not a proof of the optimizer"
)

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*")
NAMESPACE = re.compile(r"[A-Z][A-Za-z0-9_]*")
PASS_SPEC = re.compile(r"[A-Za-z0-9_<>;=,()\-]+")
TRIPLE = re.compile(r"[A-Za-z0-9_.\-]+")
SHA = re.compile(r"[0-9a-f]{64}")
# Files in a bundle, by role, and where record writes them. The manifest names each by path and hash.
ARTIFACTS = {
    "input": "input.ll",
    "src_ir": "src.ll",
    "tgt_ir": "tgt.ll",
    "src_lean": "Src.lean",
    "tgt_lean": "Tgt.lean",
    "certificate": "Cert.lean",
}


class Verdict(Exception):
    """Ends a check with a status and a reason."""

    def __init__(self, status: str, reason: str, detail: str, **extra: Any) -> None:
        super().__init__(detail)
        self.status, self.reason, self.detail, self.extra = status, reason, detail, extra


def refused(reason: str, detail: str, **extra: Any) -> NoReturn:
    raise Verdict("refused", reason, detail, **extra)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256(path.read_bytes())


def canonical(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def library_hash() -> str:
    """IRLean's .olean files, the same way tools/verify.py hashes them."""
    digest = hashlib.sha256()
    for path in sorted(LIBRARY.glob("IRLean*.olean")) + sorted((LIBRARY / "IRLean").glob("*.olean")):
        digest.update(path.name.encode() + b"\0" + path.read_bytes())
    return digest.hexdigest()


class Runner:
    """Runs one process at a time, under a time limit, Lean's own memory limit, and a cgroup capped at the
    same, with no swap, when systemd can make one."""

    def __init__(self, timeout: int, memory_mb: int) -> None:
        self.timeout, self.memory_mb = timeout, memory_mb
        self.capped = False
        if sys.platform.startswith("linux") and shutil.which("systemd-run"):
            probe = ["systemd-run", "--user", "--scope", "--quiet", "--", "true"]
            self.capped = subprocess.run(probe, capture_output=True, check=False).returncode == 0
        self.env = {**os.environ, "ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip()}

    def __call__(
        self,
        argv: list[str],
        stdin: bytes | None = None,
        env: dict[str, str] | None = None,
        cwd: Path | None = None,
    ) -> tuple[int, str, bytes]:
        """(exit code, stderr, stdout). Raises `unknown` if a limit stopped it."""
        command = argv
        unit = f"ir-lean-binding-{os.getpid()}-{secrets.token_hex(4)}"
        if self.capped:
            properties = [f"MemoryMax={self.memory_mb + 512}M", "MemorySwapMax=0"]
            command = [
                "systemd-run",
                "--user",
                "--scope",
                "--quiet",
                f"--unit={unit}",
                *(f"--property={p}" for p in properties),
                "--",
                *argv,
            ]
        # Its own process group, so a timeout stops what it started too, such as bv_decide's solver.
        p = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env={**self.env, **(env or {})},
            cwd=cwd,
            start_new_session=True,
        )
        try:
            out, raw_err = p.communicate(stdin if stdin is not None else b"", timeout=self.timeout)
        except subprocess.TimeoutExpired as e:
            if self.capped:
                subprocess.run(
                    ["systemctl", "--user", "kill", "--signal=SIGKILL", f"{unit}.scope"],
                    capture_output=True,
                    check=False,
                )
            with contextlib.suppress(ProcessLookupError):
                os.killpg(p.pid, signal.SIGKILL)
            p.kill()
            with contextlib.suppress(subprocess.TimeoutExpired):
                p.communicate(timeout=10)
            raise Verdict(
                "unknown", "time_limit", f"{Path(argv[0]).name} took more than {self.timeout} s"
            ) from e
        r = subprocess.CompletedProcess(command, p.returncode, out, raw_err)
        err = r.stderr.decode(errors="replace")
        # Lean prints its errors on stdout. A limit anywhere means the step might pass with more.
        said = err + r.stdout.decode(errors="replace")
        if r.returncode < 0 or r.returncode == 137 or (r.returncode != 0 and LIMIT.search(said)):
            raise Verdict("unknown", "resource_limit", f"{Path(argv[0]).name} hit a limit: {said[-400:]}")
        return r.returncode, err, r.stdout

    def lean(self, *args: str) -> list[str]:
        return ["lean", "-j1", "-M", str(self.memory_mb), "-s", "65536", *args]


def first_line(run: Runner, argv: list[str]) -> str:
    code, err, out = run(argv)
    if code != 0:
        raise Verdict("error", "toolchain_missing", f"{argv[0]} failed: {err[-300:]}")
    return out.decode().strip().splitlines()[0] if out.strip() else ""


def which(program: str) -> Path:
    found = shutil.which(program)
    if found is None:
        raise Verdict("error", "toolchain_missing", f"{program} isn't on PATH: run inside nix develop")
    return Path(found).resolve()


def toolchain(run: Runner) -> dict[str, str]:
    """Everything a verdict depends on that isn't in the bundle, by version and hash."""
    for path, what in [
        (TOOL, "build/ir-lean: build it with cmake and ninja"),
        (LIBRARY / "IRLean.olean", ".lake/build/lib/lean/IRLean.olean: run lake build"),
    ]:
        if not path.exists():
            raise Verdict("error", "toolchain_missing", f"missing {what}")
    prefix = Path(first_line(run, ["lean", "--print-prefix"]))
    lean_version = first_line(run, ["lean", "--version"])
    opt_lines = run(["opt", "--version"])[2].decode().splitlines()
    return {
        "lean_version": lean_version,
        "lean_sha256": sha256_file(prefix / "bin" / "lean"),
        "leanchecker_sha256": sha256_file(prefix / "bin" / "leanchecker"),
        "opt_version": next((x.strip() for x in opt_lines if "LLVM version" in x), ""),
        "opt_sha256": sha256_file(which("opt")),
        "ir_lean_sha256": sha256_file(TOOL),
        "irlean_library_sha256": library_hash(),
        "check_axioms_sha256": sha256_file(AXIOMS),
        "binding_check_sha256": sha256_file(CHECK),
        "binding_py_sha256": sha256_file(Path(__file__).resolve()),
    }


def llvm_pin() -> dict[str, str]:
    """The llvm-project commit this repo proves things about, from tests/llvm/targets.toml."""
    project = tomllib.loads(PIN.read_text())["project"]
    return {k: project[k] for k in ("repository", "tag", "commit", "nix_hash")}


def llvm_source_hash(run: Runner) -> str:
    """The NAR hash of the dev shell's llvm-project source, which Nix fetched for the pinned tag."""
    source = os.environ.get("LLVM_PROJECT_SRC")
    if not source:
        raise Verdict("error", "toolchain_missing", "LLVM_PROJECT_SRC isn't set: run inside nix develop")
    code, err, out = run(["nix", "hash", "path", source])
    if code != 0:
        raise Verdict("error", "toolchain_missing", f"nix can't hash {source}: {err[-300:]}")
    return out.decode().strip()


def ir_target(ll: str) -> dict[str, str | None]:
    triple = re.search(r'^target triple = "([^"]*)"', ll, re.M)
    layout = re.search(r'^target datalayout = "([^"]*)"', ll, re.M)
    return {"triple": triple.group(1) if triple else None, "datalayout": layout.group(1) if layout else None}


# Promises IRLean trusts instead of checking (docs/trust.md): a run the model says never ends is undefined in
# LLVM under one. A target with one could be undefined where the source spins, and the model can't see it.
TRUSTED_PROMISES = re.compile(r"\b(mustprogress|willreturn)\b")
DEFINE = re.compile(r'^define [^@]*@"?([^"(\s]+)"?\(.*?^}', re.M | re.S)


def changes_elsewhere(src: str, tgt: str, function: str) -> dict:
    """What the run changed that a claim about `function` doesn't cover: other functions, by name, and whether
    anything outside a function did, such as a global, a declaration or an attribute group."""
    a = {m.group(1): m.group(0) for m in DEFINE.finditer(src)}
    b = {m.group(1): m.group(0) for m in DEFINE.finditer(tgt)}
    outside = [
        [
            x
            for x in DEFINE.sub("", ll).splitlines()
            if x.strip() and not x.startswith(("; ModuleID", "source_"))
        ]
        for ll in (src, tgt)
    ]
    others = sorted(n for n in a.keys() | b.keys() if n != function and a.get(n) != b.get(n))
    return {"functions": others, "module_level": outside[0] != outside[1]}


def opt_argv(passes: str, mtriple: str | None) -> list[str]:
    """opt reads the input from stdin, so its output doesn't name a path."""
    return ["opt", "-S", f"-passes={passes}", "-", "-o", "-"] + ([f"-mtriple={mtriple}"] if mtriple else [])


def run_opt(run: Runner, input_ll: bytes, passes: str, mtriple: str | None) -> bytes:
    code, err, out = run(opt_argv(passes, mtriple), stdin=input_ll)
    if code != 0:
        refused("transform_replay_mismatch", f"opt -passes={passes} failed on the input: {err[-400:]}")
    return out


def translate(run: Runner, ll: Path, function: str, namespace: str, out: Path) -> list[str]:
    """Runs ir-lean on `ll`, writes the module to `out`, and returns its report on `function`: `ok`, the LLVM
    name, the Lean name, ..., and `pure` or `memory` last. Or `unsupported`, the name and why."""
    code, err, report = run([str(TOOL), str(ll), "--report"])
    if code not in (0, 3):
        raise Verdict("error", "tool_failed", f"ir-lean --report failed on {ll.name}: {err[-300:]}")
    rows = [line.split("\t") for line in report.decode().splitlines()]
    row = next((r for r in rows if len(r) >= 3 and r[1] == function), None)
    if row is None:
        refused("function_not_found", f"{ll.name} has no function {function}")
    out.parent.mkdir(parents=True, exist_ok=True)
    code, err, _ = run(
        [str(TOOL), str(ll), "--no-code", "--namespace", namespace, "-o", str(out)], cwd=ll.parent
    )
    if code not in (0, 3) or not out.exists():
        raise Verdict("error", "tool_failed", f"ir-lean failed on {ll.name}: {err[-300:]}")
    return row


# ------------------------------------------------------------------------------------------------------------
# record


def record(args: argparse.Namespace) -> int:
    """Writes a bundle. It checks nothing about the certificate: verify does, from the bundle alone."""
    run = Runner(args.timeout, args.memory)
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        sys.exit(f"{out} isn't empty")
    if args.kind not in KINDS:
        sys.exit(f"--kind is one of {sorted(KINDS)}")
    out.mkdir(parents=True, exist_ok=True)
    input_ll = args.input.read_bytes()
    (out / ARTIFACTS["input"]).write_bytes(input_ll)
    (out / ARTIFACTS["src_ir"]).write_bytes(run_opt(run, input_ll, "verify", args.mtriple))
    (out / ARTIFACTS["tgt_ir"]).write_bytes(run_opt(run, input_ll, args.passes, args.mtriple))
    lean_name = None
    for side, ir, lean in (("Src", "src_ir", "src_lean"), ("Tgt", "tgt_ir", "tgt_lean")):
        work = out / ".record" / side
        work.mkdir(parents=True)
        shutil.copy(out / ARTIFACTS[ir], work / ARTIFACTS[ir])
        row = translate(
            run, work / ARTIFACTS[ir], args.function, f"{args.namespace}.{side}", work / "out.lean"
        )
        # A function ir-lean leaves out has no Lean name. verify says it's unsupported.
        name = row[2] if row[0] == "ok" else args.function
        if lean_name not in (None, name):
            sys.exit(f"ir-lean named {args.function} {lean_name} in the source and {name} in the target")
        lean_name = name
        shutil.copy(work / "out.lean", out / ARTIFACTS[lean])
    shutil.rmtree(out / ".record")
    shutil.copy(args.certificate, out / ARTIFACTS["certificate"])
    target = ir_target((out / ARTIFACTS["src_ir"]).read_text())
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "claim": {
            "kind": args.kind,
            "namespace": args.namespace,
            "function": args.function,
            "lean_function": lean_name,
            "theorem": args.theorem,
        },
        "llvm": llvm_pin(),
        "transform": {"passes": args.passes, "mtriple": args.mtriple},
        "target": target,
        "artifacts": {role: {"path": p, "sha256": sha256_file(out / p)} for role, p in ARTIFACTS.items()},
        "toolchain": toolchain(run),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(out / "manifest.json")
    return 0


# ------------------------------------------------------------------------------------------------------------
# verify


def exact_keys(obj: Any, keys: set[str], where: str) -> dict:
    if not isinstance(obj, dict):
        refused("manifest_invalid", f"{where} isn't an object")
    if set(obj) != keys:
        refused("manifest_invalid", f"{where} has keys {sorted(obj)}, and needs exactly {sorted(keys)}")
    return obj


def string(
    obj: dict, key: str, pattern: re.Pattern[str] | None, where: str, nullable: bool = False
) -> str | None:
    v = obj[key]
    if v is None and nullable:
        return None
    if not isinstance(v, str) or (pattern is not None and not pattern.fullmatch(v)):
        refused("manifest_invalid", f"{where}.{key} isn't valid: {v!r}")
    return v


def validate(manifest: Any) -> dict:
    """Every field, with exactly the keys it should have: a field nothing checks can't ride along."""
    m = exact_keys(
        manifest, {"schema", "claim", "llvm", "transform", "target", "artifacts", "toolchain"}, "manifest"
    )
    if m["schema"] != MANIFEST_SCHEMA:
        refused("manifest_invalid", f"schema is {m['schema']!r}, not {MANIFEST_SCHEMA}")
    claim = exact_keys(m["claim"], {"kind", "namespace", "function", "lean_function", "theorem"}, "claim")
    if claim["kind"] not in KINDS:
        refused("manifest_invalid", f"claim.kind {claim['kind']!r} isn't one of {sorted(KINDS)}")
    string(claim, "namespace", NAMESPACE, "claim")
    string(claim, "function", re.compile(r"[A-Za-z0-9_.$]+"), "claim")
    string(claim, "lean_function", NAME, "claim")
    string(claim, "theorem", NAME, "claim")
    llvm = exact_keys(m["llvm"], {"repository", "tag", "commit", "nix_hash"}, "llvm")
    for k in llvm:
        string(llvm, k, None, "llvm")
    transform = exact_keys(m["transform"], {"passes", "mtriple"}, "transform")
    string(transform, "passes", PASS_SPEC, "transform")
    string(transform, "mtriple", TRIPLE, "transform", nullable=True)
    target = exact_keys(m["target"], {"triple", "datalayout"}, "target")
    for k in target:
        string(target, k, None, "target", nullable=True)
    artifacts = exact_keys(m["artifacts"], set(ARTIFACTS), "artifacts")
    for role, a in artifacts.items():
        exact_keys(a, {"path", "sha256"}, f"artifacts.{role}")
        string(a, "path", re.compile(r"[A-Za-z0-9_.\-]+"), f"artifacts.{role}")
        string(a, "sha256", SHA, f"artifacts.{role}")
    if len({a["path"] for a in artifacts.values()}) != len(artifacts):
        refused("manifest_invalid", "two artifacts share a path")
    tools = exact_keys(
        m["toolchain"],
        {
            "lean_version",
            "lean_sha256",
            "leanchecker_sha256",
            "opt_version",
            "opt_sha256",
            "ir_lean_sha256",
            "irlean_library_sha256",
            "check_axioms_sha256",
            "binding_check_sha256",
            "binding_py_sha256",
        },
        "toolchain",
    )
    for k in tools:
        string(tools, k, SHA if k.endswith("_sha256") else None, "toolchain")
    return m


def artifact(bundle: Path, a: dict) -> bytes:
    """An artifact's bytes, after checking it's a plain file in the bundle with the recorded hash."""
    path = bundle / a["path"]
    if path.is_symlink() or not path.is_file() or path.resolve().parent != bundle:
        refused("artifact_hash_mismatch", f"{a['path']} isn't a plain file in the bundle")
    data = path.read_bytes()
    if sha256(data) != a["sha256"]:
        refused(
            "artifact_hash_mismatch",
            f"{a['path']} has SHA-256 {sha256(data)}, and the manifest says {a['sha256']}",
        )
    return data


class Check:
    """The checks a verdict lists, in order, with what each found."""

    def __init__(self) -> None:
        self.done: list[dict] = []

    def __call__(self, name: str, detail: str = "") -> None:
        self.done.append({"name": name, "result": "pass", **({"detail": detail} if detail else {})})


def verify(manifest_path: Path, work: Path | None, cache: Path | None, keep: bool, run: Runner) -> dict:
    checks = Check()
    verdict: dict[str, Any] = {
        "schema": VERDICT_SCHEMA,
        "manifest": str(manifest_path),
        "checks": checks.done,
        "memory_capped": run.capped,
        "cache": "disabled" if cache is None else "miss",
    }
    try:
        verdict.update(_verify(manifest_path, work, cache, keep, run, checks, verdict))
    except Verdict as v:
        verdict.update({"status": v.status, "reason": v.reason, "detail": v.detail, **v.extra})
        checks.done.append({"name": "stopped", "result": "fail", "detail": v.reason})
    if verdict["status"] == "bound" and verdict.get("claim", {}).get("kind") not in CHECKABLE:
        # Can't happen: _verify refuses these. A verdict that says otherwise is a bug, and not bound.
        verdict.update(status="error", reason="internal_error")
    verdict["exit_code"] = EXIT[verdict["status"]]
    verdict["establishes"] = ESTABLISHES if verdict["status"] == "bound" else []
    verdict["does_not_establish"] = DOES_NOT_ESTABLISH
    verdict["trusted"] = TRUSTED
    verdict["open_obligation"] = OBLIGATION
    return verdict


def _verify(
    manifest_path: Path,
    work: Path | None,
    cache: Path | None,
    keep: bool,
    run: Runner,
    checks: Check,
    verdict: dict,
) -> dict:
    try:
        raw = json.loads(manifest_path.read_text())
    except (OSError, ValueError) as e:
        refused("manifest_invalid", f"can't read {manifest_path}: {e}")
    m = validate(raw)
    claim = m["claim"]
    verdict["claim"] = {
        "kind": claim["kind"],
        "means": KINDS[claim["kind"]],
        "scope": "one function, one input module, one opt run with this pass spec and triple",
    }
    checks("manifest", MANIFEST_SCHEMA)
    if claim["kind"] not in CHECKABLE:
        raise Verdict(
            "unsupported",
            "claim_kind_unverifiable",
            f"{claim['kind']}: {KINDS[claim['kind']]}. Nothing here can check it. {OBLIGATION}",
        )
    bundle = manifest_path.resolve().parent
    data = {role: artifact(bundle, a) for role, a in m["artifacts"].items()}
    checks("artifacts", "every file hashes as recorded")

    live = toolchain(run)
    differ = sorted(k for k in live if live[k] != m["toolchain"][k])
    if differ:
        refused(
            "toolchain_mismatch",
            f"the toolchain on PATH differs from the recorded one in {differ}",
            recorded={k: m["toolchain"][k] for k in differ},
            live={k: live[k] for k in differ},
        )
    checks("toolchain", "lean, leanchecker, opt, ir-lean, IRLean and these checkers hash as recorded")

    pin = llvm_pin()
    if m["llvm"] != pin:
        refused("llvm_pin_mismatch", f"the manifest names llvm-project {m['llvm']}, and this repo pins {pin}")
    version = pin["tag"].removeprefix("llvmorg-")
    if f"LLVM version {version}" != live["opt_version"]:
        refused("llvm_pin_mismatch", f"opt says {live['opt_version']!r}, and the pin is {pin['tag']}")
    source = llvm_source_hash(run)
    if source != pin["nix_hash"]:
        refused("llvm_pin_mismatch", f"LLVM_PROJECT_SRC hashes to {source}, and the pin is {pin['nix_hash']}")
    checks("llvm_pin", f"{pin['tag']} {pin['commit']}, and LLVM_PROJECT_SRC is that source tree")

    t = m["transform"]
    for role in ("src_ir", "tgt_ir"):
        found = ir_target(data[role].decode(errors="replace"))
        if found != m["target"]:
            refused("config_mismatch", f"{role} has target {found}, and the manifest says {m['target']}")
    if t["mtriple"] is not None and t["mtriple"] != m["target"]["triple"]:
        refused(
            "config_mismatch",
            f"opt ran with -mtriple={t['mtriple']}, and the IR's triple is {m['target']['triple']}",
        )
    checks("target", f"{m['target']['triple']} / {m['target']['datalayout']}")

    tgt_text = data["tgt_ir"].decode(errors="replace")
    if TRUSTED_PROMISES.search(tgt_text):
        raise Verdict(
            "unsupported",
            "trusted_promise",
            "the target IR has mustprogress or willreturn, which IRLean trusts instead of checking",
        )
    verdict["uncovered_changes"] = changes_elsewhere(
        data["src_ir"].decode(errors="replace"), tgt_text, claim["function"]
    )

    # Everything below is replay. The key covers the manifest and the live toolchain, which now agree, so a
    # cached verdict is reused only for exactly this evidence and these tools.
    key = sha256(canonical({"verdict": VERDICT_SCHEMA, "manifest": m, "toolchain": live}))
    verdict["key"] = key
    if cache is not None:
        entry_path = cache / f"{key}.json"
        if entry_path.exists():
            try:
                entry = json.loads(entry_path.read_text())
                good = (
                    entry.get("key") == key
                    and entry.get("manifest_sha256") == sha256(canonical(m))
                    and entry.get("toolchain") == live
                    and entry.get("status") == "bound"
                )
            except (OSError, ValueError, AttributeError):
                good = False
            if good:
                verdict["cache"] = "hit"
                checks("cache", "a verdict for exactly this manifest and toolchain")
                return {
                    "status": "bound",
                    "reason": "replayed",
                    "detail": "from cache",
                    "statement": entry.get("statement"),
                }
            verdict["cache"] = "stale_ignored"

    nonce = secrets.token_hex(8)
    work = (work or RUNS / f"{key[:16]}-{nonce}").resolve()
    if work.exists() and any(work.iterdir()):
        raise Verdict("error", "invalid_request", f"work directory {work} isn't empty")
    work.mkdir(parents=True, exist_ok=True)
    try:
        result = replay(m, data, work, nonce, run, checks)
    finally:
        if not keep:
            shutil.rmtree(work, ignore_errors=True)
    if cache is not None:
        cache.mkdir(parents=True, exist_ok=True)
        entry = {
            "key": key,
            "manifest_sha256": sha256(canonical(m)),
            "toolchain": live,
            "status": "bound",
            "statement": result["statement"],
        }
        tmp = cache / f".{key}.{nonce}"
        tmp.write_text(json.dumps(entry, indent=1, sort_keys=True))
        tmp.replace(cache / f"{key}.json")
    return result


def replay(m: dict, data: dict[str, bytes], work: Path, nonce: str, run: Runner, checks: Check) -> dict:
    claim, t = m["claim"], m["transform"]
    ns = claim["namespace"]

    if run_opt(run, data["input"], "verify", t["mtriple"]) != data["src_ir"]:
        refused("transform_replay_mismatch", "opt reading the input doesn't give the recorded source IR")
    if run_opt(run, data["input"], t["passes"], t["mtriple"]) != data["tgt_ir"]:
        refused(
            "transform_replay_mismatch",
            f"opt -passes={t['passes']} on the input doesn't give the recorded target IR",
        )
    checks("transform_replay", f"opt -passes={t['passes']} gives the target IR byte for byte")

    lean_dir = work / "lean"
    for side, ir, lean in (("Src", "src_ir", "src_lean"), ("Tgt", "tgt_ir", "tgt_lean")):
        d = work / "ir" / side
        d.mkdir(parents=True)
        (d / ARTIFACTS[ir]).write_bytes(data[ir])
        out = lean_dir / ns / f"{side}.lean"
        row = translate(run, d / ARTIFACTS[ir], claim["function"], f"{ns}.{side}", out)
        if out.read_bytes() != data[lean]:
            refused("translation_replay_mismatch", f"ir-lean doesn't write the recorded {ARTIFACTS[lean]}")
        if row[0] != "ok":
            raise Verdict(
                "unsupported", "function_unsupported", f"ir-lean leaves {claim['function']} out: {row[2:]}"
            )
        if row[2] != claim["lean_function"]:
            refused(
                "translation_replay_mismatch",
                f"ir-lean names {claim['function']} {row[2]}, not {claim['lean_function']}",
            )
        # The model has more undefined behavior than LLVM for memory (docs/trust.md), and a source that's
        # undefined where LLVM's isn't would let any target through.
        if row[-1] != "pure":
            raise Verdict(
                "unsupported", "memory_unsupported", f"{claim['function']} uses memory or pointers in {side}"
            )
    checks(
        "translation_replay", "ir-lean writes both recorded modules byte for byte, and the function is pure"
    )

    # IRLean alone, as tools/verify.py links it: the repo's other libraries build next to it, and a
    # certificate mustn't find them.
    library = work / "library"
    library.mkdir()
    for entry in LIBRARY.iterdir():
        if entry.name == "IRLean" or entry.name.startswith("IRLean."):
            (library / entry.name).symlink_to(entry)
    env = {"LEAN_PATH": f"{lean_dir}:{library}"}
    for side in ("Src", "Tgt"):
        code, err, out = run(
            run.lean(
                "-R",
                str(lean_dir),
                "-o",
                str(lean_dir / ns / f"{side}.olean"),
                str(lean_dir / ns / f"{side}.lean"),
            ),
            env=env,
        )
        if code != 0:
            raise Verdict("error", "generated_module_failed", f"{side}: {(out.decode() + err)[-600:]}")
    watched = {
        p: sha256_file(p)
        for p in [
            lean_dir / ns / "Src.olean",
            lean_dir / ns / "Tgt.olean",
            lean_dir / ns / "Src.lean",
            lean_dir / ns / "Tgt.lean",
        ]
    }
    before = toolchain(run)
    checks("compile_generated")

    cert = lean_dir / ns / "Cert.lean"
    cert.write_bytes(data["certificate"])
    code, err, out = run(
        run.lean("-R", str(lean_dir), "-o", str(lean_dir / ns / "Cert.olean"), str(cert)), env=env
    )
    if code != 0:
        refused("certificate_compile_failed", f"Lean rejects the certificate: {(out.decode() + err)[-800:]}")
    # The certificate's code ran while it compiled. What it could have changed is checked again.
    changed = [str(p) for p, h in watched.items() if sha256_file(p) != h]
    after = toolchain(run)
    changed += [k for k in before if before[k] != after[k]]
    if changed:
        refused("artifacts_modified", f"these changed while the certificate compiled: {changed}")
    # The checks below read Cert.olean, each in its own process, and have to read the same one.
    watched[lean_dir / ns / "Cert.olean"] = sha256_file(lean_dir / ns / "Cert.olean")
    checks("compile_certificate", "and nothing it could reach changed")

    src, tgt = f"{ns}.Src.{claim['lean_function']}", f"{ns}.Tgt.{claim['lean_function']}"
    check_dir = work / "check"
    check_dir.mkdir()
    config = {
        "nonce": nonce,
        "kind": claim["kind"],
        "src": src,
        "tgt": tgt,
        "src_module": f"{ns}.Src",
        "tgt_module": f"{ns}.Tgt",
        "cert_module": f"{ns}.Cert",
        "theorem": claim["theorem"],
    }
    (check_dir / "config.json").write_text(json.dumps(config))
    check_file = check_dir / "BindingCheck.lean"
    check_file.write_text(f"import IRLean\nimport {ns}.Src\nimport {ns}.Tgt\n\n" + CHECK.read_text())
    code, err, out = run(
        run.lean(str(check_file)),
        env={**env, "IRLEAN_BINDING_CONFIG": str(check_dir / "config.json"), "IRLEAN_BINDING_NONCE": nonce},
    )
    answers = [line for line in out.decode().splitlines() if line.startswith(f"IRLEAN_BINDING {nonce} ")]
    if code != 0 or len(answers) != 1:
        raise Verdict(
            "error", "tool_failed", f"the binding check gave no single answer: {(out.decode() + err)[-600:]}"
        )
    answer = json.loads(answers[0].split(" ", 2)[2])
    if not answer.get("ok"):
        reason = answer.get("reason", "checker_error")
        detail = answer.get("detail", "")
        extra = {k: answer[k] for k in ("expected", "got", "reducible_defeq") if k in answer}
        if reason in ("claim_kind_unavailable", "claim_kind_unverifiable"):
            raise Verdict("unsupported", reason, detail, **extra)
        if reason == "checker_error":
            raise Verdict("error", reason, detail, **extra)
        refused(reason, detail, **extra)
    checks("claim_type", "the theorem's type is the expected claim, as the same Expr")

    code, err, out = run(
        run.lean(str(AXIOMS)),
        env={
            **env,
            "IRLEAN_CHECK_MODULE": f"{ns}.Cert",
            "IRLEAN_CHECK_GENERATED": f"{ns}.Src {ns}.Tgt",
            "IRLEAN_CHECK_THEOREMS": f"{claim['theorem']} {src}\n{claim['theorem']} {tgt}",
        },
    )
    if code != 0:
        refused("axiom_policy_failed", (out.decode() + err)[-800:])
    checks("axioms", out.decode().strip()[-200:])

    code, err, out = run(["leanchecker", f"{ns}.Src", f"{ns}.Tgt", f"{ns}.Cert"], env=env)
    if code != 0:
        refused("kernel_replay_failed", (out.decode() + err)[-800:])
    checks("kernel_replay", "leanchecker replays the generated modules and the certificate")
    changed = [str(p) for p, h in watched.items() if sha256_file(p) != h]
    final = toolchain(run)
    changed += [k for k in before if before[k] != final[k]]
    if changed:
        refused("artifacts_modified", f"these changed while they were being checked: {changed}")
    checks("unchanged", "every module and tool checked is the one compiled, start to finish")
    return {
        "status": "bound",
        "reason": "replayed",
        "detail": "every check passed",
        "statement": answer["statement"],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    r = sub.add_parser("record")
    r.add_argument("--input", type=Path, required=True)
    r.add_argument("--passes", required=True)
    r.add_argument("--mtriple")
    r.add_argument("--function", required=True)
    r.add_argument("--certificate", type=Path, required=True)
    r.add_argument("--theorem", required=True)
    r.add_argument("--namespace", required=True)
    r.add_argument("--kind", default="ir_instance_equivalence")
    r.add_argument("--out", type=Path, required=True)
    v = sub.add_parser("verify")
    v.add_argument("manifest", type=Path)
    v.add_argument("--cache", type=Path)
    v.add_argument("--work", type=Path)
    v.add_argument("--keep", action="store_true")
    for p in (r, v):
        p.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
        p.add_argument("--memory", type=int, default=DEFAULT_MEMORY_MB, metavar="MB")
    args = ap.parse_args()
    if args.command == "record":
        try:
            return record(args)
        except Verdict as e:
            sys.exit(f"record failed: {e.reason}: {e.detail}")
    verdict: dict[str, Any]
    try:
        verdict = verify(args.manifest, args.work, args.cache, args.keep, Runner(args.timeout, args.memory))
    except Exception as e:  # A bug here answers as error, never as bound.
        verdict = {
            "schema": VERDICT_SCHEMA,
            "status": "error",
            "reason": "internal_error",
            "detail": repr(e),
            "exit_code": EXIT["error"],
        }
    print(json.dumps(verdict, indent=1, ensure_ascii=False))
    return EXIT[verdict["status"]]


if __name__ == "__main__":
    sys.exit(main())
