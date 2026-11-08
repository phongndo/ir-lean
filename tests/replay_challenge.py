#!/usr/bin/env python3
"""Challenges replay certificates from outside, and asks Alive2 what IRLean is asked.
docs/replay-challenge.md has the cases, what each one shows, what was found, and what this doesn't cover.

Three tiers, each independent of the others:

  static  Python only. Fixtures that contradict themselves, manifests tools/binding.py has to refuse before it
          looks at a tool, and how its runner classifies a process that fails, crashes, runs out of time or
          memory, or leaves something running.
  alive   alive-tv only, one capped process at a time. Each pair in tests/replay_challenge/pairs.ll, and
          each case in tests/verification_negative, against what LangRef says, worked out by hand. A case
          certified there that Alive2 finds wrong fails, whatever else is expected.
  live    Lean, one capped process at a time. IRLean's own verdict on each pair, by evaluating both functions
          on every input; and tools/binding.py record and verify on real opt runs, for reasons
          tests/binding.py doesn't reach, with Alive2 asked about every bound bundle.

Run it in `nix develop`. live needs build/ir-lean and `lake build`. Everything is written under
build/replay-challenge, with report.json.

usage: tests/replay_challenge.py [--tier static|alive|live|all] [--only NAME ...] [--keep]

exit: 0 every case came out as expected, 1 one didn't, 2 usage, 3 one couldn't run: a tool is missing, a limit
stopped it, or there wasn't enough memory free. 3 is never a pass.
"""

import argparse
import contextlib
import functools
import importlib.util
import json
import os
import re
import resource
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any, NamedTuple

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "replay_challenge"
CORPUS = ROOT / "tests" / "verification_negative" / "cases"
BINDING = ROOT / "tools" / "binding.py"
TOOL = ROOT / "build" / "ir-lean"
LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
WORK = ROOT / "build" / "replay-challenge"

# One alive-tv run: its solver's time per query, and the process's wall time and memory.
ALIVE_SMT_MS = 10000
ALIVE_SECONDS = 120
ALIVE_MB = 2048
# One Lean process evaluating the pairs.
LEAN_SECONDS = 300
LEAN_MB = 2000
# What tools/binding.py verify gets: its own limit on each process it runs.
BIND_SECONDS = 300
BIND_MB = 3000

# tools/binding.py's contract, as docs/llvm-proof-binding.md states it, written out here rather than read from
# the tool, so a change to the tool shows up as a change.
MANIFEST_SCHEMA = "ir-lean.binding.manifest/1"
VERDICT_SCHEMA = "ir-lean.binding.verdict/1"
EXIT = {"bound": 0, "refused": 1, "unsupported": 3, "unknown": 4, "error": 5}
ROLES = ["input", "src_ir", "tgt_ir", "src_lean", "tgt_lean", "certificate"]
TOOLCHAIN_KEYS = [
    "lean_version",
    "lean_sha256",
    "lean_toolchain_sha256",
    "leanchecker_sha256",
    "opt_version",
    "opt_sha256",
    "ir_lean_sha256",
    "irlean_library_sha256",
    "check_axioms_sha256",
    "binding_check_sha256",
    "binding_py_sha256",
]
# What a bound verdict has to have run, in order. A cache hit replaces everything after `target`.
REPLAY_CHECKS = [
    "manifest",
    "artifacts",
    "toolchain",
    "llvm_pin",
    "target",
    "transform_replay",
    "translation_replay",
    "compile_generated",
    "compile_certificate",
    "claim_type",
    "axioms",
    "kernel_replay",
    "unchanged",
]

# What tools/binding.py does where its contract says otherwise. Each was reported to the owner with a
# repro. A case that hits one comes back KNOWN, and passes. If the tool is fixed, the case gets the contract's
# answer and passes too, so either can land first.
FINDINGS = {
    "F1": "A certificate can turn its own refusal into unknown: Lean's output for a step that fails is "
    "matched against the messages of a resource limit, and a certificate writes what that output says",
    "F2": "A manifest the schema should refuse gets past it: a claim kind that isn't a string crashes the "
    "check, JSON nested too deep crashes the reader, a path of '..' is read as a file, and a namespace "
    "that's a root Lean finds modules under, such as IRLean, hides that root from the generated modules",
    "F3": "An internal_error verdict leaves out does_not_establish, trusted and open_obligation, which every "
    "verdict is to carry",
    "F4": "A manifest with a key twice is read with the last, and other readers may take the first: a field "
    "rides along that nothing checks",
}


class Report:
    """What each case came to: ok, known (a finding, expected), fail, or notrun (couldn't say)."""

    def __init__(self, only: list[str] | None) -> None:
        self.rows: list[dict[str, str]] = []
        self.only = only

    def wanted(self, name: str) -> bool:
        return not self.only or any(name == o or name.startswith(o + "/") for o in self.only)

    def add(self, name: str, outcome: str, detail: str = "") -> None:
        self.rows.append({"name": name, "outcome": outcome, "detail": detail})
        tag = {"ok": "ok   ", "known": "KNOWN", "fail": "FAIL ", "notrun": "SKIP "}[outcome]
        print(f"{tag} {name}{': ' + detail if detail else ''}", flush=True)

    def code(self) -> int:
        outcomes = {r["outcome"] for r in self.rows}
        return 1 if "fail" in outcomes else 3 if "notrun" in outcomes else 0


# ------------------------------------------------------------------------------------------------------------
# Running things


class Ran(NamedTuple):
    limit: str | None  # None, or why it was stopped: time_limit or resource_limit
    code: int
    out: str


@functools.cache
def scope_works() -> bool:
    probe = ["systemd-run", "--user", "--scope", "--quiet", "--", "true"]
    return (
        sys.platform.startswith("linux")
        and shutil.which("systemd-run") is not None
        and subprocess.run(probe, capture_output=True, check=False).returncode == 0
    )


def contained(
    argv: list[str],
    seconds: int,
    memory_mb: int,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    address_limit: bool = False,
) -> Ran:
    """Runs `argv` in a process group of its own, and in a scope capped at `memory_mb` with no swap where
    systemd can make one. Without one, `address_limit` caps its address space instead, which Lean can't run
    under, so a Lean process relies on its own `-M`. Running out of time, or dying by a signal, is a limit,
    never an answer. Whatever it leaves running is killed."""
    unit = f"ir-lean-replay-challenge-{os.getpid()}-{secrets.token_hex(4)}"
    command = argv
    preexec: Callable[[], None] | None = None
    if scope_works():
        command = [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            f"--unit={unit}",
            f"--property=MemoryMax={memory_mb}M",
            "--property=MemorySwapMax=0",
            "--",
            *argv,
        ]
    elif address_limit:

        def preexec() -> None:
            resource.setrlimit(resource.RLIMIT_AS, (memory_mb << 20, memory_mb << 20))

    with tempfile.TemporaryFile() as out:
        p = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            stdout=out,
            stderr=subprocess.STDOUT,
            cwd=cwd,
            env={**os.environ, **(env or {})},
            start_new_session=True,
            # This process starts no threads, so nothing holds a lock across the fork.
            preexec_fn=preexec,  # noqa: PLW1509
        )
        limit = None
        try:
            p.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            limit = "time_limit"
        finally:
            if scope_works():
                subprocess.run(
                    ["systemctl", "--user", "kill", "--signal=SIGKILL", f"{unit}.scope"],
                    capture_output=True,
                    check=False,
                )
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.killpg(p.pid, signal.SIGKILL)
            p.kill()
            p.wait()
        out.seek(0)
        text = out.read().decode(errors="replace")
    if limit is None and (p.returncode < 0 or p.returncode == 137):
        limit = "resource_limit"
    return Ran(limit, p.returncode, text)


def running(marker: str) -> list[int]:
    """Processes whose command line has `marker` in it."""
    found = []
    for d in Path("/proc").iterdir():
        if d.name.isdigit():
            with contextlib.suppress(OSError):
                if marker.encode() in (d / "cmdline").read_bytes():
                    found.append(int(d.name))
    return found


# ------------------------------------------------------------------------------------------------------------
# Alive2

SUMMARY = re.compile(
    r"^\s*(\d+) (correct|incorrect|failed-to-prove) transformations$|^\s*(\d+) Alive2 errors$", re.M
)
EXAMPLE = re.compile(r"^Example:\n\S+ %\S+ = (poison|undef|#x([0-9a-f]+))", re.M)


class Alive(NamedTuple):
    verdict: str  # correct, incorrect or unknown
    example: int | str | None  # Alive2's counterexample for the first argument: a value, poison or undef
    out: str


_alive: dict[tuple, Alive] = {}


def function_text(ir: str, name: str) -> str | None:
    """The definition of `name` in `ir`, as LLVM prints one: from `define` to the `}` that starts a line."""
    m = re.search(rf'^define [^@]*@"?{re.escape(name)}"?\(.*?^}}\n', ir, re.M | re.S)
    return m.group(0) if m else None


def alone(ir: str, name: str) -> str | None:
    """`name` from `ir`, renamed `f`, in a module of its own with `ir`'s target and declarations."""
    body = function_text(ir, name)
    if body is None:
        return None
    keep = [x for x in ir.splitlines() if x.startswith(("target ", "declare "))]
    return "\n".join(keep) + "\n\n" + re.sub(rf'@"?{re.escape(name)}"?\(', "@f(", body, count=1)


def alive(src_ir: str, src: str, tgt_ir: str, tgt: str, undef: bool, *extra: str) -> Alive:
    """What alive-tv says about `src` in `src_ir` becoming `tgt` in `tgt_ir`. Each is put alone in a file, as
    `f`, since alive-tv checks every function against itself, and calls them correct, when it doesn't find the
    one `--src-fn` names, and prints no count for a file with only `src` and `tgt`. So it's correct only if it
    proved exactly one pair, incorrect only if it found exactly one wrong, and otherwise unknown: a timeout, a
    failure to prove, an error of its own, or output it doesn't print."""
    key = (src_ir, src, tgt_ir, tgt, undef, extra)
    if key not in _alive:
        a, b = alone(src_ir, src), alone(tgt_ir, tgt)
        if a is None or b is None:
            _alive[key] = Alive("unknown", None, f"no function {src if a is None else tgt}")
            return _alive[key]
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "src.ll").write_text(a)
            (Path(d) / "tgt.ll").write_text(b)
            argv = [
                "alive-tv",
                f"--smt-to={ALIVE_SMT_MS}",
                *([] if undef else ["--disable-undef-input"]),
                *extra,
                str(Path(d) / "src.ll"),
                str(Path(d) / "tgt.ll"),
            ]
            r = contained(argv, ALIVE_SECONDS, ALIVE_MB, address_limit=True)
        counts: dict[str, int] = {}
        for m in SUMMARY.finditer(r.out):
            counts[m.group(2) or "errors"] = int(m.group(1) or m.group(3))
        verdict = "unknown"
        if r.limit is None and len(counts) == 4 and not counts["errors"] and not counts["failed-to-prove"]:
            if (counts["correct"], counts["incorrect"]) == (1, 0):
                verdict = "correct"
            elif (counts["correct"], counts["incorrect"]) == (0, 1):
                verdict = "incorrect"
        example: int | str | None = None
        if verdict == "incorrect" and (m := EXAMPLE.search(r.out)):
            example = int(m.group(2), 16) if m.group(2) else m.group(1)
        _alive[key] = Alive(verdict, example, (r.limit or "") + r.out)
    return _alive[key]


# ------------------------------------------------------------------------------------------------------------
# The pairs


def load_pairs() -> list[dict[str, Any]]:
    return json.loads((HERE / "pairs.json").read_text())["pairs"]


def failing_set(runs: list) -> set[int | str]:
    """The inputs a pair is wrong on, from pairs.json's runs: [first, last, step], or "poison"."""
    out: set[int | str] = set()
    for r in runs:
        if r == "poison":
            out.add("poison")
        else:
            first, last, step = r
            out.update(range(first, last + 1, step))
    return out


DEFINED = re.compile(r"^define [^@]*@([\w.]+)\(", re.M)


def check_fixtures(report: Report) -> None:
    """pairs.json and pairs.ll say the same thing, and pairs.json doesn't contradict itself: a pair that's
    right when no argument is undef fails on nothing, and one that's equal is right."""
    name = "static/fixtures"
    if not report.wanted(name):
        return
    problems = []
    pairs = load_pairs()
    ids = [p["id"] for p in pairs]
    defined = DEFINED.findall((HERE / "pairs.ll").read_text())
    if sorted(defined) != sorted(f"{i}_{side}" for i in ids for side in ("src", "tgt")):
        problems.append(f"pairs.ll defines {sorted(defined)}, and pairs.json has {sorted(ids)}")
    if len(set(ids)) != len(ids):
        problems.append("an id appears twice")
    for p in pairs:
        if set(p) != {"id", "llvm", "failing", "equal", "why"}:
            problems.append(f"{p.get('id')}: keys {sorted(p)}")
            continue
        valid = p["llvm"]["no_undef"] == "valid"
        if valid != (not failing_set(p["failing"])):
            problems.append(
                f"{p['id']}: valid is {valid}, and it fails on {sorted(map(str, failing_set(p['failing'])))}"
            )
        if p["equal"] and not valid:
            problems.append(f"{p['id']}: equal, and wrong")
        if {p["llvm"]["no_undef"], p["llvm"]["undef"]} - {"valid", "invalid"}:
            problems.append(f"{p['id']}: llvm is {p['llvm']}")
    if problems:
        report.add(name, "fail", "; ".join(problems))
    else:
        report.add(name, "ok", f"{len(pairs)} pairs")


# ------------------------------------------------------------------------------------------------------------
# tools/binding.py's verdicts


def invariants(v: dict[str, Any], code: int) -> tuple[list[str], list[str]]:
    """What every verdict has to be, whatever it says: problems that fail a case, and findings it shows."""
    problems, findings = [], []
    status = v.get("status")
    if v.get("schema") != VERDICT_SCHEMA:
        problems.append(f"schema is {v.get('schema')!r}")
    if status not in EXIT:
        problems.append(f"status is {status!r}")
        return problems, findings
    if v.get("exit_code") != EXIT[status] or code != EXIT[status]:
        problems.append(f"{status} exited {code}, and says exit_code {v.get('exit_code')!r}")
    lacking = [k for k in ("does_not_establish", "trusted", "open_obligation") if not v.get(k)]
    if lacking and v.get("reason") == "internal_error":
        findings.append("F3")
    elif lacking:
        problems.append(f"no {lacking}")
    if status != "bound" and v.get("establishes"):
        problems.append(f"{status}, and it establishes {v['establishes']}")
    if status == "bound":
        names = [c.get("name") for c in v.get("checks", [])]
        expected = [*REPLAY_CHECKS[:5], "cache"] if v.get("cache") == "hit" else REPLAY_CHECKS
        if names != expected:
            problems.append(f"bound after the checks {names}, not {expected}")
        if any(c.get("result") != "pass" for c in v.get("checks", [])):
            problems.append("bound with a check that didn't pass")
        if not v.get("establishes") or not isinstance(v.get("statement"), str):
            problems.append("bound without what it establishes, or its statement")
        if v.get("claim", {}).get("kind") not in ("ir_instance_equivalence", "ir_instance_refinement"):
            problems.append(f"bound for the claim kind {v.get('claim')}")
    return problems, findings


def judge(
    report: Report,
    name: str,
    v: dict[str, Any] | str,
    code: int,
    contract: tuple[str, str],
    known: tuple[str, str, str] | None = None,
) -> bool:
    """Records whether a verdict is the contract's, or a known finding's. True if it was either."""
    if isinstance(v, str):
        report.add(name, "fail", v)
        return False
    problems, findings = invariants(v, code)
    got = (v.get("status"), v.get("reason"))
    if got[0] == "bound" and contract[0] != "bound":
        problems.insert(0, "bound, which it must never be here")
    if problems:
        report.add(name, "fail", f"{got}: {'; '.join(problems)}. {v.get('detail', '')[:300]}")
        return False
    if got == contract:
        fixed = f": {known[2]} no longer shows" if known else ""
        report.add(
            name, "known" if findings else "ok", f"{got[0]}/{got[1]}{fixed} {' '.join(findings)}".strip()
        )
        return True
    if known and got == known[:2]:
        also = "".join(f", {f}" for f in findings)
        report.add(name, "known", f"{got[0]}/{got[1]}, not {contract[0]}/{contract[1]}: {known[2]}{also}")
        return True
    report.add(
        name, "fail", f"{got[0]}/{got[1]}, not {contract[0]}/{contract[1]}: {v.get('detail', '')[:300]}"
    )
    return False


def binding(*args: str, seconds: int = 3600) -> tuple[int, str, str]:
    """tools/binding.py: (exit code, stdout, stderr). It limits each process it runs, and this limits it, past
    what its steps take at their limits. If this one stops it, the scopes it made are killed too, as they're
    outside its process group."""
    with subprocess.Popen(
        [sys.executable, str(BINDING), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
    ) as p:
        try:
            out, err = p.communicate(timeout=seconds)
        except subprocess.TimeoutExpired:
            p.kill()
            p.communicate()
            subprocess.run(
                ["systemctl", "--user", "kill", "--signal=SIGKILL", f"ir-lean-binding-{p.pid}-*.scope"],
                capture_output=True,
                check=False,
            )
            return -1, "", f"tools/binding.py {args[0]} took more than {seconds} s"
    return p.returncode, out, err


def verify(manifest: Path) -> tuple[dict[str, Any] | str, int]:
    """The verdict tools/binding.py prints, without a cache, so every check runs."""
    code, out, err = binding(
        "verify", str(manifest), "--timeout", str(BIND_SECONDS), "--memory", str(BIND_MB)
    )
    try:
        v = json.loads(out)
    except ValueError:
        return f"verify printed no verdict, and exited {code}: {(out + err)[-1500:]}", code
    return (v if isinstance(v, dict) else f"verify printed {v!r}"), code


# ------------------------------------------------------------------------------------------------------------
# static


def manifest_template() -> dict[str, Any]:
    """A manifest with every key, each of the right shape, naming files that aren't there. It gets past the
    schema to the artifacts, so a case that changes one field and gets manifest_invalid was refused for it."""
    zero = "0" * 64
    return {
        "schema": MANIFEST_SCHEMA,
        "claim": {
            "kind": "ir_instance_equivalence",
            "namespace": "Fx",
            "function": "f",
            "lean_function": "f",
            "theorem": "Fx.cert",
        },
        "llvm": {"repository": "r", "tag": "t", "commit": "c", "nix_hash": "n"},
        "transform": {"passes": "instcombine", "mtriple": None},
        "target": {"triple": None, "datalayout": None},
        "artifacts": {role: {"path": f"{role}.txt", "sha256": zero} for role in ROLES},
        "toolchain": {k: zero if k.endswith("_sha256") else "v" for k in TOOLCHAIN_KEYS},
    }


def edited(change: Callable[[dict[str, Any]], None]) -> bytes:
    m = manifest_template()
    change(m)
    return json.dumps(m).encode()


REFUSED_MANIFEST = ("refused", "manifest_invalid")
# Each: a name, the manifest's bytes, the contract's verdict, and a known finding's.
MANIFESTS: list[tuple[str, bytes, tuple[str, str], tuple[str, str, str] | None]] = [
    ("template", edited(lambda m: None), ("refused", "artifact_hash_mismatch"), None),
    ("not_utf8", b'{"schema": "\xff"}', REFUSED_MANIFEST, None),
    ("top_level_array", b"[]", REFUSED_MANIFEST, None),
    ("mtriple_not_a_string", edited(lambda m: m["transform"].update(mtriple=False)), REFUSED_MANIFEST, None),
    (
        "option_in_passes",
        edited(lambda m: m["transform"].update(passes="instcombine -disable-output")),
        REFUSED_MANIFEST,
        None,
    ),
    ("function_with_type", edited(lambda m: m["claim"].update(function="f(i8)")), REFUSED_MANIFEST, None),
    (
        "kind_a_list",
        edited(lambda m: m["claim"].update(kind=["ir_instance_equivalence"])),
        REFUSED_MANIFEST,
        ("error", "internal_error", "F2"),
    ),
    (
        "kind_an_object",
        edited(lambda m: m["claim"].update(kind={"ir_instance_equivalence": True})),
        REFUSED_MANIFEST,
        ("error", "internal_error", "F2"),
    ),
    ("nested_too_deep", b"[" * 100000 + b"]" * 100000, REFUSED_MANIFEST, ("error", "internal_error", "F2")),
    (
        "path_parent",
        edited(lambda m: m["artifacts"]["input"].update(path="..")),
        REFUSED_MANIFEST,
        ("refused", "artifact_hash_mismatch", "F2"),
    ),
    # The first `kind` is an L4 claim, and the last the one checked. Python's reader takes the last.
    (
        "key_twice",
        edited(lambda m: None).replace(
            b'"kind": "ir_instance_equivalence"',
            b'"kind": "pass_implementation", "kind": "ir_instance_equivalence"',
        ),
        REFUSED_MANIFEST,
        ("refused", "artifact_hash_mismatch", "F4"),
    ),
]


def manifest_cases(report: Report) -> None:
    base = WORK / "static" / "manifests"
    for name, data, contract, known in MANIFESTS:
        case = f"static/manifest/{name}"
        if not report.wanted(case):
            continue
        d = base / name
        shutil.rmtree(d, ignore_errors=True)
        d.mkdir(parents=True)
        (d / "manifest.json").write_bytes(data)
        v, code = verify(d / "manifest.json")
        judge(report, case, v, code, contract, known)


def load_binding() -> ModuleType:
    """tools/binding.py as a module, to run its runner on processes that misbehave on purpose."""
    spec = importlib.util.spec_from_file_location("binding_under_test", BINDING)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def runner_cases(report: Report) -> None:
    """tools/binding.py's runner: a failure is an answer, and a crash, a timeout or running out of memory is
    unknown, and leaves nothing running."""
    if not any(
        report.wanted(f"static/runner/{n}") for n in ("failure", "signal", "timeout", "leftover", "memory")
    ):
        return
    b = load_binding()
    py = sys.executable
    marker = f"{317 + secrets.randbelow(1000)}.{secrets.randbelow(10**6)}"

    def outcome(timeout: int, memory: int, argv: list[str]) -> tuple[str, str]:
        try:
            return "returned", str(b.Runner(timeout, memory)(argv)[0])
        except b.Verdict as v:
            return v.status, v.reason

    cases: list[tuple[str, int, int, list[str], tuple[str, str], str | None]] = [
        (
            "failure",
            30,
            500,
            [py, "-c", "print('error: type mismatch'); raise SystemExit(1)"],
            ("returned", "1"),
            None,
        ),
        (
            "signal",
            30,
            500,
            [py, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGSEGV)"],
            ("unknown", "resource_limit"),
            None,
        ),
        (
            "timeout",
            2,
            500,
            [py, "-c", f"import subprocess, time; subprocess.Popen(['sleep', '{marker}1']); time.sleep(60)"],
            ("unknown", "time_limit"),
            f"sleep {marker}1",
        ),
        (
            "leftover",
            30,
            500,
            [py, "-c", f"import subprocess; subprocess.Popen(['sleep', '{marker}2'])"],
            ("returned", "0"),
            f"sleep {marker}2",
        ),
    ]
    for name, timeout, memory, argv, want, left in cases:
        case = f"static/runner/{name}"
        if not report.wanted(case):
            continue
        got = outcome(timeout, memory, argv)
        stray = running(left.split()[1]) if left else []
        if got == want and not stray:
            report.add(case, "ok", f"{got[0]}/{got[1]}" + (", nothing left running" if left else ""))
        else:
            for pid in stray:
                with contextlib.suppress(ProcessLookupError):
                    os.kill(pid, signal.SIGKILL)
            report.add(case, "fail", f"{got}, not {want}" + (f", and {stray} left running" if stray else ""))
    case = "static/runner/memory"
    if report.wanted(case):
        capped = b.Runner(30, 200).capped
        if capped != scope_works():
            report.add(
                case, "fail", f"the runner says capped is {capped}, and a scope works: {scope_works()}"
            )
        elif not capped:
            # Nothing to classify: no cgroup kills anything here, and the runner doesn't say one does, so
            # every verdict's memory_capped is false, and Lean's -M is the only cap.
            report.add(case, "ok", "no systemd scope here, and the runner doesn't claim one")
        else:
            got = outcome(30, 200, [py, "-c", "x = bytearray(1536 << 20); print(len(x))"])
            want = ("unknown", "resource_limit")
            report.add(case, "ok" if got == want else "fail", f"{got[0]}/{got[1]}")


def promise_cases(report: Report) -> None:
    """The promises IRLean trusts are found wherever LLVM writes them, in metadata and attribute groups
    too."""
    case = "static/promises"
    if not report.wanted(case):
        return
    b = load_binding()
    texts = {
        "loop metadata": '!1 = distinct !{!1, !2}\n!2 = !{!"llvm.loop.mustprogress"}\n',
        "attribute group": "attributes #0 = { mustprogress nofree norecurse }\n",
        "function attribute": "define i8 @f(i8 noundef %x) willreturn {\n",
    }
    missed = [k for k, t in texts.items() if not b.TRUSTED_PROMISES.search(t)]
    report.add(case, "fail" if missed else "ok", f"missed in {missed}" if missed else ", ".join(texts))


def static_tier(report: Report) -> None:
    check_fixtures(report)
    manifest_cases(report)
    runner_cases(report)
    promise_cases(report)


# ------------------------------------------------------------------------------------------------------------
# alive


HYPOTHESIS = re.compile(r"(\w+) < (\d+)#(\d+)")


def with_assumptions(ir: str, src: str, hypotheses: list[str]) -> str | None:
    """`ir` with `hypotheses` assumed at the start of `src`, as Alive2 reads a precondition: where one fails,
    src is undefined, which allows anything. Only `x < N#W` is read, which is unsigned in Lean. None for
    anything else."""
    lines = []
    for i, h in enumerate(hypotheses):
        m = HYPOTHESIS.fullmatch(h.strip())
        if m is None:
            return None
        var, bound, width = m.groups()
        lines += [f"  %pre.{i} = icmp ult i{width} %{var}, {bound}", f"  call void @llvm.assume(i1 %pre.{i})"]
    head = re.search(rf"^define [^@]*@{re.escape(src)}\(.*\{{\n(\w+:\n)?", ir, re.M)
    if head is None:
        return None
    return ir[: head.end()] + "\n".join(lines) + "\n" + ir[head.end() :] + "\ndeclare void @llvm.assume(i1)\n"


def function_of(term: str | None, default: str) -> str:
    """The function a claim's side names: `src` in `Opt.src (some x)`."""
    m = re.match(r"\w+\.(\w+)\b", term or "")
    return m.group(1) if m else default


def pair_alive(p: dict[str, Any], undef: bool) -> Alive:
    ir = (HERE / "pairs.ll").read_text()
    return alive(ir, f"{p['id']}_src", ir, f"{p['id']}_tgt", undef)


def alive_tier(report: Report) -> None:
    if shutil.which("alive-tv") is None or shutil.which("opt") is None:
        report.add("alive", "notrun", "alive-tv or opt isn't on PATH: run inside nix develop")
        return
    for ll in sorted(HERE.glob("*.ll")):
        r = contained(["opt", "-passes=verify", "-disable-output", str(ll)], 60, 2048)
        if r.code != 0 or r.limit:
            report.add(f"alive/fixture/{ll.name}", "fail", f"opt's verifier rejects it: {r.out[-500:]}")
    for p in load_pairs():
        for mode in ("no_undef", "undef"):
            name = f"alive/pair/{p['id']}/{mode}"
            if not report.wanted(name):
                continue
            want = {"valid": "correct", "invalid": "incorrect"}[p["llvm"][mode]]
            a = pair_alive(p, undef=mode == "undef")
            if a.verdict == "unknown":
                report.add(name, "notrun", f"Alive2 didn't decide: {a.out[-300:]}")
            elif a.verdict != want:
                report.add(name, "fail", f"Alive2 says {a.verdict}, and LangRef {p['llvm'][mode]}")
            elif (
                a.verdict == "incorrect" and mode == "no_undef" and a.example not in failing_set(p["failing"])
            ):
                report.add(name, "fail", f"Alive2's counterexample {a.example} isn't one pairs.json gives")
            else:
                report.add(name, "ok", a.verdict + (f" at {a.example}" if a.example is not None else ""))
    explained = json.loads((HERE / "corpus.json").read_text())["alive2"]
    for d in sorted(p for p in CORPUS.iterdir() if (p / "case.json").exists()):
        case = json.loads((d / "case.json").read_text())
        claim = case.get("claim") or {}
        src, tgt = function_of(claim.get("src"), "src"), function_of(claim.get("tgt"), "tgt")
        text: str | None = (d / case["request"]["input"]["ir"]).read_text()
        if claim.get("hypotheses"):
            text = with_assumptions(text or "", src, claim["hypotheses"])
        if text is None:
            report.add(f"alive/corpus/{d.name}", "notrun", f"can't state {claim['hypotheses']} for Alive2")
            continue
        note = explained.get(d.name, {})
        want = note.get("expect") or {"valid": "correct", "invalid": "incorrect"}.get(case["llvm_verdict"])
        for mode in ("no_undef", "undef"):
            name = f"alive/corpus/{d.name}/{mode}"
            if not report.wanted(name):
                continue
            a = alive(text, src, text, tgt, undef=mode == "undef")
            if a.verdict == "incorrect" and case["expect"]["certified"]:
                report.add(
                    name,
                    "fail",
                    f"certified by tests/verify_negative.py, and Alive2 finds it wrong at {a.example}",
                )
            elif a.verdict == "unknown":
                report.add(name, "notrun", f"Alive2 didn't decide: {a.out[-300:]}")
            elif want is None:
                report.add(
                    name,
                    "fail",
                    f"nothing says what Alive2 should say to llvm_verdict {case['llvm_verdict']}",
                )
            elif a.verdict != want:
                report.add(name, "fail", f"Alive2 says {a.verdict}, and {want} was expected")
            elif (
                note.get("because") == "bounded_loops"
                and "#sink"
                not in alive(text, src, text, tgt, mode == "undef", "--src-unroll=2", "--tgt-unroll=2").out
            ):
                report.add(name, "fail", "said to be a loop Alive2 cuts, and it didn't cut one")
            else:
                why = f", because of {note['because']}" if note else ""
                report.add(
                    name, "ok", f"{a.verdict}{why}" + (f" at {a.example}" if a.example is not None else "")
                )


# ------------------------------------------------------------------------------------------------------------
# live: IRLean on the pairs

EVALUATE = """import RC

open IRLean

/-- Whether `t` is allowed where `s` happened, as tests/verify_negative.py's claim says: undefined behavior
allows anything, poison any result, a value only itself, a run that never ends only one that never ends, and a
model stop nothing. -/
def allows : Outcome (Val v) → Outcome (Val v) → Bool
  | some (.error (.undefined _)), _ => true
  | some (.error (.model _)), _ => false
  | some (.ok none), _ => true
  | some (.ok (some a)), some (.ok (some b)) => a == b
  | some (.ok (some _)), _ => false
  | none, none => true
  | none, some _ => false

def same : Outcome (Val v) → Outcome (Val v) → Bool
  | none, none => true
  | some (.ok a), some (.ok b) => a == b
  | some (.error e), some (.error f) => e == f
  | _, _ => false

/-- Every input of width `w`: poison, and each value. -/
def inputs (w : Nat) : List (Val w) := none :: (List.range (2 ^ w)).map fun n => some (BitVec.ofNat w n)

def code : Val w → String
  | none => "\\"poison\\""
  | some b => toString b.toNat

/-- One line of JSON about a pair: the inputs where refinement fails, whether the two are equal, and the
inputs where the source stops the model. -/
def row (id : String) (src tgt : Val w → Outcome (Val v)) : String :=
  let xs := inputs w
  let list (ys : List (Val w)) : String := "[" ++ ", ".intercalate (ys.map code) ++ "]"
  let failing := list (xs.filter fun x => !allows (src x) (tgt x))
  let stops := list (xs.filter fun x => match src x with | some (.error (.model _)) => true | _ => false)
  let equal := xs.all fun x => same (src x) (tgt x)
  "REPLAY_PAIR {\\"id\\": \\"" ++ id ++ "\\", \\"failing\\": " ++ failing ++ ", \\"equal\\": " ++
    toString equal ++ ", \\"stops\\": " ++ stops ++ "}"
"""


def model_pairs(report: Report) -> None:
    """IRLean's verdict on each pair, by running both functions on every input, poison included, in Lean's
    interpreter: which inputs refinement fails on, and whether they're equal. A cross-check of the model, not
    a proof: it trusts Lean's compiler, not its kernel."""
    if not any(report.wanted(f"live/model/{p['id']}") for p in load_pairs()):
        return
    d = WORK / "model"
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    env = {"LEAN_PATH": f"{d}:{LIBRARY}", "ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip()}
    r = contained(
        [str(TOOL), str(HERE / "pairs.ll"), "--namespace", "RC", "-o", str(d / "RC.lean")], 120, 2048
    )
    steps = [r]
    if r.code == 0 and not r.limit:
        r = contained(
            ["lean", "-j1", "-M", str(LEAN_MB), "-o", "RC.olean", "RC.lean"],
            LEAN_SECONDS,
            LEAN_MB + 512,
            d,
            env,
        )
        steps.append(r)
    pairs = load_pairs()
    if r.code == 0 and not r.limit:
        (d / "Evaluate.lean").write_text(
            EVALUATE
            + "".join(
                f'\n#eval IO.println (row "{p["id"]}" RC.{p["id"]}_src RC.{p["id"]}_tgt)' for p in pairs
            )
            + "\n"
        )
        r = contained(
            ["lean", "-j1", "-M", str(LEAN_MB), "Evaluate.lean"], LEAN_SECONDS, LEAN_MB + 512, d, env
        )
        steps.append(r)
    if any(s.limit for s in steps):
        report.add("live/model", "notrun", f"a limit stopped it: {steps[-1].limit}")
        return
    if r.code != 0:
        report.add("live/model", "fail", f"ir-lean or Lean failed: {r.out[-1500:]}")
        return
    rows = {}
    for line in r.out.splitlines():
        if line.startswith("REPLAY_PAIR "):
            row = json.loads(line.removeprefix("REPLAY_PAIR "))
            rows[row["id"]] = row
    for p in pairs:
        name = f"live/model/{p['id']}"
        if not report.wanted(name):
            continue
        row = rows.get(p["id"])
        if row is None:
            report.add(name, "fail", "Lean printed nothing for it")
            continue
        got, want = set(row["failing"]), failing_set(p["failing"])
        problems = []
        if got != want:
            problems.append(
                f"fails on {sorted(map(str, got - want))} beyond, and not on {sorted(map(str, want - got))}"
            )
        if row["equal"] != p["equal"]:
            problems.append(f"equal is {row['equal']}, not {p['equal']}")
        if row["stops"]:
            problems.append(f"the source stops the model at {row['stops']}")
        a = pair_alive(p, undef=False)
        if a is not None and a.verdict == "incorrect" and a.example not in got:
            problems.append(f"Alive2's counterexample {a.example} isn't one in the model")
        if problems:
            report.add(name, "fail", "; ".join(problems))
        else:
            agrees = " and Alive2's counterexample" if a is not None and a.verdict == "incorrect" else ""
            report.add(
                name, "ok", f"fails on {len(got)} inputs, as pairs.json{agrees} says, equal {row['equal']}"
            )


# ------------------------------------------------------------------------------------------------------------
# live: tools/binding.py on real opt runs

CLAIM = (
    "Fx.Src.f = Fx.Tgt.f ∧\n"
    "    ∀ (x : IRLean.Val 8) (s : IRLean.ModelStop), Fx.Src.f x ≠ some (.error (.model s))"
)
GOOD = (HERE / "MulNsw.lean").read_text()
assert CLAIM in GOOD
HEADER = "import Fx.Src\nimport Fx.Tgt\n\nopen IRLean\n\n"
# A certificate that compiles and claims nothing, for cases stopped before its theorem is read.
TRIVIAL = "import Fx.Src\nimport Fx.Tgt\n\ntheorem Fx.cert : True := trivial\n"


def record(
    name: str,
    input_ll: Path,
    passes: str,
    certificate: str,
    namespace: str = "Fx",
    function: str = "f",
) -> Path | str:
    bundle = WORK / "live" / name
    shutil.rmtree(bundle, ignore_errors=True)
    cert = WORK / "live" / f"{name}.lean"
    cert.parent.mkdir(parents=True, exist_ok=True)
    cert.write_text(certificate)
    code, out, err = binding(
        "record",
        *("--input", str(input_ll), "--passes", passes, "--mtriple", "x86_64-unknown-linux-gnu"),
        *("--function", function, "--certificate", str(cert), "--theorem", f"{namespace}.cert"),
        *("--namespace", namespace, "--out", str(bundle)),
    )
    return bundle / "manifest.json" if code == 0 else f"record failed: {(out + err)[-1500:]}"


def edit(manifest: Path | str, change: Callable[[dict[str, Any]], None]) -> Path | str:
    if isinstance(manifest, str):
        return manifest
    m = json.loads(manifest.read_text())
    change(m)
    manifest.write_text(json.dumps(m, indent=2, sort_keys=True))
    return manifest


def copy(manifest: Path | str, name: str) -> Path | str:
    """A copy of a recorded bundle, somewhere else."""
    if isinstance(manifest, str):
        return manifest
    out = WORK / "live" / name / "elsewhere" / "bundle"
    shutil.rmtree(out.parent.parent, ignore_errors=True)
    shutil.copytree(manifest.parent, out)
    return out / "manifest.json"


def against_alive(report: Report, name: str, manifest: Path) -> None:
    """Alive2 on the bundle's own IR, for the claim's function: a bound bundle Alive2 finds wrong is a bug in
    one of them, and one it can't decide is unknown."""
    d = manifest.parent
    a = alive((d / "src.ll").read_text(), "f", (d / "tgt.ll").read_text(), "f", undef=False)
    if a.verdict == "correct":
        report.add(name, "ok", "Alive2 agrees the opt run is right")
    elif a.verdict == "unknown":
        report.add(name, "notrun", f"Alive2 didn't decide: {a.out[-300:]}")
    else:
        report.add(name, "fail", f"Alive2 finds the opt run wrong at {a.example}")


SPOOF = (
    GOOD
    + '\ntheorem Fx.spoof : False := by\n  fail "maximum number of heartbeats (200000) has been reached"\n'
)
AXIOM = HEADER + f"axiom Fx.trustMe : {CLAIM}\n\ntheorem Fx.cert : {CLAIM} :=\n  Fx.trustMe\n"


def binding_cases(report: Report) -> None:
    mul_nsw = HERE / "mul_nsw.ll"
    good: Path | str | None = None

    def recorded_good() -> Path | str:
        nonlocal good
        if good is None:
            good = record("good", mul_nsw, "instcombine", GOOD)
        return good

    cases: list[tuple[str, Callable[[], Path | str], tuple[str, str], tuple[str, str, str] | None]] = [
        ("bound", recorded_good, ("bound", "replayed"), None),
        (
            "add_zero_bound",
            lambda: record(
                "add_zero_bound",
                ROOT / "tests" / "binding" / "add_zero.ll",
                "instcombine",
                (ROOT / "tests" / "binding" / "AddZero.lean").read_text(),
            ),
            ("bound", "replayed"),
            None,
        ),
        ("relocated", lambda: copy(recorded_good(), "relocated"), ("bound", "replayed"), None),
        (
            "function_missing",
            lambda: edit(
                copy(recorded_good(), "function_missing"),
                lambda j: j["claim"].update(function="h", lean_function="h"),
            ),
            ("refused", "function_not_found"),
            None,
        ),
        (
            "signature_changed",
            lambda: record("signature_changed", HERE / "dead_argument.ll", "deadargelim", TRIVIAL),
            ("refused", "signature_mismatch"),
            None,
        ),
        (
            "namespace_irlean",
            lambda: record(
                "namespace_irlean",
                mul_nsw,
                "instcombine",
                TRIVIAL.replace("Fx", "IRLean"),
                namespace="IRLean",
            ),
            REFUSED_MANIFEST,
            ("error", "generated_module_failed", "F2"),
        ),
        (
            "string_noundef",
            lambda: record("string_noundef", HERE / "string_noundef.ll", "instcombine", TRIVIAL),
            ("unsupported", "undef_argument"),
            None,
        ),
        (
            "o2_promises",
            lambda: record("o2_promises", mul_nsw, "default<O2>", GOOD),
            ("unsupported", "trusted_promise"),
            None,
        ),
        (
            "custom_axiom",
            lambda: record("custom_axiom", mul_nsw, "instcombine", AXIOM),
            ("refused", "axiom_policy_failed"),
            None,
        ),
        (
            "spoofed_limit",
            lambda: record("spoofed_limit", mul_nsw, "instcombine", SPOOF),
            ("refused", "certificate_compile_failed"),
            ("unknown", "resource_limit", "F1"),
        ),
    ]
    for name, make, contract, known in cases:
        case = f"live/binding/{name}"
        if not report.wanted(case):
            continue
        manifest = make()
        if isinstance(manifest, str):
            report.add(case, "fail", manifest)
            continue
        v, code = verify(manifest)
        if isinstance(v, dict) and v.get("reason") in ("toolchain_missing",):
            report.add(case, "notrun", f"{v.get('reason')}: {v.get('detail')}")
            continue
        if judge(report, case, v, code, contract, known) and contract[0] == "bound":
            against_alive(report, f"{case}/alive", manifest)
        elif name == "o2_promises":
            # Unsupported isn't refuted: Alive2 finds the O2 pipeline's output right.
            against_alive(report, f"{case}/alive", manifest)


def available_mb() -> int:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) // 1024
    return 0


def live_tier(report: Report, min_available_mb: int) -> None:
    missing = [str(p) for p in (TOOL, LIBRARY / "IRLean.olean") if not p.exists()]
    missing += [t for t in ("lean", "opt", "alive-tv") if shutil.which(t) is None]
    if not os.environ.get("LLVM_PROJECT_SRC"):
        missing.append("LLVM_PROJECT_SRC")
    if missing:
        report.add("live", "notrun", f"missing {missing}: build ir-lean, run lake build, and use nix develop")
        return
    if (free := available_mb()) < min_available_mb:
        report.add("live", "notrun", f"{free} MB free, and it needs {min_available_mb}")
        return
    model_pairs(report)
    binding_cases(report)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--tier", choices=["static", "alive", "live", "all"], default="all")
    ap.add_argument("--only", nargs="*", help="cases by name, or by a prefix ending before a /")
    ap.add_argument("--keep", action="store_true", help="keep build/replay-challenge's work directories")
    ap.add_argument("--min-available-mb", type=int, default=4000)
    args = ap.parse_args()
    report = Report(args.only)
    WORK.mkdir(parents=True, exist_ok=True)
    try:
        if args.tier in ("static", "all"):
            static_tier(report)
        if args.tier in ("alive", "all"):
            alive_tier(report)
        if args.tier in ("live", "all"):
            live_tier(report, args.min_available_mb)
    finally:
        if not args.keep:
            for d in ("static", "alive", "model", "live"):
                shutil.rmtree(WORK / d, ignore_errors=True)
    if not report.rows:
        print("no case matched", file=sys.stderr)
        return 2
    seen = sorted({f for f in FINDINGS for r in report.rows if r["outcome"] == "known" and f in r["detail"]})
    for f in seen:
        print(f"known {f}: {FINDINGS[f]}")
    (WORK / "report.json").write_text(json.dumps({"tier": args.tier, "cases": report.rows}, indent=1) + "\n")
    counts = {o: sum(r["outcome"] == o for r in report.rows) for o in ("ok", "known", "fail", "notrun")}
    print(f"{counts['ok']} ok, {counts['known']} known, {counts['fail']} failed, {counts['notrun']} not run")
    return report.code()


if __name__ == "__main__":
    sys.exit(main())
