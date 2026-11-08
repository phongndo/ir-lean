#!/usr/bin/env python3
"""Runs LLVM's passes on their own regression tests, and binds a certificate to each function a run
changed, as replayable evidence that tools/binding.py checks from scratch. docs/passes.md says what each
status means, what the report counts, and what it doesn't.

For each test in llvm/test/Transforms whose RUN line runs one pass in `opt` with `-passes=`, this runs that
pass on the test, as tools/binding.py would, and finds the functions the run changed, and their callers: the
instances. For each one the model can judge, it writes a certificate stating the claim
tools/binding_check.lean builds for the claim kind, with a proof its own automation found, untrusted. If Lean
accepts it, it records a bundle with `tools/binding.py record`, one function, one test and one `opt` run, and
checks it with `tools/binding.py verify`. An instance counts only if that verdict, from this run, is `bound`:

  bound        tools/binding.py verify said `bound` in this run, with exit code 0
  refused      it said `refused`: the evidence doesn't bind. Never a counterexample
  unsupported  the model or the bundle format can't state the claim: the function is left out, uses memory,
               can take `undef`, the target IR makes a promise IRLean trusts, the pass added or removed the
               function, or the RUN line has an option a bundle can't represent
  failed       the automation found no proof. Never a counterexample: nothing here finds one
  unknown      a time or memory limit stopped a step. More may help
  error        a tool failed, or a bug here

A pass is never done: a bound instance is translation validation of one run, not a proof of the pass, its
C++, or a pipeline. Before scoring, known-wrong rewrites have to fail to prove, and one right rewrite has to
be bound, or nothing is scored.

Results are cached in WORK/runs, keyed on the test, the pass spec, the triple, the options, the claim kind,
the limits, this file and every tool tools/binding.py hashes. The cache never holds `bound`: an instance that
was bound is stored as a `candidate` with its bundle, and verified again every run, which tools/binding.py may
answer from its own cache only after rehashing the bundle and the toolchain. Entries of another schema or key,
and the research scorer's build/passes/cache, are never read.

Memory is capped, since an uncapped run once filled RAM and the OOM killer took the agent that started it. On
Linux the scorer re-runs itself in a systemd scope of its own, capped at --memory with no swap, and each
process it starts gets a cgroup there capped at --lean-memory plus 512 MB. tools/binding.py caps each of its
processes the same way, in a scope of its own. At most two test runs go at once. A process stopped by a limit,
the wall clock, its cap or any signal, makes its instances unknown, never bound.

usage: tests/passes.py [build/ir-lean] [--only PASS ...] [--files TEST ...] [--limit-files N] [--max-runs N]
                       [--jobs N] [--memory MB] [--no-scope] [--timeout S] [--lean-memory MB]
                       [--kind KIND] [--work DIR] [--json FILE] [--no-cache] [--keep]
                       [--debug FILE SPEC TRIPLE]
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import hashlib
import importlib.util
import itertools
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
SELF = Path(__file__).resolve()
BINDING_PY = ROOT / "tools" / "binding.py"
INVENTORY = ROOT / "tests" / "llvm_scope" / "inventory.json"
TOOL = ROOT / "build" / "ir-lean"


def load_binding() -> Any:
    """tools/binding.py, for its constants and helpers, so the scorer asks what it checks, the same way."""
    spec = importlib.util.spec_from_file_location("ir_lean_binding", BINDING_PY)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


B = load_binding()

INSTANCE_SCHEMA = "ir-lean.passes.instance/1"
RUN_SCHEMA = "ir-lean.passes.run/1"
SCORE_SCHEMA = "ir-lean.passes.score/1"
SELFCHECK_SCHEMA = "ir-lean.passes.selfcheck/1"
# Bump when what a result means changes. The research scorer's results were version 2.
VERSION = "3"
STATUSES = ("bound", "refused", "unsupported", "failed", "unknown", "error")
# What a run's cache entry may say of an instance. Never `bound`: a `candidate` is verified again.
CACHED_STATUSES = ("candidate", "refused", "unsupported", "failed", "unknown")

# The scorer's share of RAM, as its scope's hard cap. It gets less if that much isn't available, keeping
# HEADROOM_MB free for everything else.
MEMORY_SHARE = 0.6
HEADROOM_MB = 3072
# Kept back from the scorer's cap for itself, and for the page cache its processes share.
SCORER_MB = 2048
# What a cgroup gets above Lean's own -M limit, as tools/binding.py gives it.
CGROUP_SLACK_MB = 512
# Test runs at once. Each runs one process at a time, and tools/binding.py's processes are capped outside the
# scorer's scope, so this bounds the total too.
MAX_JOBS = 2
HEARTBEATS = 2000000
OPT_TIMEOUT = 120
# tools/binding.py verify runs about fifteen processes, each under --timeout. This only catches a hang.
VERIFY_STEPS = 20
# Set in the scorer's own scope, to the cap in MB, so it doesn't re-run itself again.
SCOPE_ENV = "IRLEAN_PASSES_SCOPE"
LEAN_ERROR = re.compile(r"^.*?:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$", re.M)

RUN_LINE = re.compile(r"^\s*;\s*RUN:(.*)$", re.M)
# What a RUN line's opt may say besides -passes= and -mtriple: where it reads and writes, and nothing else.
# -disable-output only stops opt printing what the pass made.
IO_FLAGS = {"-S", "-", "%s", "-disable-output", "--disable-output"}
# A shell redirection, which shlex leaves as a word: `< %s`, `2>&1`, `2> %t`, `>%t`.
REDIRECT = re.compile(r"\d*(?:<|>>?)(&\d+|\S*)")
FUNCTION_NAME = re.compile(r"[A-Za-z0-9_.$]+")
DEFINE_NAME = re.compile(r'^define [^@]*@"?([^"(]+)"?\(', re.M)
SIGNATURE = re.compile(r"^noncomputable def (\S+)((?: \([^()]*\))*) : (Outcome .*) :=$", re.M)


def sha(*parts: str | bytes) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else p.encode())
        h.update(b"\0")
    return h.hexdigest()


def canonical(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def result(status: str, reason: str, detail: str = "", **extra: Any) -> dict:
    assert status in STATUSES or status == "candidate", status
    return {"status": status, "reason": reason, "detail": detail[:600], **extra}


# ------------------------------------------------------------------------------------------------------------
# Memory and processes


def memory_budget() -> int:
    """The default cap on the whole scorer in MB: MEMORY_SHARE of RAM, or less if that isn't available."""
    total = os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // 2**20
    budget = int(total * MEMORY_SHARE)
    try:
        meminfo = Path("/proc/meminfo").read_text()
    except OSError:
        return budget
    m = re.search(r"^MemAvailable:\s+(\d+) kB", meminfo, re.M)
    return min(budget, int(m.group(1)) // 1024 - HEADROOM_MB) if m else budget


def enter_scope(budget: int) -> None:
    """Re-runs the scorer in a systemd scope of its own, capped at `budget` MB without swap, unless it's in
    one. Then running out of memory kills one of its processes, never the agent, editor or session that
    started it. OOMPolicy=continue keeps the scope going when one of its processes is killed, and
    Delegate=yes lets the scorer give each process a cgroup of its own (Cgroups)."""
    if os.environ.get(SCOPE_ENV) or not sys.platform.startswith("linux") or not shutil.which("systemd-run"):
        return
    probe = ["systemd-run", "--user", "--scope", "--quiet", "--", "true"]
    r = subprocess.run(probe, capture_output=True, text=True, check=False)
    if r.returncode != 0:
        print(f"warning: no systemd scope, so nothing caps memory: {r.stderr.strip()}", file=sys.stderr)
        return
    os.environ[SCOPE_ENV] = str(budget)
    properties = [f"MemoryMax={budget}M", "MemorySwapMax=0", "OOMPolicy=continue", "Delegate=yes"]
    command = ["systemd-run", "--user", "--scope", "--quiet", *(f"--property={p}" for p in properties), "--"]
    sys.stdout.flush()
    os.execvp(command[0], [*command, sys.executable, *sys.argv])


def peak_mb(cg: Path) -> int:
    """The most memory a cgroup has used, in MB, or 0 on a kernel too old to say (before 5.19)."""
    try:
        return int((cg / "memory.peak").read_text()) // 2**20
    except (OSError, ValueError):
        return 0


class Cgroups:
    """A cgroup for each process the scorer starts, capped without swap, in the scope that enter_scope made.
    The OOM killer stops all of a cgroup's processes at once: lean and its SAT solver."""

    def __init__(self) -> None:
        self.root: Path | None = None
        self.cap_mb = 0
        self.ids = itertools.count()
        self.lock = threading.Lock()
        # Per tool: processes run, seconds they took, most MB one used, and how many the OOM killer stopped.
        self.stats: dict[str, list[float]] = {}

    def setup(self, cap_mb: int) -> None:
        self.cap_mb = cap_mb
        if not os.environ.get(SCOPE_ENV):
            return
        try:
            line = next(x for x in Path("/proc/self/cgroup").read_text().splitlines() if x.startswith("0::"))
            root = Path("/sys/fs/cgroup") / line[3:].lstrip("/")
            # A cgroup with processes can't hand its memory controller down, so the scorer moves out first.
            (root / "scorer").mkdir(exist_ok=True)
            (root / "scorer" / "cgroup.procs").write_text("0")
            (root / "cgroup.subtree_control").write_text("+memory")
        except (OSError, StopIteration) as e:
            print(f"warning: no cgroup per process, so only the scorer's cap holds: {e}", file=sys.stderr)
            return
        self.root = root

    def make(self) -> Path | None:
        if self.root is None:
            return None
        cg = self.root / f"p{next(self.ids)}"
        cg.mkdir()
        (cg / "memory.max").write_text(f"{self.cap_mb}M")
        (cg / "memory.swap.max").write_text("0")
        (cg / "memory.oom.group").write_text("1")
        return cg

    def finish(self, cg: Path, tool: str, seconds: float) -> str | None:
        """Kills what's left in the cgroup and removes it. Why the OOM killer stopped it, if it did."""
        try:
            events = dict(line.split() for line in (cg / "memory.events").read_text().splitlines())
        except OSError:
            events = {}
        peak = peak_mb(cg)
        with contextlib.suppress(OSError):
            (cg / "cgroup.kill").write_text("1")
        for _ in range(100):
            try:
                cg.rmdir()
                break
            except OSError:
                time.sleep(0.05)
        why = None
        if int(events.get("oom_kill", 0)):
            # `oom` counts this cgroup reaching its own cap. Without it, the scope as a whole ran out.
            own = int(events.get("oom", 0))
            why = f"over its {self.cap_mb} MB cap" if own else "the scorer as a whole ran out of memory"
        with self.lock:
            s = self.stats.setdefault(tool, [0, 0, 0, 0])
            s[0] += 1
            s[1] += seconds
            s[2] = max(s[2], peak)
            s[3] += why is not None
        return why

    def kill_all(self) -> None:
        if self.root is None:
            return
        for cg in self.root.glob("p*"):
            with contextlib.suppress(OSError):
                (cg / "cgroup.kill").write_text("1")

    def summary(self) -> dict:
        if self.root is None:
            return {"capped": False}
        cap = (self.root / "memory.max").read_text().strip()
        return {
            "capped": True,
            "scope_cap_mb": int(cap) // 2**20 if cap.isdigit() else cap,
            "scope_peak_mb": peak_mb(self.root),
            "process_cap_mb": self.cap_mb,
            "per_tool": {
                t: {"runs": int(n), "seconds": round(s), "peak_mb": int(p), "oom_killed": int(k)}
                for t, (n, s, p, k) in sorted(self.stats.items())
            },
        }


CGROUPS = Cgroups()
# Process groups running now, so a signal to the scorer stops them too, and the tools/binding.py processes
# whose scopes have to go with them.
LIVE: dict[int, str] = {}
LIVE_LOCK = threading.Lock()
# Runs a command in the cgroup given first, if any, with no core dump, and first in line for the OOM killer.
WRAP = (
    "ulimit -c 0; { echo 1000 > /proc/self/oom_score_adj; } 2>/dev/null; "
    'if [ -n "$1" ] && ! echo 0 > "$1/cgroup.procs"; then echo "passes.py: no cgroup" >&2; exit 125; fi; '
    'shift; exec "$@"'
)


def kill_binding_scopes(pid: int) -> None:
    """tools/binding.py runs each process in a scope named for its own pid, which killing it leaves running.
    Call this only while that pid is still alive, so the name can't be another process's."""
    if shutil.which("systemctl"):
        subprocess.run(
            ["systemctl", "--user", "kill", "--signal=SIGKILL", f"ir-lean-binding-{pid}-*.scope"],
            capture_output=True,
            check=False,
        )


def kill_group(pid: int) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(pid, signal.SIGKILL)


@dataclass
class Ran:
    code: int
    out: str
    err: str
    # Why a limit stopped it, or None if it finished.
    limit: str | None = None


def run(
    command: list[str],
    *,
    timeout: int,
    stdin: bytes | None = None,
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
    kind: str = "",
) -> Ran:
    """Runs a command in a cgroup of its own, if there are cgroups, and its own process group, under a wall
    clock. Whatever it leaves running is killed when it exits. `limit` says if a limit stopped it."""
    cg = CGROUPS.make()
    start = time.monotonic()
    timed_out = False
    p = subprocess.Popen(
        ["/bin/sh", "-c", WRAP, "sh", str(cg or ""), *command],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        cwd=cwd,
        start_new_session=True,
    )
    with LIVE_LOCK:
        LIVE[p.pid] = kind
    try:
        try:
            out, err = p.communicate(stdin, timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            if kind == "binding":
                kill_binding_scopes(p.pid)
            kill_group(p.pid)
            out, err = p.communicate()
    finally:
        kill_group(p.pid)
        with LIVE_LOCK:
            LIVE.pop(p.pid, None)
        why = CGROUPS.finish(cg, Path(command[0]).name, time.monotonic() - start) if cg else None
    text_err = err.decode(errors="replace")
    if p.returncode == 125 and "passes.py: no cgroup" in text_err:
        raise RuntimeError(f"couldn't cap {command[0]}: {text_err[-300:]}")
    limit = None
    if timed_out:
        limit = f"took more than {timeout} s"
    elif why:
        limit = why
    elif p.returncode < 0 or p.returncode == 137:
        last = next((x.strip() for x in reversed(text_err.splitlines()) if x.strip()), "")
        limit = f"signal {-p.returncode if p.returncode < 0 else 9}" + (
            f", after: {last[:120]}" if last else ""
        )
    return Ran(p.returncode, out.decode(errors="replace"), text_err, limit)


def stop_everything(signum: int, _frame: Any) -> None:
    """A signal to the scorer stops everything it started, and nothing is reported."""
    with LIVE_LOCK:
        live = dict(LIVE)
    for pid, kind in live.items():
        if kind == "binding":
            kill_binding_scopes(pid)
        kill_group(pid)
    CGROUPS.kill_all()
    os._exit(128 + signum)


# ------------------------------------------------------------------------------------------------------------
# The corpus


@dataclass(frozen=True)
class Run:
    """One RUN line of one test: the pass, its spec, -mtriple, and every other option it gave opt."""

    pass_name: str
    path: Path
    spec: str
    mtriple: str | None
    options: tuple[str, ...]


def run_commands(text: str) -> list[str]:
    """Each RUN command in a test, with lines that end in a backslash joined to the next."""
    out, cur = [], ""
    for m in RUN_LINE.finditer(text):
        line = m.group(1).rstrip()
        if line.endswith("\\"):
            cur += line[:-1] + " "
            continue
        out.append((cur + line).strip())
        cur = ""
    return out


def parse_opt(command: str) -> tuple[str, str | None, tuple[str, ...]] | None:
    """The pass spec, -mtriple and every other option of a RUN command that starts with opt and gives
    -passes=, or None. Options are kept, not dropped, so a run whose bundle can't represent one is unsupported
    rather than about another configuration."""
    head = command.split("|", 1)[0]
    try:
        words = shlex.split(head)
    except ValueError:
        return None
    if not words or words[0] != "opt":
        return None
    spec, mtriple, options = None, None, []
    i = 1
    while i < len(words):
        w = words[i]
        if w.startswith(("-passes=", "--passes=")):
            if spec is not None:
                options.append(w)
            spec = w.split("=", 1)[1]
        elif w.startswith(("-mtriple=", "--mtriple=")):
            mtriple = w.split("=", 1)[1]
        elif w in ("-mtriple", "--mtriple") and i + 1 < len(words):
            mtriple = words[i + 1]
            i += 1
        elif w == "-o" and i + 1 < len(words):
            i += 1
        elif (m := REDIRECT.fullmatch(w)) is not None:
            # A redirection with nothing after it names its file in the next word.
            i += not m.group(1)
        elif w not in IO_FLAGS:
            options.append(w)
        i += 1
    if spec is None:
        return None
    return spec, mtriple, tuple(options)


def single_pass(spec: str) -> str | None:
    """The pass a spec runs alone, maybe with parameters, or None for a pipeline: a pipeline says nothing
    about one pass alone."""
    if re.search(r"[,()]", spec.split("<")[0]) or "," in re.sub(r"<[^>]*>", "", spec):
        return None
    return spec.split("<")[0]


def ir_passes() -> list[str]:
    """Every pass the pinned opt runs by name, from the inventory tests/llvm_scope.py derives and checks."""
    items = json.loads(INVENTORY.read_text())["items"]
    return sorted(
        {
            item["name"]
            for item in items
            if "transform" in item["kinds"]
            and any(
                r["registry"] == "PassRegistry.def" and r.get("kind") == "transform"
                for r in item["registrations"]
            )
        }
    )


def corpus(known: set[str], llvm: Path, files: list[Path] | None) -> dict[str, list[Run]]:
    """For each pass, the RUN lines in llvm/test/Transforms, or in `files`, that run it alone."""
    out: dict[str, set[Run]] = {}
    paths = files if files is not None else sorted((llvm / "llvm" / "test" / "Transforms").rglob("*.ll"))
    for path in paths:
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        for command in run_commands(text):
            parsed = parse_opt(command)
            if parsed is None:
                continue
            spec, mtriple, options = parsed
            base = single_pass(spec)
            if base is None or base not in known:
                continue
            out.setdefault(base, set()).add(Run(base, path.resolve(), spec, mtriple, options))
    return {
        k: sorted(v, key=lambda r: (str(r.path), r.spec, r.mtriple or "", r.options)) for k, v in out.items()
    }


# ------------------------------------------------------------------------------------------------------------
# Instances


def func_text(ll: str, name: str) -> str | None:
    """A function's text with its attribute groups written out, so a change to its attributes counts as a
    change."""
    m = re.search(rf'^define [^@]*@"?{re.escape(name)}"?\(.*?^}}', ll, re.M | re.S)
    if not m:
        return None
    groups = dict(re.findall(r"^attributes (#\d+) = \{ (.*) \}$", ll, re.M))
    return re.sub(r"#\d+\b", lambda g: "{" + groups.get(g.group(0), g.group(0)) + "}", m.group(0))


def calls(ll: str, name: str, callee: str) -> bool:
    text = func_text(ll, name) or ""
    return re.search(rf'@"?{re.escape(callee)}"?[(\s,)]', text.split("\n", 1)[-1]) is not None


def instances(src: str, tgt: str) -> tuple[list[str], set[str]]:
    """The functions a run changed, and every function calling one, sorted. And those it added or removed."""
    names_src = DEFINE_NAME.findall(src)
    names_tgt = DEFINE_NAME.findall(tgt)
    changed = {n for n in set(names_src) | set(names_tgt) if func_text(src, n) != func_text(tgt, n)}
    grew = bool(changed)
    while grew:
        grew = False
        for n in names_src:
            if n not in changed and any(calls(src, n, c) or calls(tgt, n, c) for c in changed):
                changed.add(n)
                grew = True
    return sorted(changed), set(names_src) ^ set(names_tgt)


def noundef_arguments(ll: str, function: str) -> list[str]:
    """The arguments that aren't noundef, as tools/binding.py decides it."""
    return [
        x
        for x in B.parameters(ll, function)
        if not re.search(r"\bnoundef\b", re.sub(r'%"[^"]*"|%[-\w.$]+|"[^"]*"', "", x))
    ]


def binders(module: str, lean_name: str) -> list[tuple[str, str]] | None:
    """The arguments of a generated function, as (name, type), or None if its signature isn't found."""
    bare = lean_name.split(".")[-1]
    for m in SIGNATURE.finditer(module):
        if m.group(1) in (lean_name, bare, f"«{bare}»"):
            out = []
            for group in re.findall(r"\(([^()]*)\)", m.group(2)):
                names, _, ty = group.partition(" : ")
                out += [(n, ty.strip()) for n in names.split()]
            return out
    return None


def functions_in(module: str, ns: str) -> list[str]:
    """Every generated function in a module, and its step, for the proof to unfold."""
    out = []
    for m in SIGNATURE.finditer(module):
        out.append(f"{ns}.{m.group(1)}")
        if re.search(rf"^namespace {re.escape(m.group(1))}$", module, re.M):
            out.append(f"{ns}.{m.group(1)}.step")
    return out


AUTOMATION = """namespace {ns}.Auto

theorem run_ite {{β ρ : Type}} (step : β → Outcome (Next β ρ)) (c : Prop) [Decidable c] (a b : β) :
    run step (if c then a else b) = if c then run step a else run step b := by split <;> rfl

/-- Runs each side a block at a time, splitting at each branch, and closes each path with `bv_decide`. -/
macro "ir_exec" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [$ls,*, IRLean.noundef]
  repeat' (first
    | simp [$ls,*, llvm, llvm_val, {ns}.Auto.run_ite, IRLean.jump, IRLean.ret, IRLean.Outcome.ok,
        IRLean.Outcome.ub] at *
    | rw [IRLean.run]
    | split)
  all_goals first
    | rfl
    | bv_decide
    | (exfalso; bv_decide)))

end {ns}.Auto
"""


def certificate(
    ns: str, lean_name: str, args: list[tuple[str, str]], src_defs: list[str], tgt_defs: list[str]
) -> str:
    """A certificate for `ir_instance_equivalence`, stating the claim as tests/binding/AddZero.lean does, with
    a proof found by symbolic execution. Its type has to be exactly what tools/binding_check.lean builds; the
    proof is untrusted."""
    names = [f"x{i}" for i in range(len(args))]
    bound = " ".join(f"({n} : {ty})" for n, (_, ty) in zip(names, args, strict=True))
    applied = " ".join(names)
    src, tgt = f"{ns}.Src.{lean_name}", f"{ns}.Tgt.{lean_name}"
    claim = (
        f"{src} = {tgt} ∧\n    ∀ {bound + ' ' if bound else ''}(s : IRLean.ModelStop), "
        f"{src}{' ' + applied if applied else ''} ≠ some (.error (.model s))"
    )
    split = " <;> ".join(f"cases {n}" for n in names)
    lead = f"{split} <;> " if split else ""
    both = ", ".join(src_defs + tgt_defs)
    only = ", ".join(src_defs)
    intro_eq = f"funext {applied}\n    " if applied else ""
    return (
        f"import {ns}.Src\nimport {ns}.Tgt\n\n"
        f"/-! Written by tests/passes.py: `{lean_name}` is the same function in IRLean's semantics\n"
        "before and after the pass, and never stops the model. The proof is untrusted: tools/binding.py\n"
        "checks the type, the axioms and the kernel replay. -/\n\n"
        "open IRLean\n\nset_option linter.unusedSimpArgs false\n\n"
        + AUTOMATION.format(ns=ns)
        + f"\nset_option maxHeartbeats {HEARTBEATS} in\n"
        f"theorem {ns}.cert : {claim} := by\n"
        "  refine ⟨?_, ?_⟩\n"
        f"  · {intro_eq}{lead}ir_exec [{both}]\n"
        f"  · intro {applied + ' ' if applied else ''}s\n"
        f"    {lead}ir_exec [{only}]\n"
    )


# ------------------------------------------------------------------------------------------------------------
# The scorer


class Scorer:
    def __init__(
        self, work: Path, kind: str, timeout: int, lean_mb: int, use_cache: bool, keep: bool
    ) -> None:
        self.work = work
        self.kind = kind
        self.timeout = timeout
        self.lean_mb = lean_mb
        self.use_cache = use_cache
        self.keep = keep
        self.runs = work / "runs"
        self.bundles = work / "bundles"
        self.verdicts = work / "verdicts"
        self.binding_cache = work / "binding-cache"
        self.scratch = work / "work"
        for d in (self.runs, self.bundles, self.verdicts, self.binding_cache, self.scratch):
            d.mkdir(parents=True, exist_ok=True)
        runner = B.Runner(timeout, lean_mb)
        # Everything tools/binding.py hashes, from here, so the key changes when anything it checks does.
        self.toolchain = B.toolchain(runner)
        self.bins = dict(runner.bins)
        self.salt = sha(
            VERSION,
            canonical(self.toolchain),
            SELF.read_bytes(),
            canonical({"kind": kind, "timeout": timeout, "lean_mb": lean_mb, "heartbeats": HEARTBEATS}),
            # A cap that's enforced can stop a proof that would otherwise finish.
            repr(CGROUPS.root is not None),
        )
        self.env = {**os.environ, "ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip()}
        # IRLean alone, as tools/binding.py links it, made again each run so it's the library built now.
        library = work / "library"
        shutil.rmtree(library, ignore_errors=True)
        library.mkdir()
        for entry in B.LIBRARY.iterdir():
            if entry.name == "IRLean" or entry.name.startswith("IRLean."):
                (library / entry.name).symlink_to(entry)
        self.library = library
        self.stats = {"fresh": 0, "reused": 0, "rechecked": 0, "stale_ignored": 0}
        self.lock = threading.Lock()

    def count(self, key: str) -> None:
        with self.lock:
            self.stats[key] += 1

    def lean(self, *args: str) -> list[str]:
        return [self.bins["lean"], "-j1", "-M", str(self.lean_mb), "-s", "65536", *args]

    def opt(self, input_ll: bytes, spec: str, mtriple: str | None) -> tuple[str | None, str]:
        """What tools/binding.py's opt gives for this input, so the bundle's IR is the IR scored."""
        r = run(
            B.opt_argv(self.bins["opt"], spec, mtriple), stdin=input_ll, timeout=OPT_TIMEOUT, env=self.env
        )
        if r.limit:
            return None, f"limit: {r.limit}"
        return (r.out if r.code == 0 else None), r.err[-300:]

    # The cache ------------------------------------------------------------------------------------------

    def run_key(self, r: Run, input_ll: bytes) -> str:
        return sha(self.salt, input_ll, canonical([r.spec, r.mtriple, list(r.options)]))

    def instance_key(self, key: str, function: str) -> str:
        return sha(key, function, self.kind)[:32]

    def cached(self, key: str) -> dict | None:
        """A run's cache entry, if it's for exactly this key and well formed. Anything else is ignored."""
        path = self.runs / f"{key}.json"
        if not self.use_cache or not path.exists():
            return None
        try:
            entry = json.loads(path.read_text())
            good = (
                isinstance(entry, dict)
                and entry.get("schema") == RUN_SCHEMA
                and entry.get("key") == key
                and entry.get("salt") == self.salt
                and isinstance(entry.get("instances"), dict)
                and all(
                    isinstance(v, dict) and v.get("status") in CACHED_STATUSES
                    for v in entry["instances"].values()
                )
            )
        except (OSError, ValueError):
            good = False
        if not good:
            self.count("stale_ignored")
            return None
        return entry

    def store(self, key: str, r: Run, input_ll: bytes, found: dict) -> None:
        """Keeps a run's results, with every `bound` instance stored as a `candidate`, never as bound, and
        nothing if an instance is an error, which may not happen again."""
        insts = {}
        for n, v in found.get("instances", {}).items():
            if v["status"] == "error":
                return
            insts[n] = {**v, "status": "candidate"} if v["status"] == "bound" else v
        entry = {
            "schema": RUN_SCHEMA,
            "key": key,
            "salt": self.salt,
            "test_sha256": hashlib.sha256(input_ll).hexdigest(),
            "spec": r.spec,
            "mtriple": r.mtriple,
            "options": list(r.options),
            **({"skipped": found["skipped"]} if "skipped" in found else {}),
            "instances": insts,
        }
        tmp = self.runs / f".{key}.{uuid.uuid4().hex[:8]}"
        tmp.write_text(json.dumps(entry, indent=1, sort_keys=True))
        tmp.replace(self.runs / f"{key}.json")

    # One run ---------------------------------------------------------------------------------------------

    def score(self, r: Run) -> dict:
        """Every instance of one RUN line, each with a status, from cache where it can be."""
        input_ll = r.path.read_bytes()
        key = self.run_key(r, input_ll)
        entry = self.cached(key)
        if entry is not None:
            self.count("reused")
            out: dict = {"source": "cache", "instances": {}}
            if "skipped" in entry:
                out["skipped"] = entry["skipped"]
            for n, v in entry["instances"].items():
                if v["status"] == "candidate":
                    # Never believed: the bundle at this key is verified again, from scratch or from
                    # tools/binding.py's own cache after its hashes are checked.
                    self.count("rechecked")
                    out["instances"][n] = self.verify(
                        self.bundles / self.instance_key(key, n) / "manifest.json"
                    )
                else:
                    out["instances"][n] = v
            return out
        self.count("fresh")
        found = self.fresh(r, input_ll, key)
        self.store(key, r, input_ll, found)
        return {"source": "fresh", **found}

    def fresh(self, r: Run, input_ll: bytes, key: str) -> dict:
        if r.options:
            return {"skipped": "opt_options_unrepresentable", "options": list(r.options), "instances": {}}
        if not B.PASS_SPEC.fullmatch(r.spec) or (r.mtriple is not None and not B.TRIPLE.fullmatch(r.mtriple)):
            return {"skipped": "config_unrepresentable", "instances": {}}
        src, err = self.opt(input_ll, "verify", r.mtriple)
        if src is None:
            return {"skipped": f"opt rejects the test as input: {err[:200]}", "instances": {}}
        tgt, err = self.opt(input_ll, r.spec, r.mtriple)
        if tgt is None:
            return {"skipped": f"opt fails running the pass: {err[:200]}", "instances": {}}
        d = self.scratch / f"{key[:16]}-{uuid.uuid4().hex[:8]}"
        d.mkdir(parents=True)
        try:
            return {"instances": self.instances(src, tgt, f"P{key[:16]}", d, record=(r, key))}
        finally:
            if not self.keep:
                shutil.rmtree(d, ignore_errors=True)

    def report(self, ll: str, d: Path, side: str) -> tuple[dict[str, list[str]], dict | None]:
        """ir-lean's report on each function, by LLVM name, as tools/binding.py reads it."""
        sub = d / "ir" / side
        sub.mkdir(parents=True, exist_ok=True)
        path = sub / ("src.ll" if side == "Src" else "tgt.ll")
        path.write_text(ll)
        r = run([str(TOOL), str(path), "--report"], timeout=self.timeout, env=self.env)
        if r.limit:
            return {}, result(
                "unknown", "time_limit" if "took more" in r.limit else "resource_limit", r.limit
            )
        if r.code not in (0, 3):
            return {}, result("error", "tool_failed", f"ir-lean --report: {r.err[-300:]}")
        rows = [line.split("\t") for line in r.out.splitlines()]
        return {row[1]: row for row in rows if len(row) >= 3}, None

    def instances(self, src: str, tgt: str, ns: str, d: Path, record: tuple[Run, str] | None) -> dict:
        """Each instance's result. With `record`, a proved one is recorded as a bundle and verified."""
        changed, added_removed = instances(src, tgt)
        out: dict[str, dict] = {}
        if not changed:
            return out
        (rs, stop_s), (rt, stop_t) = self.report(src, d, "Src"), self.report(tgt, d, "Tgt")
        trusted = B.TRUSTED_PROMISES.search(tgt) is not None
        pending: dict[str, str] = {}
        for n in changed:
            if n in added_removed:
                out[n] = result("unsupported", "function_added_or_removed", "the pass added or removed it")
            elif stop_s or stop_t:
                out[n] = stop_s or stop_t or {}
            elif not FUNCTION_NAME.fullmatch(n):
                out[n] = result("unsupported", "function_name_unrepresentable", "a bundle can't name it")
            elif rs.get(n, [""])[0] != "ok" or rt.get(n, [""])[0] != "ok":
                why = (rs.get(n) or rt.get(n) or ["", "", "no report"])[2:]
                out[n] = result("unsupported", "function_unsupported", f"ir-lean leaves it out: {why}")
            elif rs[n][-1] != "pure" or rt[n][-1] != "pure":
                out[n] = result("unsupported", "memory_unsupported", "it uses memory or pointers")
            elif trusted:
                out[n] = result(
                    "unsupported", "trusted_promise", "the target IR has mustprogress or willreturn"
                )
            elif noundef_arguments(src, n):
                out[n] = result("unsupported", "undef_argument", f"{noundef_arguments(src, n)}")
            elif rs[n][2] != rt[n][2]:
                out[n] = result("unsupported", "function_unsupported", "ir-lean names it differently")
            else:
                pending[n] = rs[n][2]
        if not pending:
            return out
        if self.kind != "ir_instance_equivalence":
            # The automation proves equivalence only. Without IRLean.Refines there's no refinement claim to
            # state at all, as tools/binding.py says.
            available = (B.LIBRARY / "IRLean" / "Refine.olean").exists()
            for n in pending:
                out[n] = (
                    result("failed", "no_automation", f"nothing here proves {self.kind}")
                    if available
                    else result("unsupported", "claim_kind_unavailable", "this IRLean has no IRLean.Refines")
                )
            return out
        lean_dir = d / "lean"
        modules = {}
        for side, ll in (("Src", "src.ll"), ("Tgt", "tgt.ll")):
            target = lean_dir / ns / f"{side}.lean"
            target.parent.mkdir(parents=True, exist_ok=True)
            r = run(
                [
                    str(TOOL),
                    str(d / "ir" / side / ll),
                    "--no-code",
                    "--namespace",
                    f"{ns}.{side}",
                    "-o",
                    str(target),
                ],
                timeout=self.timeout,
                env=self.env,
                cwd=d / "ir" / side,
            )
            stop = self.stopped(r, "ir-lean")
            if stop or r.code not in (0, 3) or not target.exists():
                for n in pending:
                    out[n] = stop or result("error", "tool_failed", f"ir-lean failed on {ll}: {r.err[-300:]}")
                return out
            modules[side] = target.read_text()
            r = run(
                self.lean("-R", str(lean_dir), "-o", str(target.with_suffix(".olean")), str(target)),
                timeout=self.timeout,
                env=self.lean_env(lean_dir),
            )
            stop = self.stopped(r, f"lean on {side}")
            if stop or r.code != 0:
                for n in pending:
                    out[n] = stop or result(
                        "error", "generated_module_failed", f"{side}: {(r.out + r.err)[-300:]}"
                    )
                return out
        src_defs = functions_in(modules["Src"], f"{ns}.Src")
        tgt_defs = functions_in(modules["Tgt"], f"{ns}.Tgt")
        for n, lean_name in pending.items():
            args = binders(modules["Src"], lean_name)
            if args is None or args != binders(modules["Tgt"], lean_name):
                out[n] = result("failed", "no_automation", "its signature isn't one the automation states")
                continue
            if any(not re.fullmatch(r"Val \d+", ty) for _, ty in args):
                out[n] = result("failed", "no_automation", f"arguments of types {[t for _, t in args]}")
                continue
            cert = certificate(ns, lean_name, args, src_defs, tgt_defs)
            proved = self.prove(cert, ns, lean_dir)
            if proved is not None:
                out[n] = proved
            elif record is None:
                out[n] = result("candidate", "proved", "Lean accepts the certificate; not recorded")
            else:
                out[n] = self.bind(record[0], record[1], n, cert, ns)
        return out

    def lean_env(self, lean_dir: Path) -> dict[str, str]:
        return {**self.env, "LEAN_PATH": f"{lean_dir}:{self.library}"}

    def stopped(self, r: Ran, what: str) -> dict | None:
        """The result when a limit stopped a step: unknown, never anything else."""
        said = r.out + r.err
        if r.limit:
            reason = "time_limit" if r.limit.startswith("took more") else "resource_limit"
            return result("unknown", reason, f"{what} was stopped: {r.limit}")
        if r.code != 0 and B.LIMIT.search(said):
            return result("unknown", "resource_limit", f"{what}: {B.LIMIT.search(said).group(0)}")
        return None

    def prove(self, cert: str, ns: str, lean_dir: Path) -> dict | None:
        """None if Lean accepts the certificate. Otherwise failed, or unknown if a limit stopped it."""
        path = lean_dir / ns / "Cert.lean"
        path.write_text(cert)
        olean = path.with_suffix(".olean")
        olean.unlink(missing_ok=True)
        r = run(
            self.lean("-R", str(lean_dir), "-o", str(olean), str(path)),
            timeout=self.timeout,
            env=self.lean_env(lean_dir),
        )
        stop = self.stopped(r, "lean on the certificate")
        if stop:
            return stop
        if r.code != 0:
            m = LEAN_ERROR.search(r.out + r.err)
            return result("failed", "proof_not_found", m.group(3) if m else (r.out + r.err)[-300:])
        return None

    def bind(self, r: Run, key: str, function: str, cert: str, ns: str) -> dict:
        """Records the instance's bundle with tools/binding.py, and verifies it."""
        bundle = self.bundles / self.instance_key(key, function)
        manifest = bundle / "manifest.json"
        if not manifest.exists():
            shutil.rmtree(bundle, ignore_errors=True)
            cert_path = self.scratch / f"cert-{uuid.uuid4().hex[:12]}.lean"
            cert_path.write_text(cert)
            command = [
                sys.executable,
                str(BINDING_PY),
                "record",
                "--input",
                str(r.path),
                "--passes",
                r.spec,
                *(["--mtriple", r.mtriple] if r.mtriple else []),
                "--function",
                function,
                "--certificate",
                str(cert_path),
                "--theorem",
                f"{ns}.cert",
                "--namespace",
                ns,
                "--kind",
                self.kind,
                "--out",
                str(bundle),
                "--timeout",
                str(self.timeout),
                "--memory",
                str(self.lean_mb),
            ]
            try:
                rec = run(command, timeout=self.timeout * VERIFY_STEPS, env=self.env, kind="binding")
            finally:
                cert_path.unlink(missing_ok=True)
            if rec.limit:
                shutil.rmtree(bundle, ignore_errors=True)
                return result(
                    "unknown",
                    "time_limit" if rec.limit.startswith("took") else "resource_limit",
                    f"tools/binding.py record was stopped: {rec.limit}",
                )
            if rec.code != 0 or not manifest.exists():
                shutil.rmtree(bundle, ignore_errors=True)
                return result("error", "record_failed", rec.err[-400:])
        return self.verify(manifest)

    def verify(self, manifest: Path) -> dict:
        """The instance's status, from tools/binding.py verify in this run. Only `bound` with exit code 0, a
        verdict of the right schema about this manifest and claim kind, is bound. Anything it doesn't
        recognise is an error, never bound."""
        rel = str(manifest.relative_to(self.work)) if manifest.is_relative_to(self.work) else str(manifest)
        command = [
            sys.executable,
            str(BINDING_PY),
            "verify",
            str(manifest),
            "--cache",
            str(self.binding_cache),
            "--timeout",
            str(self.timeout),
            "--memory",
            str(self.lean_mb),
        ]
        r = run(command, timeout=self.timeout * VERIFY_STEPS, env=self.env, kind="binding")
        if r.limit:
            return result(
                "unknown",
                "time_limit" if r.limit.startswith("took") else "resource_limit",
                f"tools/binding.py verify was stopped: {r.limit}",
                bundle=rel,
            )
        try:
            verdict = json.loads(r.out)
        except ValueError:
            return result("error", "verdict_unreadable", (r.out + r.err)[-300:], bundle=rel)
        status = verdict.get("status") if isinstance(verdict, dict) else None
        if (
            status not in B.EXIT
            or verdict.get("schema") != B.VERDICT_SCHEMA
            or r.code != B.EXIT[status]
            or verdict.get("exit_code") != r.code
            or verdict.get("manifest") != str(manifest)
        ):
            return result(
                "error", "verdict_unreadable", f"exit {r.code}, verdict {str(verdict)[:300]}", bundle=rel
            )
        if status == "bound" and (verdict.get("claim") or {}).get("kind") != self.kind:
            return result(
                "error", "verdict_unreadable", "a bound verdict about another claim kind", bundle=rel
            )
        verdict_path = self.verdicts / f"{manifest.parent.name}.json"
        verdict_path.write_text(json.dumps(verdict, indent=1, ensure_ascii=False))
        return result(
            str(status),
            verdict.get("reason", ""),
            verdict.get("detail", ""),
            bundle=rel,
            verdict=str(verdict_path.relative_to(self.work)),
            binding_cache=verdict.get("cache"),
        )


# ------------------------------------------------------------------------------------------------------------
# The self-check

# Rewrites that are wrong in LLVM, each with noundef arguments so it reaches the proof. Each has to fail to
# prove, or the scorer's results mean nothing. A wrong rewrite that only stops the model, such as the freeze
# one, must fail too, since the claim says the source never stops it.
MUTANTS = [
    (
        "off by one",
        "define i8 @f(i8 noundef %x) {\n  %r = add i8 %x, 1\n  ret i8 %r\n}\n",
        "define i8 @f(i8 noundef %x) {\n  %r = add i8 %x, 2\n  ret i8 %r\n}\n",
    ),
    (
        "adds nuw",
        "define i8 @f(i8 noundef %x) {\n  %r = shl i8 %x, 1\n  ret i8 %r\n}\n",
        "define i8 @f(i8 noundef %x) {\n  %r = shl nuw i8 %x, 1\n  ret i8 %r\n}\n",
    ),
    (
        "value to poison",
        "define i8 @f(i8 noundef %x) {\n  ret i8 0\n}\n",
        "define i8 @f(i8 noundef %x) {\n  ret i8 poison\n}\n",
    ),
    (
        "adds UB",
        "define i8 @f(i8 noundef %x, i8 noundef %y) {\n  %r = add i8 %x, %y\n  ret i8 %r\n}\n",
        "define i8 @f(i8 noundef %x, i8 noundef %y) {\n  %r = udiv i8 %x, %y\n  ret i8 %r\n}\n",
    ),
    (
        "drops a guard",
        "define i8 @f(i8 noundef %x, i8 noundef %y) {\nentry:\n  %c = icmp ult i8 %x, %y\n"
        "  br i1 %c, label %a, label %b\na:\n  %s = sub nuw i8 %y, %x\n  ret i8 %s\nb:\n  ret i8 0\n}\n",
        "define i8 @f(i8 noundef %x, i8 noundef %y) {\n  %s = sub nuw i8 %y, %x\n  ret i8 %s\n}\n",
    ),
    (
        "duplicates a freeze",
        "define i8 @f(i8 noundef %x) {\n  %p = shl i8 1, %x\n  %a = freeze i8 %p\n"
        "  %r = sub i8 %a, %a\n  ret i8 %r\n}\n",
        "define i8 @f(i8 noundef %x) {\n  %p = shl i8 1, %x\n  %a = freeze i8 %p\n  %b = freeze i8 %p\n"
        "  %r = sub i8 %a, %b\n  ret i8 %r\n}\n",
    ),
    (
        "loops forever",
        "define i8 @f(i8 noundef %x) {\n  ret i8 %x\n}\n",
        "define i8 @f(i8 noundef %x) {\nentry:\n  br label %l\nl:\n  br label %l\n}\n",
    ),
]
# A right rewrite instcombine makes, which has to be bound end to end, or the mutants failing says nothing.
CONTROL = "define i8 @f(i8 noundef %x) {\n  %a = add i8 %x, 1\n  %b = sub i8 %a, 1\n  ret i8 %b\n}\n"


def mutants_passed(scorer: Scorer) -> dict | None:
    """The mutants' results from an earlier self-check with this exact salt that every mutant failed. A
    mutant's result depends only on what the salt covers, this file, Lean, IRLean and the limits, since it
    never reaches tools/binding.py. Anything else is ignored."""
    path = scorer.work / "selfcheck" / f"{scorer.salt}.json"
    if not scorer.use_cache or not path.exists():
        return None
    try:
        entry = json.loads(path.read_text())
        mutants = entry["mutants"]
        good = (
            entry.get("schema") == SELFCHECK_SCHEMA
            and entry.get("salt") == scorer.salt
            and set(mutants) == {m[0] for m in MUTANTS}
            and all(
                v.get("status") in ("failed", "unknown") and v.get("reason") != "no_automation"
                for found in mutants.values()
                for v in found.values()
            )
            and all(found for found in mutants.values())
        )
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        good = False
    return mutants if good else None


def self_check(scorer: Scorer) -> dict:
    """Each mutant's result and the control's. `ok` is false if a mutant was proved, or didn't reach the
    proof, or the control isn't bound. The control is scored and verified every time."""
    out: dict = {"mutants": {}, "ok": True, "problems": [], "mutants_from_cache": False}
    cached = mutants_passed(scorer)
    if cached is not None:
        out["mutants"], out["mutants_from_cache"] = cached, True
    for name, src, tgt in [] if cached is not None else MUTANTS:
        d = scorer.scratch / f"mutant-{uuid.uuid4().hex[:8]}"
        d.mkdir(parents=True)
        try:
            found = scorer.instances(src, tgt, "Mutant", d, record=None)
        finally:
            if not scorer.keep:
                shutil.rmtree(d, ignore_errors=True)
        statuses = sorted({v["status"] for v in found.values()})
        out["mutants"][name] = {n: {"status": v["status"], "reason": v["reason"]} for n, v in found.items()}
        # It has to fail in the proof itself: anything else, such as unsupported, would hide a wrong
        # certificate.
        if statuses not in (["failed"], ["unknown"]) or any(
            v["reason"] == "no_automation" for v in found.values()
        ):
            out["ok"] = False
            out["problems"].append(f"mutant {name!r} didn't fail to prove: {found}")
    control = scorer.work / "selfcheck" / "control.ll"
    control.parent.mkdir(parents=True, exist_ok=True)
    control.write_text(CONTROL)
    found = scorer.score(Run("instcombine", control.resolve(), "instcombine", None, ()))
    statuses = {n: v["status"] for n, v in found["instances"].items()}
    out["control"] = {
        n: {k: v[k] for k in ("status", "reason") if k in v} for n, v in found["instances"].items()
    }
    if statuses != {"f": "bound"}:
        out["ok"] = False
        out["problems"].append(f"the control isn't bound: {found}")
    if out["ok"] and cached is None:
        entry = {"schema": SELFCHECK_SCHEMA, "salt": scorer.salt, "mutants": out["mutants"]}
        (control.parent / f"{scorer.salt}.json").write_text(json.dumps(entry, indent=1, sort_keys=True))
    return out


# ------------------------------------------------------------------------------------------------------------
# The report


def tally(runs: list[tuple[Run, dict]], llvm: Path, work: Path) -> tuple[dict, list[dict]]:
    per_pass: dict[str, dict[str, int]] = {}
    reasons: dict[str, int] = {}
    records: list[dict] = []
    for r, found in runs:
        c = per_pass.setdefault(r.pass_name, {})
        try:
            test = str(r.path.relative_to(llvm))
        except ValueError:
            test = str(r.path)
        if "skipped" in found:
            k = (
                "unsupported_runs"
                if found["skipped"] in ("opt_options_unrepresentable", "config_unrepresentable")
                else "skipped_runs"
            )
            c[k] = c.get(k, 0) + 1
            reasons[f"{k}: {found['skipped'][:80]}"] = reasons.get(f"{k}: {found['skipped'][:80]}", 0) + 1
        for n, v in found.get("instances", {}).items():
            status = v["status"] if v["status"] in STATUSES else "error"
            c[status] = c.get(status, 0) + 1
            if status != "bound":
                k = f"{status}: {v.get('reason', '')}"
                reasons[k] = reasons.get(k, 0) + 1
            records.append(
                {
                    "schema": INSTANCE_SCHEMA,
                    "pass": r.pass_name,
                    "test": test,
                    "spec": r.spec,
                    "mtriple": r.mtriple,
                    "options": list(r.options),
                    "function": n,
                    "status": status,
                    "reason": v.get("reason", ""),
                    "detail": v.get("detail", ""),
                    "bundle": v.get("bundle"),
                    "verdict": v.get("verdict"),
                    "binding_cache": v.get("binding_cache"),
                    "source": found.get("source", "fresh"),
                }
            )
    return {"per_pass": per_pass, "reasons": reasons}, records


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument(
        "tool", type=Path, nargs="?", default=TOOL, help="build/ir-lean, the one tools/binding.py checks"
    )
    ap.add_argument("--only", nargs="*", default=None, metavar="PASS")
    ap.add_argument(
        "--files",
        nargs="*",
        type=Path,
        default=None,
        metavar="TEST",
        help="these test files instead of llvm/test/Transforms",
    )
    ap.add_argument(
        "--limit-files", type=int, default=0, help="at most this many runs per pass, for a quick look"
    )
    ap.add_argument("--max-runs", type=int, default=0, help="at most this many runs in all")
    ap.add_argument("--jobs", type=int, default=1, help=f"test runs at once, at most {MAX_JOBS}")
    share = round(MEMORY_SHARE * 100)
    ap.add_argument(
        "--memory",
        type=int,
        default=None,
        metavar="MB",
        help=f"cap on the whole scorer; default {share}%% of RAM, less if that isn't free",
    )
    ap.add_argument(
        "--no-scope", action="store_true", help="no systemd scope, so only each process is capped"
    )
    ap.add_argument("--timeout", type=int, default=B.DEFAULT_TIMEOUT, metavar="S", help="per process")
    ap.add_argument(
        "--lean-memory",
        type=int,
        default=B.DEFAULT_MEMORY_MB,
        metavar="MB",
        help="Lean's -M per process; each process's cgroup gets 512 MB more",
    )
    ap.add_argument("--kind", default="ir_instance_equivalence", choices=sorted(B.CHECKABLE))
    ap.add_argument("--work", type=Path, default=ROOT / "build" / "passes")
    ap.add_argument("--json", type=Path, default=None, help="default: WORK/score.json")
    ap.add_argument("--no-cache", action="store_true", help="neither read nor trust WORK/runs")
    ap.add_argument("--keep", action="store_true", help="keep each run's Lean in WORK/work")
    ap.add_argument(
        "--debug",
        nargs=3,
        metavar=("FILE", "SPEC", "TRIPLE"),
        help="score one test file with one spec, uncached, keeping its Lean; TRIPLE '' for none",
    )
    args = ap.parse_args()
    if args.tool.resolve() != TOOL.resolve():
        sys.exit(f"tools/binding.py checks {TOOL}, so the scorer uses it, not {args.tool}")
    if not 1 <= args.jobs <= MAX_JOBS:
        sys.exit(
            f"--jobs is 1 to {MAX_JOBS}: each job can hold several GB, and an uncapped run once filled RAM"
        )
    process_mb = args.lean_memory + CGROUP_SLACK_MB
    budget = args.memory or int(os.environ.get(SCOPE_ENV) or 0) or memory_budget()
    if budget < SCORER_MB + process_mb * args.jobs:
        sys.exit(
            f"only {budget} MB of memory to use; {args.jobs} job(s) need "
            f"{SCORER_MB + process_mb * args.jobs} MB"
        )
    if not args.no_scope:
        enter_scope(budget)
    signal.signal(signal.SIGTERM, stop_everything)
    signal.signal(signal.SIGINT, stop_everything)
    CGROUPS.setup(process_mb)
    print(
        f"{args.jobs} job(s), "
        + (
            f"memory capped at {budget} MB"
            if CGROUPS.root
            else f"scorer not capped; each process capped by Lean's -M {args.lean_memory} MB"
        ),
        file=sys.stderr,
    )
    llvm = Path(os.environ.get("LLVM_PROJECT_SRC", ""))
    if args.files is None and args.debug is None and not (llvm / "llvm" / "test" / "Transforms").is_dir():
        sys.exit("LLVM_PROJECT_SRC isn't the pinned llvm-project; run in nix develop")
    work = args.work.resolve()
    legacy = work / "cache"
    started = time.time()
    try:
        scorer = Scorer(
            work,
            args.kind,
            args.timeout,
            args.lean_memory,
            not args.no_cache and not args.debug,
            args.keep or bool(args.debug),
        )
    except B.Verdict as e:
        sys.exit(f"the toolchain isn't ready: {e.reason}: {e.detail}")
    if args.debug:
        f, spec, triple = args.debug
        r = Run(single_pass(spec) or spec, Path(f).resolve(), spec, triple or None, ())
        print(json.dumps(scorer.score(r), indent=1))
        return 0
    check = self_check(scorer)
    if not check["ok"]:
        print(f"UNSOUND or broken, so nothing is scored: {check['problems']}", file=sys.stderr)
        return 1
    known = set(ir_passes())
    tests = corpus(known, llvm, [p.resolve() for p in args.files] if args.files is not None else None)
    passes = args.only if args.only is not None else sorted(known)
    jobs = [r for p in passes for r in tests.get(p, [])[: args.limit_files or None]]
    if args.max_runs:
        jobs = jobs[: args.max_runs]

    def one(r: Run) -> tuple[Run, dict]:
        try:
            return r, scorer.score(r)
        except Exception as e:  # One broken test mustn't stop the rest; it's an error, never bound.
            return r, {"instances": {"?": result("error", "internal_error", f"scorer: {e!r}")}}

    done: list[tuple[Run, dict]] = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        for i, fut in enumerate(concurrent.futures.as_completed([ex.submit(one, r) for r in jobs]), 1):
            done.append(fut.result())
            if i % 50 == 0:
                print(f"  {i}/{len(jobs)} test runs, {time.time() - started:.0f} s", file=sys.stderr)
    counts, records = tally(done, llvm, work)
    per_pass = counts["per_pass"]
    blocking = ("refused", "unsupported", "failed", "unknown", "error", "unsupported_runs")
    l1 = sorted(p for p, c in per_pass.items() if c.get("bound", 0) > 0)
    l2 = sorted(p for p in l1 if all(per_pass[p].get(k, 0) == 0 for k in blocking))
    totals = {s: sum(c.get(s, 0) for c in per_pass.values()) for s in STATUSES}
    out_json = (args.json or work / "score.json").resolve()
    instances_json = out_json.with_suffix(".instances.json")
    score = {
        "schema": SCORE_SCHEMA,
        "llvm": B.llvm_pin(),
        "opt_version": scorer.toolchain["opt_version"],
        "claim": {"kind": args.kind, "means": B.KINDS[args.kind]},
        "done": 0,
        "done_reason": "A bound instance is translation validation of one run. No pass has all-input proofs "
        "of its rewrites, of its C++, or of the pipelines it's in, so none is done.",
        "inventory": {"source": str(INVENTORY.relative_to(ROOT)), "ir_passes_by_name": len(known)},
        "ladder": {"L4": 0, "L3": 0, "L2": len(l2), "L1": len(l1)},
        "L1_passes": l1,
        "L2_passes": l2,
        "instances": totals,
        "runs": len(done),
        "passes_scored": len(passes),
        "per_pass": {p: c for p, c in sorted(per_pass.items()) if c},
        "top_reasons": sorted(counts["reasons"].items(), key=lambda kv: -kv[1])[:30],
        "self_check": check,
        "cache": {**scorer.stats, "legacy_cache_ignored": legacy.is_dir()},
        "limits": {
            "jobs": args.jobs,
            "timeout_s": args.timeout,
            "lean_memory_mb": args.lean_memory,
            "process_cap_mb": process_mb,
            "heartbeats": HEARTBEATS,
            "scorer_cap_mb": budget if CGROUPS.root else None,
        },
        "memory": CGROUPS.summary(),
        "instance_records": str(instances_json),
        "seconds": round(time.time() - started),
    }
    out_json.parent.mkdir(parents=True, exist_ok=True)
    instances_json.write_text(json.dumps(records, indent=1, ensure_ascii=False))
    out_json.write_text(json.dumps(score, indent=1, ensure_ascii=False))
    print(
        f"done 0 passes | L4 0 | L3 0 | L2 {len(l2)} | L1 {len(l1)} | bound {totals['bound']} of "
        f"{sum(totals.values())} changed functions in {len(done)} runs ("
        + ", ".join(f"{s} {totals[s]}" for s in STATUSES[1:])
        + f") | {score['seconds']} s"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
