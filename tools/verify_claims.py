#!/usr/bin/env python3
"""BIND-03: an independent verifier for claims about LLVM's passes.

A claim in tests/llvm_scope/coverage.json says a pass is done along one dimension, and names its evidence. Its
status and hashes are the claimant's word. This replays the evidence and decides whether it covers the pass in
every context, and only then does tests/llvm_scope.py count the claim. See docs/verify-claims.md.

It shares no code with the scorer: not tools/verify.py, tools/binding.py, tools/irlean, or the Lean checkers
they run. It uses Python's standard library, Lean, and the tools the evidence is about: clang, llvm-extract,
ir-lean, lean and leanchecker. The evidence is replayed from the pinned llvm-project's source:

- every file of llvm-project each unit's compile reads has the SHA-256 the evidence records, and llvm-project
  has the pinned NAR hash;
- the pinned clang compiles each unit with the recorded flags to the same IR, byte for byte;
- ir-lean translates that IR to the same Lean, byte for byte;
- Lean compiles the generated modules and the evidence's own, and tools/verify_claims_check.lean reads them as
  data: each theorem is declared where the evidence says, its statement is the one the evidence records, as
  a hash of its Expr, uses only Lean's, IRLean's, the generated modules' and the model's constants, names the
  generated function it's about, and rests only on the standard axioms and bv_decide's, which are rerun;
- leanchecker replays every module that isn't Lean's or IRLean's through the kernel;
- nothing the evidence's code could change while it compiled has changed.

Each file the replay rests on is read once, by read_once, and the replay uses those bytes, never the path
again: the evidence, its Lean files, its IR, and every file of the repo clang reads, which it compiles from a
private copy. llvm-project has to be the Nix store's, which nothing changes, and the work area outside both
trees. A claim's plan is its evidence files by the SHA-256 of the bytes read, each once.

usage:
  tools/verify_claims.py evidence EVIDENCE.json [--record OUT.json] [--work DIR] [--jobs N] [--memory MB]
  tools/verify_claims.py claim [--coverage FILE] [--inventory FILE] [--closures DIR] [--index N]

`evidence` replays one evidence file and prints a verdict. With --record, it fills in the hashes and
statements it found, and writes the evidence to OUT.json, after every other check has passed. `claim` decides
each complete claim in the coverage manifest, or the one at --index. Exit codes: 0 replayed or verified, 1
refused, 2 partial, 4 unknown (a limit stopped it), 5 error.

It decides its own verdicts, and denies by default, as docs/verdicts.md says: only `complete` gives
`replayed`, when every check of REPLAYED passed exactly once over every module the evidence plans, and only
`verified` gives `verified`, when the replays are of each planned evidence file's bytes, once. Anything else
is `error`, `incomplete`, and IRLEAN_DENY_ALL, set to anything but 0, takes every grant away.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import secrets
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve()
CHECKER = HERE.parent / "verify_claims_check.lean"
EVIDENCE_SCHEMA = "ir-lean.claim-evidence/1"
VERDICT_SCHEMA = "ir-lean.claim-verdict/1"
CLOSURE_SCHEMA = "ir-lean.closure/1"
PIN = ROOT / "tests" / "llvm" / "targets.toml"
INVENTORY = ROOT / "tests" / "llvm_scope" / "inventory.json"
COVERAGE = ROOT / "tests" / "llvm_scope" / "coverage.json"
CLOSURES = ROOT / "tests" / "llvm_scope" / "closure"
REWRITES = ROOT / "tests" / "llvm_scope" / "rewrites"
# What no process without root can change: llvm-project, and every other file clang reads but the repo's.
STORE = Path("/nix/store")
EXIT = {"replayed": 0, "verified": 0, "refused": 1, "partial": 2, "unknown": 4, "error": 5}
# The grants, which only `complete` and `verified` give, and the checks a replay needs for one.
GRANTED = ("replayed", "verified")
REPLAYED = (
    "pin", "anchors", "ir_replay", "translation_replay", "compile_generated", "compile_evidence",
    "statements", "axioms", "kernel_replay", "unchanged",
)  # fmt: skip
DENY_ALL = "IRLEAN_DENY_ALL"
HEX = re.compile(r"[0-9a-f]{64}")
FLAG = re.compile(
    r"-(O[0-3sz]|D[A-Za-z_]\w*(=[\w.+-]*)?|U[A-Za-z_]\w*|std=[\w+]+|f[A-Za-z][\w=.+-]*|W[\w=-]*|m[\w=.-]+)"
)
UNSAFE_FLAGS = (
    "-fplugin", "-fpass-plugin", "-fmodule", "-fprofile", "-fcrash", "-fdebug-prefix", "-ffile-prefix",
    "-fmacro-prefix", "-fcoverage-prefix", "-fsanitize", "-mllvm",
)  # fmt: skip
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*")
# Lean's messages for running out of time, memory, stack, heartbeats or the solver's time. Hitting one says
# nothing about the evidence, so it's unknown, never refused.
LIMIT = re.compile(
    r"maximum number of heartbeats|deterministic\)? timeout|maximum recursion depth|deep recursion|"
    r"stack overflow|out of memory|excessive memory|memory limit|SAT solver timed out|resource exhausted|"
    r"not enough memory|cannot allocate memory|"
    r"maximum number of steps",
    re.IGNORECASE,
)
TRUSTED = [
    "Lean's kernel, as leanchecker runs it, and the toolchain's bv_decide checker",
    "IRLean's semantics of LLVM IR, and ir-lean's translation",
    "the pinned clang, compiling the pinned source as the shipped LLVM was compiled",
    "whoever reads each theorem's statement, and the model definitions it names, against what the claim says",
]


class Stop(Exception):
    """Ends the replay with a verdict."""

    def __init__(self, status: str, reason: str, detail: str) -> None:
        super().__init__(f"{status}: {reason}: {detail}")
        self.status, self.reason, self.detail = status, reason, detail


def refuse(reason: str, detail: str) -> Stop:
    return Stop("refused", reason, detail)


# --- Running things ---------------------------------------------------------------------------------------


@dataclass
class Ran:
    argv: list[str]
    exit: int | None
    out: str
    err: str
    timed_out: bool
    seconds: float

    @property
    def ok(self) -> bool:
        return self.exit == 0 and not self.timed_out

    def limited(self) -> bool:
        """Whether a limit, rather than the input, could explain how it ended."""
        return self.timed_out or self.exit == -signal.SIGKILL or bool(LIMIT.search(self.out + self.err))

    def text(self) -> str:
        return (self.out + self.err).strip()[-4000:]


def run(
    argv: list[str], *, cwd: Path | None = None, env: dict[str, str] | None = None, timeout: float
) -> Ran:
    """Runs a command in a session of its own, so it and whatever it starts are killed when it ends or times
    out. Output goes to files, so a process it leaves holding them can't keep this waiting."""
    started = time.monotonic()
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        p = subprocess.Popen(
            argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=out, stderr=err, start_new_session=True
        )
        timed_out = False
        try:
            p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
        finally:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(p.pid, signal.SIGKILL)
            p.wait()
        out.seek(0)
        err.seek(0)
        return Ran(
            argv,
            None if timed_out else p.returncode,
            out.read().decode("utf-8", "replace"),
            err.read().decode("utf-8", "replace"),
            timed_out,
            time.monotonic() - started,
        )


def need(r: Ran, reason: str, what: str) -> Ran:
    """A step that has to succeed: unknown if a limit stopped it, an error if it crashed, refused with
    `reason` only when it ran and ended on its own with a non-zero exit."""
    if r.ok:
        return r
    if r.limited():
        raise Stop("unknown", "limit", f"{what}: {r.text()}")
    # A signal death (other than SIGKILL, which limited() reads as a cap) or a crash / could-not-execute exit
    # code (126 and above): the tool didn't do its job, so nothing was learned about the evidence. That's an
    # error, never a refusal of the evidence.
    if r.exit is not None and (r.exit < 0 or r.exit >= 126):
        raise Stop("error", "tool_failed", f"{what} was killed (exit {r.exit}): {r.text()}")
    raise refuse(reason, f"{what}: {r.text()}")


def sha256(path: Path) -> str:
    """The hash of a file this run wrote, in its private work area. Files of the repo or llvm-project go
    through read_once."""
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def dependencies(text: str, cwd: Path) -> list[Path]:
    """The files a make rule from clang's -M or -MD lists, as clang named them, made absolute, with its
    escapes for spaces read back. Not normalized: a `..` after a symlink means what the kernel says."""
    body = text.replace("\\\n", " ").split(":", 1)[1] if ":" in text else ""
    files, word, chars = [], "", iter(body)
    for ch in chars:
        if ch == "\\":
            word += next(chars, "")
        elif ch.isspace():
            if word:
                files.append(word)
            word = ""
        else:
            word += ch
    if word:
        files.append(word)
    return [cwd / f for f in files]


def stamp(paths: list[Path]) -> dict[str, tuple[int, int, int, int]]:
    """What lstat says of every entry under each path: a process without root can't change an entry and set
    its change time back."""
    seen: dict[str, tuple[int, int, int, int]] = {}
    for top in paths:
        entries = [top]
        if top.is_dir() and not top.is_symlink():
            entries += sorted(top.rglob("*"))
        for p in entries:
            s = p.lstat()
            seen[str(p)] = (s.st_ino, s.st_size, s.st_ctime_ns, s.st_mtime_ns)
    return seen


@dataclass(frozen=True)
class Read:
    """A file's bytes, read once, and their SHA-256, which is the file's identity from then on."""

    path: Path
    data: bytes
    sha256: str


class Held:
    """The files a replay has read, by normalized path, so each path is read once for the whole replay however
    many units read it, and every unit gets the same bytes. A file reached by two paths, through a symlink, is
    read once by each: reading by the file's identity is a follow-up."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.reads: dict[Path, Read] = {}


def read_once(path: Path, tree: Path | None, reason: str, what: str, *, links: bool = True,
              status: str = "refused", held: Held | None = None) -> Read:  # fmt: skip
    """The one place this reads a file of the repo or llvm-project for what's in it, so each is read once and
    every later step uses these bytes, never the path again; with `held`, once a path for the replay. The path
    is taken as written, made absolute and normalized, and has to stay inside `tree`, as written and resolved.
    Normalizing can't change which file it names: a `..` after a symlink, which the kernel follows and
    normalizing doesn't, is refused. Without `links`, it can't be a symlink. Anything else ends the replay as
    `status`, with `reason`."""
    raw = Path(path).absolute()
    p = Path(os.path.normpath(raw))
    if tree is not None:
        top = Path(os.path.normpath(tree.absolute()))
        if not p.is_relative_to(top) or not p.resolve().is_relative_to(top.resolve()):
            raise Stop(status, reason, f"{what} isn't a path inside {tree}")
    if os.path.realpath(raw) != os.path.realpath(p):
        raise Stop(status, reason, f"{what}, as {raw}, goes through a symlink and back up with `..`")
    with held.lock if held is not None else contextlib.nullcontext():
        if held is not None and p in held.reads:
            return held.reads[p]
        flags = os.O_RDONLY | os.O_NONBLOCK | (0 if links else os.O_NOFOLLOW)
        try:
            fd = os.open(p, flags)
        except OSError as e:
            raise Stop(status, reason, f"{what} can't be read: {e.strerror}") from None
        with os.fdopen(fd, "rb") as f:
            if not stat.S_ISREG(os.fstat(f.fileno()).st_mode):
                raise Stop(status, reason, f"{what} isn't a file")
            data = f.read()
        r = Read(p, data, hashlib.sha256(data).hexdigest())
        if held is not None:
            held.reads[p] = r
        return r


def immutable(src: Path) -> Path:
    """llvm-project as the Nix store holds it, which no process without root can change, so the NAR hash
    check_pin compares and the files clang reads are the same bytes."""
    s = src.resolve()
    if not s.is_relative_to(STORE) or os.access(s, os.W_OK):
        raise Stop("error", "toolchain_missing",
                   f"LLVM_PROJECT_SRC is {s}, not read-only in {STORE}: run inside nix develop")  # fmt: skip
    return s


def outside_trees(work: Path, src: Path) -> Path:
    """Where a replay works: outside the repo and llvm-project, where nothing else working in them reaches."""
    w = work.resolve()
    for tree in (ROOT, src):
        if w.is_relative_to(tree.resolve()):
            raise Stop(
                "error", "work_in_tree", f"the work area {w} is inside {tree}: put it outside both trees"
            )
    return w


# --- The evidence -----------------------------------------------------------------------------------------

UNIT_KEYS = {
    "source", "source_in", "language", "flags", "include", "local_include", "llvm_config", "extract",
    "namespace", "translate", "anchors", "repo_files", "ir_sha256", "lean_sha256",
}  # fmt: skip
THEOREM_KEYS = {"module", "name", "about", "statement", "statement_sha256"}
EVIDENCE_KEYS = {"schema", "llvm", "lean_version", "units", "lean", "theorems", "cuts", "contexts"}


def exact(obj: Any, keys: set[str], where: str) -> None:
    if not isinstance(obj, dict) or set(obj) != keys:
        have = sorted(obj) if isinstance(obj, dict) else type(obj).__name__
        raise refuse("evidence_invalid", f"{where} needs exactly the keys {sorted(keys)}, and has {have}")


def strings(v: Any, where: str) -> list[str]:
    if not isinstance(v, list) or not all(isinstance(x, str) for x in v):
        raise refuse("evidence_invalid", f"{where} has to be a list of strings")
    return v


def relative(path: str, where: str) -> str:
    """A path inside a tree, which can't climb out of it."""
    p = Path(path)
    if not path or p.is_absolute() or ".." in p.parts:
        raise refuse("evidence_invalid", f"{where}: {path!r} isn't a path inside its tree")
    return path


def validate(ev: Any, record: bool) -> None:
    """The evidence's shape, exactly: a field nothing checks can't ride along."""
    exact(ev, EVIDENCE_KEYS, "the evidence")
    if ev["schema"] != EVIDENCE_SCHEMA:
        raise refuse("evidence_invalid", f"schema {ev['schema']!r} isn't {EVIDENCE_SCHEMA}")
    exact(ev["llvm"], {"tag", "commit", "nix_hash"}, "llvm")
    if not isinstance(ev["units"], list) or not ev["units"]:
        raise refuse("evidence_invalid", "units has to be a non-empty list")
    names = set()
    for n, u in enumerate(ev["units"]):
        exact(u, UNIT_KEYS, f"unit {n}")
        relative(u["source"], f"unit {n}'s source")
        for k in ("flags", "include", "local_include", "extract", "translate"):
            strings(u[k], f"unit {n}'s {k}")
        for f in u["flags"]:
            # Only flags that say how to compile: nothing that loads code into clang or names a file.
            if not FLAG.fullmatch(f) or f.startswith(UNSAFE_FLAGS):
                raise refuse(
                    "evidence_invalid", f"unit {n}'s flag {f!r} isn't one this verifier passes to clang"
                )
        for k in ("include", "local_include"):
            for i in u[k]:
                relative(i, f"unit {n}'s {k}")
        if u["language"] not in ("c", "c++", "ir") or not isinstance(u["llvm_config"], bool):
            raise refuse("evidence_invalid", f"unit {n}: language is c, c++ or ir, and llvm_config a boolean")
        if u["source_in"] not in ("llvm-project", "repo"):
            raise refuse("evidence_invalid", f"unit {n}: source_in is llvm-project or repo")
        compiles = u["flags"] or u["include"] or u["local_include"] or u["llvm_config"]
        if u["language"] == "ir" and (u["source_in"] != "repo" or compiles):
            raise refuse("evidence_invalid", f"unit {n}: IR is a file in the repo, and nothing compiles it")
        for k in ("anchors", "repo_files"):
            if not isinstance(u[k], dict) or not all(
                isinstance(h, str) and HEX.fullmatch(h) and relative(f, f"unit {n}'s {k}")
                for f, h in u[k].items()
            ):
                raise refuse("evidence_invalid", f"unit {n}'s {k} maps paths to SHA-256s")
        if (
            not isinstance(u["namespace"], str)
            or not MODULE.fullmatch(u["namespace"])
            or u["namespace"] in names
        ):
            raise refuse("evidence_invalid", f"unit {n}: namespace has to be a module name used once")
        names.add(u["namespace"])
        for k in ("ir_sha256", "lean_sha256"):
            if not (record and u[k] == "") and not (isinstance(u[k], str) and HEX.fullmatch(u[k])):
                raise refuse("evidence_invalid", f"unit {n}'s {k} isn't a SHA-256")
    lean = ev["lean"]
    exact(lean, {"root", "files", "model"}, "lean")
    relative(lean["root"], "lean.root")
    if not isinstance(lean["files"], dict) or not lean["files"]:
        raise refuse("evidence_invalid", "lean.files has to map modules to SHA-256s")
    for m, h in lean["files"].items():
        if (
            not MODULE.fullmatch(m)
            or m.split(".")[0] in ("Init", "Std", "Lean", "Lake", "IRLean")
            or m in names
        ):
            raise refuse("evidence_invalid", f"lean.files: {m!r} can't be the evidence's own module")
        if not (record and h == "") and not (isinstance(h, str) and HEX.fullmatch(h)):
            raise refuse("evidence_invalid", f"lean.files: {m}'s hash isn't a SHA-256")
    for m in strings(lean["model"], "lean.model"):
        if m not in lean["files"]:
            raise refuse("evidence_invalid", f"lean.model names {m}, which isn't in lean.files")
    if not isinstance(ev["theorems"], list) or not ev["theorems"]:
        raise refuse("evidence_invalid", "theorems has to be a non-empty list")
    theorem_names: set[str] = set()
    for n, t in enumerate(ev["theorems"]):
        exact(t, THEOREM_KEYS, f"theorem {n}")
        # Each theorem is checked once, and its answer can't stand for another entry's.
        if t["name"] in theorem_names:
            raise refuse("evidence_invalid", f"theorem {n}, {t['name']}, is listed twice")
        theorem_names.add(t["name"])
        if t["module"] not in lean["files"]:
            raise refuse("evidence_invalid", f"theorem {n}'s module has to be one of lean.files")
        if not strings(t["about"], f"theorem {n}'s about"):
            raise refuse("evidence_invalid", f"theorem {n} has to be about at least one generated function")
        if not isinstance(t["name"], str) or not isinstance(t["statement"], str):
            raise refuse("evidence_invalid", f"theorem {n}'s name and statement are strings")
        if not (record and t["statement_sha256"] == "") and not HEX.fullmatch(str(t["statement_sha256"])):
            raise refuse("evidence_invalid", f"theorem {n}'s statement_sha256 isn't a SHA-256")
    strings(ev["cuts"], "cuts")
    if ev["contexts"] != "all" and not (isinstance(ev["contexts"], list) and ev["contexts"]):
        raise refuse("evidence_invalid", 'contexts is "all" or a non-empty list')


# --- Replaying it -----------------------------------------------------------------------------------------


@dataclass
class Tools:
    src: Path
    irlean_tool: Path
    irlean_lib: Path
    toolchain: Path
    lean_version: str
    proof_cflags: list[str]

    @property
    def lean(self) -> str:
        # By absolute path, not elan's shim, so what runs is the toolchain that was stamped.
        return str(self.toolchain / "bin" / "lean")

    @property
    def leanchecker(self) -> str:
        return str(self.toolchain / "bin" / "leanchecker")


def pinned() -> dict[str, str]:
    """The pin, read once for each decision, which passes it down."""
    data = read_once(PIN, ROOT, "toolchain_missing", str(PIN.relative_to(ROOT)), status="error").data
    project = tomllib.loads(data.decode())["project"]
    return {k: project[k] for k in ("tag", "commit", "nix_hash")}


def tools(timeout: float) -> Tools:
    for t in ("clang", "llvm-extract", "llvm-config", "lean", "nix"):
        if shutil.which(t) is None:
            raise Stop("error", "toolchain_missing", f"{t} isn't on PATH: run inside nix develop")
    src = os.environ.get("LLVM_PROJECT_SRC")
    if not src or not Path(src).is_dir():
        raise Stop("error", "toolchain_missing", "LLVM_PROJECT_SRC isn't set: run inside nix develop")
    store = immutable(Path(src))
    tool = ROOT / "build" / "ir-lean"
    lib = ROOT / ".lake" / "build" / "lib" / "lean"
    if not tool.is_file() or not (lib / "IRLean.olean").is_file():
        raise Stop("error", "toolchain_missing", "build build/ir-lean and run lake build IRLean first")
    prefix = need(
        run(["lean", "--print-prefix"], cwd=ROOT, timeout=timeout), "toolchain_missing", "lean --print-prefix"
    )
    toolchain = Path(prefix.out.strip()).resolve()
    version = need(
        run([str(toolchain / "bin" / "lean"), "--version"], timeout=timeout), "toolchain_missing", "lean"
    )
    return Tools(
        store,
        tool,
        lib.resolve(),
        toolchain,
        version.out.strip().splitlines()[0],
        os.environ.get("PROOF_CFLAGS", "").split(),
    )


def check_pin(ev: dict[str, Any], t: Tools, timeout: float, pin: dict[str, str]) -> None:
    if ev["llvm"] != pin:
        raise refuse("stale_anchors", f"the evidence is for llvm-project {ev['llvm']}, the pin is {pin}")
    got = need(
        run(["nix", "hash", "path", str(t.src)], timeout=timeout), "llvm_pin_mismatch", "nix hash path"
    )
    if got.out.strip() != pin["nix_hash"]:
        raise refuse(
            "llvm_pin_mismatch", f"LLVM_PROJECT_SRC hashes to {got.out.strip()}, not {pin['nix_hash']}"
        )


class Replay:
    def __init__(self, ev: dict[str, Any], t: Tools, work: Path, jobs: int, memory: int, timeout: float,
                 record: bool, validated: dict[str, Any]) -> None:  # fmt: skip
        self.ev, self.t, self.work, self.jobs, self.memory, self.timeout = ev, t, work, jobs, memory, timeout
        self.record = record
        self.checks: list[dict[str, str]] = []
        # The modules each check over modules has to cover, each once, from the evidence before anything ran,
        # and those it did cover.
        generated, own = [u["namespace"] for u in validated["units"]], list(validated["lean"]["files"])
        self.plan = {
            "compile_generated": generated,
            "compile_evidence": own,
            "kernel_replay": generated + own,
        }
        self.observed: dict[str, list[str]] = {step: [] for step in self.plan}
        self.held = Held()  # every file of the repo or llvm-project this replay read, each once
        # Lean's memory limit, and a thread stack of 64 MB, as tests/llvm.py gives it: Lean commits about
        # 1 GiB of stack for each thread, and bv_decide forks Lean to start its solver, which fails with
        # ENOMEM on a machine with less memory than that commit, such as a CI runner.
        self.limits = ["-M", str(memory), "-s", "65536"]
        # For each theorem, which unit's function each symbol it's about is.
        self.covers: dict[str, list[dict[str, str]]] = {}
        # LEAN_SYSROOT, so leanchecker finds the stamped toolchain rather than asking elan.
        self.lean_env = {
            **os.environ,
            "LEAN_PATH": f"{work}:{t.irlean_lib}",
            "LEAN_SYSROOT": str(t.toolchain),
        }

    def passed(self, name: str, detail: str = "") -> None:
        self.checks.append({"name": name, "result": "pass", "detail": detail})

    def same(self, got: str, recorded: str, reason: str, what: str) -> str:
        """Compares a hash with the evidence's, or records it."""
        if self.record:
            return got
        if got != recorded:
            raise refuse(reason, f"{what} is {got}, and the evidence records {recorded}")
        return recorded

    def pool(self) -> ThreadPoolExecutor:
        return ThreadPoolExecutor(max(1, self.jobs))

    # Sources and IR -----------------------------------------------------------------------------------------

    def clang(self, u: dict[str, Any], in_llvm: bool, repo: Path) -> list[str]:
        """clang's command for a unit, up to what it writes and the source, with the repo's include
        directories under `repo`: the repo itself, or this run's copy of it."""
        cflags = self.t.proof_cflags
        if u["language"] == "c++":
            # The C++ library's headers find the C library's with #include_next, so those come after.
            cflags = ["-idirafter" if f == "-isystem" else f for f in cflags]
        includes = [i if in_llvm else str(self.t.src / i) for i in u["include"]]
        argv = ["clang", *cflags, *u["flags"], *[f"-I{i}" for i in includes]]
        argv += [f"-I{repo / i}" for i in u["local_include"]]
        if u["llvm_config"]:
            inc = need(
                run(["llvm-config", "--includedir"], timeout=self.timeout), "toolchain_missing", "llvm-config"
            )
            argv.append(f"-I{inc.out.strip()}")
        return [*argv, "-x", "c++" if u["language"] == "c++" else "c"]

    def compile_source(self, u: dict[str, Any], compiled: Path) -> tuple[dict[str, str], dict[str, str]]:
        """Compiles a unit's source with clang from what's held still: every file of the repo it reads, read
        once and written into a private copy of the repo, and llvm-project's, in the Nix store. Returns the
        hashes of exactly what clang read, llvm-project's files and the repo's.

        `clang -M` lists the files first, from the real trees. Then the compile, from the copy, has to read
        each file of the repo listed, and nothing but those and the Nix store's: else the trees changed in
        between, and it's `error`, `artifacts_modified`."""
        ns, in_llvm = u["namespace"], u["source_in"] == "llvm-project"
        copy = self.work.parent / "src" / ns  # one for each unit, since units are built at once
        argv = self.clang(u, in_llvm, ROOT)
        found = self.work / f"{ns}.found.d"
        # From the source's own tree, with the source named relative to it, so the IR names no machine's path.
        need(run([*argv, "-M", "-MF", str(found), u["source"]], cwd=self.t.src if in_llvm else ROOT,
                 timeout=self.timeout), "ir_replay_mismatch", f"clang -M {u['source']}")  # fmt: skip
        repo: dict[str, str] = {}
        for i in u["local_include"]:
            (copy / i).mkdir(parents=True, exist_ok=True)
        for d in dependencies(found.read_text(), self.t.src if in_llvm else ROOT):
            if Path(os.path.normpath(d)).is_relative_to(ROOT):
                r = read_once(d, ROOT, "stale_evidence", f"a file {u['source']} reads", held=self.held)
                rel = str(r.path.relative_to(ROOT))
                # Every directory the path as clang named it goes through, so `x/../y.h` resolves in the copy.
                tail = d.parts[len(ROOT.parts) :] if d.parts[: len(ROOT.parts)] == ROOT.parts else ()
                for n in range(1, len(tail)):
                    up = Path(os.path.normpath(ROOT.joinpath(*tail[:n])))
                    if up.is_relative_to(ROOT):
                        (copy / up.relative_to(ROOT)).mkdir(parents=True, exist_ok=True)
                (copy / rel).parent.mkdir(parents=True, exist_ok=True)
                (copy / rel).write_bytes(r.data)
                repo[rel] = r.sha256
        deps = self.work / f"{ns}.d"
        argv = [*self.clang(u, in_llvm, copy), "-S", "-emit-llvm", "-fno-discard-value-names", "-o",
                str(compiled), "-MD", "-MF", str(deps), u["source"]]  # fmt: skip
        home = self.t.src if in_llvm else copy
        need(run(argv, cwd=home, timeout=self.timeout), "ir_replay_mismatch", f"clang {u['source']}")
        anchors, read = {}, set()
        for d in dependencies(deps.read_text(), home):
            # The copy has no symlinks, and the store's files are read where the kernel resolves them, which
            # is what clang read.
            plain, resolved = Path(os.path.normpath(d)), Path(os.path.realpath(d))
            if plain.is_relative_to(copy):
                read.add(str(plain.relative_to(copy)))
            elif resolved.is_relative_to(self.t.src):
                rel = str(resolved.relative_to(self.t.src))
                what = f"llvm-project's {rel}"
                anchors[rel] = read_once(resolved, self.t.src, "stale_anchors", what, held=self.held).sha256
            elif not resolved.is_relative_to(STORE):
                raise Stop("error", "artifacts_modified",
                           f"clang read {d}, neither the copy of the repo nor in {STORE}")  # fmt: skip
        if read != set(repo):
            changed = sorted(read ^ set(repo))
            raise Stop(
                "error",
                "artifacts_modified",
                f"the repo changed while {u['source']} was copied: {changed[:5]}",
            )
        return anchors, repo

    def build(self, u: dict[str, Any]) -> None:
        """Compiles one unit's source as the evidence says, takes out the functions it names, and translates
        it. Its anchors are every file of llvm-project clang read, the source and its headers, each with the
        recorded SHA-256, and no other; so are the repo's files it read."""
        home = self.t.src if u["source_in"] == "llvm-project" else ROOT
        src = (home / u["source"]).resolve()
        if not src.is_relative_to(home) or not src.is_file():
            raise refuse("stale_anchors", f"{u['source']} isn't a file in {u['source_in']}")
        ns = u["namespace"]
        compiled = self.work / f"{ns}.compiled.ll"
        if u["language"] == "ir":
            # IR written by hand, or by a run of a pass: what it says is all there is to replay.
            r = read_once(
                ROOT / u["source"], ROOT, "stale_anchors", f"{u['source']} in the repo", held=self.held
            )
            compiled.write_bytes(r.data)
            anchors, repo = {}, {str(r.path.relative_to(ROOT)): r.sha256}
        else:
            anchors, repo = self.compile_source(u, compiled)
        for got, k, why in ((anchors, "anchors", "stale_anchors"), (repo, "repo_files", "stale_evidence")):
            if self.record:
                u[k] = got
            elif got != u[k]:
                diff = sorted(f for f in got.keys() | u[k].keys() if got.get(f) != u[k].get(f))
                raise refuse(why, f"{u['source']} reads {k} other than the evidence records: {diff[:5]}")
        ll = self.work / f"{ns}.ll"
        if u["extract"]:
            argv = [
                "llvm-extract",
                *[f"--func={f}" for f in u["extract"]],
                "-S",
                "-o",
                str(ll),
                str(compiled),
            ]
            need(run(argv, timeout=self.timeout), "ir_replay_mismatch", f"llvm-extract from {u['source']}")
        else:
            shutil.copyfile(compiled, ll)
        u["ir_sha256"] = self.same(
            sha256(ll), u["ir_sha256"], "ir_replay_mismatch", f"the IR of {u['source']}"
        )
        argv = [str(self.t.irlean_tool), ll.name, "--namespace", ns, "-o", f"{ns}.lean", *u["translate"]]
        r = run(argv, cwd=self.work, timeout=self.timeout)
        if r.exit not in (0, 3):
            need(r, "translation_replay_mismatch", f"ir-lean {ll.name}")
        lean = self.work / f"{ns}.lean"
        u["lean_sha256"] = self.same(
            sha256(lean), u["lean_sha256"], "translation_replay_mismatch", f"{ns}.lean"
        )
        report = run(
            [str(self.t.irlean_tool), ll.name, "--namespace", ns, "--report"],
            cwd=self.work,
            timeout=self.timeout,
        )
        if report.exit not in (0, 3):
            need(report, "translation_replay_mismatch", f"ir-lean --report {ll.name}")
        u["_functions"] = {}
        for line in report.out.splitlines():
            f = line.split("\t")
            if len(f) >= 3 and f[0] in ("ok", "unsupported"):
                u["_functions"][f[1]] = (f[0] == "ok", f[2])

    # Lean ---------------------------------------------------------------------------------------------------

    def lean(self, *args: str) -> Ran:
        return run(
            [self.t.lean, *self.limits, *args],
            cwd=self.work,
            env=self.lean_env,
            timeout=self.timeout,
        )

    def compile(self, module: str, step: str, reason: str) -> None:
        path = module.replace(".", "/")
        need(self.lean("-R", str(self.work), "-o", f"{path}.olean", f"{path}.lean"), reason, f"lean {module}")
        self.observed[step].append(module)

    def waves(self, files: dict[str, str]) -> list[list[str]]:
        """The evidence's modules in waves, each importing only modules of earlier waves, read from the import
        lines at the top of each file."""
        imports = {}
        for m in files:
            text = (self.work / f"{m.replace('.', '/')}.lean").read_text(encoding="utf-8", errors="replace")
            imports[m] = {i for i in re.findall(r"^import\s+(\S+)", text, re.M) if i in files}
        done: set[str] = set()
        waves = []
        while len(done) < len(files):
            wave = sorted(m for m in files if m not in done and imports[m] <= done)
            if not wave:
                raise refuse(
                    "evidence_invalid",
                    f"the evidence's modules import each other in a cycle: {sorted(set(files) - done)}",
                )
            waves.append(wave)
            done |= set(wave)
        return waves

    def replay(self) -> list[dict[str, Any]]:
        ev = self.ev
        # Stamped before anything the evidence names runs, clang included, and compared at the end.
        before = stamp([self.t.irlean_lib, self.t.toolchain, HERE, CHECKER, self.t.irlean_tool])
        with self.pool() as pool:
            list(pool.map(self.build, ev["units"]))
        self.passed(
            "anchors",
            f"every file of llvm-project the {len(ev['units'])} units read has the recorded SHA-256",
        )
        self.passed("ir_replay", "clang gives the recorded IR, byte for byte")
        self.passed("translation_replay", "ir-lean gives the recorded Lean, byte for byte")
        generated = [u["namespace"] for u in ev["units"]]
        with self.pool() as pool:
            list(
                pool.map(lambda m: self.compile(m, "compile_generated", "generated_module_failed"), generated)
            )
        self.passed("compile_generated", "Lean compiles every generated module")

        # The evidence's own modules, read once from the repo, with the recorded hashes. Their code runs while
        # they compile, so everything a check reads is stamped first, and compared at the end.
        root = (ROOT / ev["lean"]["root"]).resolve()
        if not root.is_relative_to(ROOT) or not root.is_dir():
            raise refuse("evidence_invalid", f"lean.root {ev['lean']['root']} isn't a directory here")
        for m, h in ev["lean"]["files"].items():
            what = f"{m}.lean under {ev['lean']['root']}"
            path = root / f"{m.replace('.', '/')}.lean"
            r = read_once(path, root, "evidence_invalid", what, links=False, held=self.held)
            ev["lean"]["files"][m] = self.same(r.sha256, h, "stale_evidence", f"{m}.lean")
            dest = self.work / f"{m.replace('.', '/')}.lean"
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(r.data)
        before_files = self.hashes()
        for wave in self.waves(ev["lean"]["files"]):
            with self.pool() as pool:
                list(pool.map(lambda m: self.compile(m, "compile_evidence", "proof_compile_failed"), wave))
        self.passed("compile_evidence", "Lean compiles the evidence's modules")
        after_compile = self.hashes()
        self.unchanged(before_files, after_compile, before, expected_new=True)

        theorems = self.statements()
        self.kernel()
        self.unchanged(after_compile, self.hashes(), before, expected_new=False)
        self.passed("unchanged", "nothing a check read changed while the evidence's code could run")
        return theorems

    def hashes(self) -> dict[str, str]:
        return {
            str(p.relative_to(self.work)): ("link:" + os.readlink(p)) if p.is_symlink() else
            ("dir" if p.is_dir() else sha256(p))
            for p in sorted(self.work.rglob("*"))
        }  # fmt: skip

    def unchanged(
        self, old: dict[str, str], new: dict[str, str], stamped: dict[str, Any], expected_new: bool
    ) -> None:
        """The run's directory is what it was, apart from each evidence module's .olean, and nothing else
        changed."""
        allowed = (
            {f"{m.replace('.', '/')}.olean" for m in self.ev["lean"]["files"]} if expected_new else set()
        )
        allowed |= {str(Path(a).parent) for a in allowed if "/" in a}
        for path in sorted(old.keys() | new.keys()):
            if old.get(path) != new.get(path) and not (path in allowed and path not in old):
                raise Stop(
                    "error", "artifacts_modified", f"{path} changed while the evidence's code could run"
                )
        now = stamp([self.t.irlean_lib, self.t.toolchain, HERE, CHECKER, self.t.irlean_tool])
        if now != stamped:
            changed = sorted(k for k in now.keys() | stamped.keys() if now.get(k) != stamped.get(k))
            raise Stop("error", "artifacts_modified", f"{changed[:3]} changed while the evidence's code ran")

    def statements(self) -> list[dict[str, Any]]:
        ev = self.ev
        defined: dict[str, list[tuple[dict[str, Any], str]]] = {}
        for u in ev["units"]:
            for symbol, (ok, name) in u["_functions"].items():
                defined.setdefault(symbol, []).append((u, f"{u['namespace']}.{name}" if ok else ""))
        theorems: list[dict[str, Any]] = []
        for t in ev["theorems"]:
            about = []
            for symbol in t["about"]:
                if symbol not in defined:
                    raise refuse("not_about_target", f"no unit's IR defines @{symbol}")
                if len(defined[symbol]) > 1:
                    # Which unit's function a theorem is about has to be plain, or a stand-in could cover
                    # another.
                    where = [u["source"] for u, _ in defined[symbol]]
                    raise refuse("evidence_invalid", f"@{symbol} is defined in more than one unit: {where}")
                u, name = defined[symbol][0]
                if not name:
                    raise refuse("function_unsupported", f"ir-lean leaves @{symbol} out")
                about.append(name)
                self.covers.setdefault(t["name"], []).append(
                    {"symbol": symbol, "source": u["source"], "source_in": u["source_in"]}
                )
            theorems.append({"module": t["module"], "name": t["name"], "about": about})
        by_module: dict[str, list[dict[str, Any]]] = {}
        for t in theorems:
            by_module.setdefault(t["module"], []).append(t)
        # One process for each module, since two modules can each define the same auxiliary constant, as
        # bv_decide's enum handling does, and then no environment can hold both.
        modules = sorted(by_module)
        with self.pool() as pool:
            answers = list(pool.map(lambda m: self.ask(m, by_module[m]), modules))
        got = {(m, a["theorem"]): a for m, batch in zip(modules, answers, strict=True) for a in batch}
        out = []
        for t in ev["theorems"]:
            a = got.get((t["module"], t["name"]))
            if a is None:
                raise Stop("error", "checker_failed", f"no answer about {t['name']}")
            if not a["ok"]:
                raise refuse(a["reason"], a["detail"])
            digest = hashlib.sha256(a["canonical"].encode()).hexdigest()
            t["statement_sha256"] = self.same(
                digest, t["statement_sha256"], "statement_mismatch", f"{t['name']}'s statement"
            )
            if self.record:
                t["statement"] = a["statement"]
            elif a["statement"] != t["statement"]:
                raise refuse(
                    "statement_mismatch",
                    f"{t['name']} prints as {a['statement']!r}, not as the evidence says",
                )
            out.append({"name": t["name"], "statement": a["statement"], "statement_sha256": digest,
                        "axioms": a["axioms"], "model_constants": a["names"],
                        "covers": self.covers[t["name"]]})  # fmt: skip
        self.passed(
            "statements",
            f"{len(out)} theorems state what the evidence records, about the generated functions",
        )
        self.passed("axioms", "every theorem rests only on the standard axioms and bv_decide's, rerun")
        return out

    def ask(self, module: str, theorems: list[dict[str, Any]]) -> list[dict[str, Any]]:
        """What tools/verify_claims_check.lean says of a module's theorems, reading it and its imports as
        data."""
        nonce = secrets.token_hex(16)
        config = self.work.parent / f"{self.work.name}.{module}.check.json"
        config.write_text(json.dumps({
            "nonce": nonce, "modules": [module], "generated": [u["namespace"] for u in self.ev["units"]],
            "model": self.ev["lean"]["model"], "theorems": theorems, "run_dir": str(self.work.resolve()),
            "irlean_dir": str(self.t.irlean_lib), "toolchain_dir": str(self.t.toolchain / "lib" / "lean"),
        }))  # fmt: skip
        r = run(
            [self.t.lean, *self.limits, str(CHECKER)],
            cwd=self.work.parent,
            env={**self.lean_env, "VERIFY_CLAIMS_CONFIG": str(config)},
            timeout=self.timeout,
        )
        need(r, "checker_failed", f"tools/verify_claims_check.lean on {module}")
        answers = [json.loads(line.split(" ", 2)[2]) for line in r.out.splitlines()
                   if line.startswith(f"VERIFY_CLAIMS {nonce} ")]  # fmt: skip
        if answers and answers[-1].get("reason") == "module_shadowed":
            raise refuse("module_shadowed", answers[-1]["detail"])
        if not answers or answers[-1] != {"done": True}:
            raise Stop("error", "checker_failed", f"the checker didn't finish on {module}: {r.text()}")
        return answers[:-1]

    def kernel(self) -> None:
        """leanchecker replays every module that isn't Lean's or IRLean's: the generated ones, and the
        evidence's."""
        modules = [u["namespace"] for u in self.ev["units"]] + list(self.ev["lean"]["files"])

        def check(module: str) -> None:
            # One module at a time, for the same reason as the checker.
            r = run([self.t.leanchecker, module], cwd=self.work, env=self.lean_env, timeout=self.timeout)
            need(r, "kernel_replay_failed", f"leanchecker {module}")
            self.observed["kernel_replay"].append(module)

        with self.pool() as pool:
            list(pool.map(check, modules))
        self.passed("kernel_replay", f"leanchecker replays {len(modules)} modules")


def verdict(status: str, reason: str, detail: str, **extra: Any) -> dict[str, Any]:
    """Any verdict but a grant, which only `complete` and `verified` give."""
    if status in GRANTED:
        raise ValueError(f"{status} is given only by complete and verified")
    return {"schema": VERDICT_SCHEMA, "status": status, "reason": reason, "detail": detail, **extra,
            "trusted": TRUSTED}  # fmt: skip


def deny() -> None:
    """IRLEAN_DENY_ALL, set to anything but 0, takes every grant away, as irlean.verdict's does. It's read
    here, since this shares no code with that."""
    if os.environ.get(DENY_ALL, "") not in ("", "0"):
        raise Stop("error", "denied", f"{DENY_ALL} is set, and nothing is granted")


@dataclass(frozen=True)
class Replayed:
    """What only `complete` gives: the evidence it replayed, by the SHA-256 of the bytes it was given, the
    path they were read from, for messages, and its verdict."""

    path: str
    sha256: str
    verdict: dict[str, Any]


def complete(replay: Replay, detail: str, *, path: str = "", digest: str = "", **extra: Any) -> Replayed:
    """The one place a replay is `replayed`: every check of REPLAYED passed exactly once, and Lean compiled
    and leanchecker replayed every module the evidence planned, each once. Anything else is `error`,
    `incomplete`, so a step skipped, by a bug here or a caller's, can't grant."""
    names = [c["name"] for c in replay.checks]
    if sorted(names) != sorted(REPLAYED):
        raise Stop("error", "incomplete", f"the checks passed are {names}, not each of {list(REPLAYED)} once")
    for step, plan in replay.plan.items():
        if sorted(replay.observed[step]) != sorted(plan):
            got = replay.observed[step]
            raise Stop("error", "incomplete", f"{step} covered {got}, not each of {plan} once")
    deny()
    v = {"schema": VERDICT_SCHEMA, "status": "replayed", "reason": "replayed", "detail": detail,
         "checks": replay.checks, **extra, "trusted": TRUSTED}  # fmt: skip
    return Replayed(path, digest, v)


def verified(results: list[Any], planned: list[Read], detail: str) -> dict[str, Any]:
    """The one place a claim is `verified`. The plan is the evidence files the claim names, each read once,
    by the hash of those bytes, and none twice; and `complete`'s results are of exactly those bytes, each
    once, and of no others. Else `error`, `incomplete`."""
    want = [p.sha256 for p in planned if isinstance(p, Read)]
    done = [r for r in results if isinstance(r, Replayed)]
    if (not want or len(want) != len(planned) or len(set(want)) != len(want) or len(done) != len(results)
            or sorted(r.sha256 for r in done) != sorted(want)):  # fmt: skip
        planned_ = [f"{p.path.name} {p.sha256[:12]}" if isinstance(p, Read) else repr(p) for p in planned]
        replayed_ = [f"{r.path} {r.sha256[:12]}" for r in done]
        raise Stop("error", "incomplete", f"{planned_} are planned, and complete replayed {replayed_}")
    deny()
    return {"schema": VERDICT_SCHEMA, "status": "verified", "reason": "verified", "detail": detail,
            "evidence": [r.verdict for r in done], "trusted": TRUSTED}  # fmt: skip


def replay_evidence(data: bytes, *, path: str = "", work: Path | None = None, jobs: int = 4,
                    memory: int = 4000, timeout: float = 900, record: bool = False,
                    pin: dict[str, str] | None = None) -> tuple[Replayed | dict[str, Any], Any]:  # fmt: skip
    """Replays evidence, given as the bytes of its file, read once. Returns the verdict, and the evidence as
    parsed from those bytes, with what's recorded. `pin` is the decision's, read once; by default, it's read
    here. The work area is a fresh directory in `work`, or in the system's, outside both trees."""
    if not isinstance(data, bytes):
        raise TypeError("replay_evidence takes the bytes of the evidence file, as read once")
    replay: Replay | None = None
    ev: Any = None
    top: Path | None = None
    try:
        try:
            ev = json.loads(data)
        except (UnicodeDecodeError, json.JSONDecodeError) as err:
            raise refuse("evidence_invalid", f"the evidence isn't JSON: {err}") from None
        validate(ev, record)
        validated = json.loads(data)  # the evidence as validated, before any tool runs
        if ev["cuts"]:
            # A call the theorem rules out by stopping the model says nothing about the code it runs.
            return verdict("partial", "cut", f"calls out of the code are cut: {ev['cuts']}"), ev
        t = tools(timeout)
        if ev["lean_version"] != t.lean_version and not record:
            raise refuse(
                "toolchain_mismatch",
                f"the evidence is for {ev['lean_version']!r}, and lean is {t.lean_version!r}",
            )
        ev["lean_version"] = t.lean_version
        check_pin(ev, t, timeout, pin if pin is not None else pinned())
        area = outside_trees(work if work is not None else Path(tempfile.gettempdir()), t.src)
        top = Path(tempfile.mkdtemp(prefix="verify-claims-", dir=area))
        run_dir = top / "run"
        run_dir.mkdir()
        replay = Replay(ev, t, run_dir, jobs, memory, timeout, record, validated)
        replay.passed("pin", "llvm-project has the pinned NAR hash")
        theorems = replay.replay()
        for u in ev["units"]:
            u.pop("_functions", None)
        detail = "every check passed" + (", and the evidence is recorded" if record else "")
        digest = hashlib.sha256(data).hexdigest()
        return complete(
            replay, detail, path=path, digest=digest, theorems=theorems, contexts=ev["contexts"]
        ), ev
    except Stop as s:
        return verdict(s.status, s.reason, s.detail, checks=replay.checks if replay else []), ev
    except Exception as e:
        return verdict("error", "internal_error", f"{type(e).__name__}: {e}"), ev
    finally:
        if top is not None and work is None:
            shutil.rmtree(top, ignore_errors=True)


# --- Claims ---------------------------------------------------------------------------------------------

NEEDS = {
    "code-binding": "binding-check",
    "all-input": "lean-proof",
    "analysis-soundness": "lean-proof",
    "composition": "composition-proof",
}


def decide_claim(
    claim: dict[str, Any],
    *,
    root: Path = ROOT,
    inventory: Path = INVENTORY,
    closures: Path = CLOSURES,
    replay_options: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Whether a claim is done along its dimension: its evidence replays, and covers the pass in every
    context."""
    try:
        return _decide_claim(claim, root, inventory, closures, replay_options or {})
    except Stop as s:
        return verdict(s.status, s.reason, s.detail)
    except Exception as e:
        return verdict("error", "internal_error", f"{type(e).__name__}: {e}")


def _decide_claim(claim: dict[str, Any], root: Path, inventory: Path, closures: Path,
                  options: dict[str, Any]) -> dict[str, Any]:  # fmt: skip
    if not isinstance(claim, dict) or not {"item", "dimension", "status", "contexts", "evidence"} <= set(
        claim
    ):
        raise refuse("claim_invalid", "a claim needs item, dimension, status, contexts and evidence")
    item_id, dim = claim["item"], claim["dimension"]
    if claim["status"] != "complete":
        raise refuse("not_complete", f"the claim is {claim['status']!r}, and only complete claims count")
    if claim["contexts"] != "all":
        raise refuse(
            "contexts_uncovered",
            f"the claim covers {claim['contexts']}, and a pass is done only in every context",
        )
    if claim.get("gaps"):
        raise refuse("gaps_listed", f"the claim lists gaps: {claim['gaps']}")
    if dim not in NEEDS:
        raise refuse(
            "dimension_unverifiable", f"{dim!r} is never done by itself: finite evidence isn't proof"
        )
    pin = pinned()  # once for the decision
    inv = json.loads(read_once(inventory, None, "internal_error", str(inventory), status="error").data)
    items = {i["id"]: i for i in inv["items"]}
    item = items.get(item_id)
    if item is None:
        raise refuse("claim_invalid", f"{item_id} isn't in the inventory")
    if inv["pin"]["tag"] != pin["tag"]:
        raise refuse(
            "stale_anchors", f"the inventory is for {inv['pin']['tag']}, and the pin is {pin['tag']}"
        )
    pass_name = item_id.removeprefix("pass:")
    # What the claim has to cover, which only a task that isn't done yet can say for these dimensions.
    if dim in ("all-input", "analysis-soundness") and not (REWRITES / f"{pass_name}.json").is_file():
        why = f"nothing lists {pass_name}'s rewrites (INV-04), so no evidence can be shown to cover them all"
        raise refuse("coverage_undecidable", why)
    if dim == "all-input" or dim == "analysis-soundness":
        raise refuse("coverage_undecidable", "this verifier doesn't read INV-04's rewrite lists yet")
    if dim == "composition":
        why = "nothing states the pipelines' contract (PASS-05) a composition proof has to meet"
        raise refuse("coverage_undecidable", why)
    closure = None
    if dim == "code-binding":
        if claim.get("anchors") != item["anchors"]:
            raise refuse("stale_anchors", "the claim's anchors aren't the inventory's, for the pinned source")
        if item.get("unresolved_classes"):
            raise refuse(
                "coverage_undecidable", f"the inventory found no code for {item['unresolved_classes']}"
            )
        path = closures / f"{pass_name}.json"
        if not path.is_file():
            why = f"there's no closure for {pass_name} (BIND-02), so nothing says what its code can reach"
            raise refuse("coverage_undecidable", why)
        closure = json.loads(read_once(path, None, "coverage_undecidable", path.name).data)
        if closure.get("schema") != CLOSURE_SCHEMA or closure.get("complete") is not True:
            raise refuse("coverage_undecidable", f"{path.name} isn't a complete {CLOSURE_SCHEMA}")
        for f, h in closure["files"].items():
            if h != claim["anchors"].get(f, h) or item["anchors"].get(f, h) != h:
                raise refuse("stale_anchors", f"{f}'s hash in the closure isn't the inventory's")

    kind = NEEDS[dim]
    evidence = [e for e in claim["evidence"] if isinstance(e, dict) and e.get("kind") == kind]
    if not evidence:
        raise refuse("claim_invalid", f"a complete {dim} claim needs {kind} evidence")
    # The plan: each evidence file read once, before any replay, and known from then on by the hash of those
    # bytes. A file named twice, by an alias or a copy, is the claim's mistake, not a second replay.
    planned: list[Read] = []
    for e in evidence:
        name = e.get("path")
        if not isinstance(name, str) or not name:
            raise refuse("claim_invalid", f"evidence {name!r} isn't a path")
        r = read_once(root / name, root, "claim_invalid", f"evidence {name!r}")
        if r.sha256 != e.get("sha256"):
            raise refuse("stale_evidence", f"{name} changed since the claim was made")
        if any(p.sha256 == r.sha256 or p.path.resolve() == r.path.resolve() for p in planned):
            raise refuse("claim_invalid", f"{name} is evidence the claim already names")
        planned.append(r)
    covered: set[tuple[str, str]] = set()
    anchors: dict[str, str] = {}
    compiled: set[str] = set()
    results = []
    for e, r in zip(evidence, planned, strict=True):
        v, ev = replay_evidence(r.data, path=e["path"], pin=pin, **options)
        results.append(v)
        if not isinstance(v, Replayed):
            raise Stop(v["status"] if v["status"] != "partial" else "refused", v["reason"],
                       f"{e['path']}: {v['detail']}")  # fmt: skip
        if ev["contexts"] != "all":
            raise refuse("contexts_uncovered", f"{e['path']} covers only {ev['contexts']}")
        for u in ev["units"]:
            anchors.update(u["anchors"])
            if u["source_in"] == "llvm-project":
                compiled.add(u["source"])
        # A closure's function is covered by a theorem about it as compiled from its own file.
        for t in v.verdict["theorems"]:
            covered |= {(c["source"], c["symbol"]) for c in t["covers"] if c["source_in"] == "llvm-project"}
    if closure is not None:
        for f, h in closure["files"].items():
            if anchors.get(f) != h:
                raise refuse("stale_anchors", f"the evidence doesn't read {f} at the closure's hash")
        for f in {fn["file"] for fn in closure["functions"]} - compiled:
            raise refuse(
                "closure_uncovered", f"the evidence doesn't compile {f}, which the closure's code comes from"
            )
        missing = [fn["symbol"] for fn in closure["functions"] if (fn["file"], fn["symbol"]) not in covered]
        if missing:
            why = f"no theorem is about {len(missing)} functions of the closure, such as {missing[:3]}"
            raise refuse("closure_uncovered", why)
    detail = f"{len(results)} evidence files replay and cover {item_id}'s {dim}"
    return verified(results, planned, detail)


def check_claim(claim: dict[str, Any], item: dict[str, Any], contexts: set[str], root: Path) -> str | None:
    """What tests/llvm_scope.py calls for each complete claim: None to accept, or why not. It decides from
    the claim and the repo itself, and uses neither the item nor the contexts the scorer read."""
    v = decide_claim(claim, root=root)
    return None if v["status"] == "verified" else f"{v['status']}, {v['reason']}: {v['detail']}"


# --- Command line -----------------------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("evidence")
    e.add_argument("path", type=Path)
    e.add_argument("--record", type=Path)
    e.add_argument("--work", type=Path)
    c = sub.add_parser("claim")
    c.add_argument("--coverage", type=Path, default=COVERAGE)
    c.add_argument("--inventory", type=Path, default=INVENTORY)
    c.add_argument("--closures", type=Path, default=CLOSURES)
    c.add_argument("--index", type=int)
    for p in (e, c):
        p.add_argument("--jobs", type=int, default=4)
        p.add_argument("--memory", type=int, default=4000, help="Lean's -M, in MB, for each Lean process")
        p.add_argument("--timeout", type=float, default=900, help="seconds for each process")
    args = ap.parse_args()
    options = {"jobs": args.jobs, "memory": args.memory, "timeout": args.timeout}
    if args.cmd == "evidence":
        try:
            data = read_once(args.path, None, "evidence_invalid", str(args.path)).data
        except Stop as s:
            print(json.dumps(verdict(s.status, s.reason, s.detail), indent=1))
            return EXIT[s.status]
        work = args.work.resolve() if args.work else None
        if work is not None:
            work.mkdir(parents=True, exist_ok=True)
        v, recorded = replay_evidence(data, path=str(args.path), work=work, record=args.record is not None,
                                      **options)  # fmt: skip
        if args.record is not None and isinstance(v, Replayed):
            args.record.write_text(json.dumps(recorded, indent=1) + "\n")
        v = v.verdict if isinstance(v, Replayed) else v
        print(json.dumps(v, indent=1))
        return EXIT[v["status"]]
    coverage = read_once(args.coverage, None, "internal_error", str(args.coverage), status="error")
    claims = json.loads(coverage.data).get("claims", [])
    picked = [(args.index, claims[args.index])] if args.index is not None else list(enumerate(claims))
    worst = 0
    for n, claim in picked:
        if claim.get("status") != "complete" and args.index is None:
            continue
        v = decide_claim(claim, inventory=args.inventory, closures=args.closures, replay_options=options)
        print(json.dumps({"claim": n, **v}, indent=1))
        worst = max(worst, EXIT[v["status"]])
    return worst


if __name__ == "__main__":
    sys.exit(main())
