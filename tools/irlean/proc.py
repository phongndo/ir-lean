"""Running commands: under a time limit and a memory cap, with everything a command started killed at either
limit and when it ends, and with what it cost measured. Also the machine's heavy-job lock. docs/python.md says
how to use it, and docs/corpus.md how `tools/measure.py` uses it.

Every command runs in a session of its own, so it and what it starts are one process group. A limit kills the
command, every descendant with the process group and session it started, and then the command's own group: a
descendant can be in a session of its own, as every step tools/binding.py runs is, so killing one group isn't
enough. Descendants are found by parent, which only works while the command is alive, so this happens before
it's reaped. When the command ends on its own, its group is killed, and its systemd scope if it has one. A
scope holds every descendant, whatever session it's in, so with one nothing outlives the command; without one,
a descendant that started a session of its own and outlived the command isn't found.

A memory cap is kept one of three ways:

- `cap_mb`, sampled: the largest sum of `ps` RSS over the command's process group and descendants, read every
  `interval` seconds. Past the cap, the tree is killed and the result says `resource_limit`. It can overshoot
  by what the tree allocates in one interval. This is the cap on macOS, which has no cgroups and doesn't
  enforce RLIMIT_AS.
- `scope`, a systemd scope of the user's, capped with no swap, where `systemd-run --user --scope` works with
  `OOMPolicy=kill`. Past the cap the kernel kills every process in the scope at once, with SIGKILL, so a
  parent can't carry on as if a child it lost was fine, and the result says `resource_limit`. The whole scope
  is killed when the command ends too.
- `address_mb`, RLIMIT_AS, set by `/bin/sh` before it runs the command. Past it an allocation fails, rather
  than anything being killed, so what happens then is up to the program. Lean can't run under it.

Lean's own `-M`, which `irlean.lean` passes, is the cap to use per Lean process. A timeout or a cap is never a
success: `Ran.limit` says which stopped it, and `Ran.ok` is false.

Two peaks are measured, because neither is enough alone:

- `peak_process_mb` is exact. It's `ru_maxrss` from wait4(), which is the largest of the process and every
  descendant it waited for. macOS gives it in bytes and Linux in KiB, and both become MiB here.
- `peak_tree_mb` is sampled, as for `cap_mb`, and only when sampling. It's what several workers cost together.

Heavy jobs take a slot in a pool first, shared by every checkout on the machine, so they don't run out of
memory together. There are `heavy_slots()` slots, one per 3.5 GB of RAM, a Lean process's peak in the
`binding` test, at least one, or `IR_LEAN_HEAVY_SLOTS`. A job declares the memory it needs, and takes a free
slot only if what's available, less what the jobs already holding slots declared, less its need,
stays above `heavy_reserve_mb()`. Otherwise it waits. A job alone in the pool is let in whatever memory says,
as one at a time always was. What it declares is its cap too: `tools/measure.py` passes `--max-tree-rss-mb` as
both.

The pool lives in the platform's cache directory: `~/Library/Caches/ir-lean/` on macOS, and
`$XDG_CACHE_HOME/ir-lean/`, by default `~/.cache/ir-lean/`, elsewhere, as `heavy-job.slotN.lock`, with
`heavy-job.gate.lock`, held while a job decides, and `heavy-job.lock`, which each slot also holds shared, so a
checkout still on the single lock, which holds it exclusively, runs alone. `IR_LEAN_HEAVY_LOCK` moves all of
them, naming the one that's `heavy-job.lock`. Each is flock(2), which macOS and Linux both have, and released
when the process exits, however it exits.
"""

from __future__ import annotations

import contextlib
import fcntl
import json
import os
import platform
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable, Generator, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import UTC, datetime
from functools import cache
from pathlib import Path
from typing import IO, Any, ClassVar

from .schemas import MEASUREMENT

# EX_TEMPFAIL: the machine is too busy to start, which says nothing about the command.
BUSY = 75
# What `stdout` and `stderr` take to capture a stream, and `stderr` to send it to wherever stdout goes.
CAPTURE = "capture"
STDOUT = "stdout"


class _Inherit:
    def __repr__(self) -> str:
        return "proc.INHERIT"


# What `stdin` takes to give the command this process's own: an object of its own, so no text can pass for it.
INHERIT: Any = _Inherit()
# For `spawn`, which takes Popen's arguments, and its callers, so nothing else imports subprocess.
PIPE = subprocess.PIPE
DEVNULL = subprocess.DEVNULL
Popen = subprocess.Popen
TimeoutExpired = subprocess.TimeoutExpired

type Stream = str | Path | IO[Any] | int | None


def now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds")


def maxrss_mib(ru_maxrss: int) -> float:
    """`ru_maxrss` in MiB: macOS reports bytes, Linux KiB."""
    return ru_maxrss / (1 << 20) if sys.platform == "darwin" else ru_maxrss / 1024


# ------------------------------------------------------------------------------------------------------------
# What the machine has


def _sysctl(name: str) -> str | None:
    r = subprocess.run(["sysctl", "-n", name], capture_output=True, text=True, check=False)
    return r.stdout.strip() if r.returncode == 0 else None


def memory() -> dict[str, Any]:
    """What the machine has now. `available_mb` is free plus reclaimable memory, as each kernel counts it."""
    if sys.platform == "darwin":
        page = int(_sysctl("hw.pagesize") or 16384)
        vm = subprocess.run(["vm_stat"], capture_output=True, text=True, check=False).stdout
        pages = {
            m.group(1): int(m.group(2)) for m in re.finditer(r'^"?([^":]+)"?:\s+(\d+)\.', vm, re.MULTILINE)
        }
        reclaimable = sum(pages.get(k, 0) for k in ("Pages free", "Pages inactive", "Pages speculative"))
        swap = _sysctl("vm.swapusage") or ""
        used = re.search(r"used = ([\d.]+)M", swap)
        level = _sysctl("kern.memorystatus_vm_pressure_level")
        return {
            "total_mb": int(_sysctl("hw.memsize") or 0) >> 20,
            "available_mb": reclaimable * page >> 20,
            # 1 normal, 2 warning, 4 critical, as `memory_pressure` reports it.
            "pressure_level": int(level) if level else None,
            "free_percent": int(_sysctl("kern.memorystatus_level") or 0),
            "swap_used_mb": float(used.group(1)) if used else None,
            "source": "vm_stat free+inactive+speculative, kern.memorystatus_*",
        }
    info: dict[str, int] = {}
    with contextlib.suppress(OSError):
        for line in Path("/proc/meminfo").read_text().splitlines():
            key, _, rest = line.partition(":")
            info[key] = int(rest.split()[0])
    return {
        "total_mb": info.get("MemTotal", 0) >> 10,
        "available_mb": info.get("MemAvailable", 0) >> 10,
        "pressure_level": None,
        "free_percent": None,
        "swap_used_mb": (info.get("SwapTotal", 0) - info.get("SwapFree", 0)) / 1024 if info else None,
        "source": "/proc/meminfo MemAvailable",
    }


def too_busy(min_available_mb: int) -> str | None:
    """Why the machine is too busy to start something needing `min_available_mb`, or None."""
    m = memory()
    if m["pressure_level"] not in (None, 1):
        return f"memory pressure level {m['pressure_level']}, not normal"
    if m["available_mb"] < min_available_mb:
        return f"{m['available_mb']} MB available, under {min_available_mb}"
    return None


# ------------------------------------------------------------------------------------------------------------
# The heavy-job lock


def cache_dir() -> Path:
    """The platform's cache directory for ir-lean. XDG says to ignore a relative `XDG_CACHE_HOME`."""
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Caches" / "ir-lean"
    xdg = os.environ.get("XDG_CACHE_HOME", "")
    return (Path(xdg) if os.path.isabs(xdg) else Path.home() / ".cache") / "ir-lean"


def lock_path() -> Path:
    if env := os.environ.get("IR_LEAN_HEAVY_LOCK"):
        return Path(env)
    return cache_dir() / "heavy-job.lock"


# A Lean process's peak, as the `binding` test caps one: what a slot is sized for, and what a job that doesn't
# say what it needs is taken to need.
SLOT_MB = 3584


def heavy_slots(total_mb: int | None = None) -> int:
    """How many heavy jobs may run at once: `IR_LEAN_HEAVY_SLOTS`, or one per SLOT_MB of RAM, at least one."""
    if env := os.environ.get("IR_LEAN_HEAVY_SLOTS"):
        return max(1, int(env))
    total = memory()["total_mb"] if total_mb is None else total_mb
    return max(1, total // SLOT_MB)


def heavy_reserve_mb(total_mb: int | None = None) -> int:
    """Memory a job may not take: `IR_LEAN_HEAVY_RESERVE_MB`, or a tenth of RAM, at least 2 GB, for whatever
    else the machine runs."""
    if env := os.environ.get("IR_LEAN_HEAVY_RESERVE_MB"):
        return max(0, int(env))
    total = memory()["total_mb"] if total_mb is None else total_mb
    return max(2048, total // 10)


def _slot(i: int) -> Path:
    base = lock_path()
    return base.with_name(f"{base.stem}.slot{i}{base.suffix}")


def _gate() -> Path:
    base = lock_path()
    return base.with_name(f"{base.stem}.gate{base.suffix}")


def _try(fd: int, how: int) -> bool:
    try:
        fcntl.flock(fd, how | fcntl.LOCK_NB)
        return True
    except BlockingIOError:
        return False


def _holder(slot: Path) -> dict[str, Any]:
    with contextlib.suppress(OSError, ValueError):
        found = json.loads(slot.with_suffix(".holder").read_text())
        if isinstance(found, dict):
            return found
    return {}


def _declared(holder: dict[str, Any]) -> int:
    """What a slot's job declared it needs, or SLOT_MB if its holder file doesn't say."""
    need = holder.get("need_mb")
    return need if type(need) is int and need >= 0 else SLOT_MB


def _slots_on_disk() -> list[int]:
    """Every slot whose file exists, which a job using more slots than this process counts may have made."""
    base = lock_path()
    name = re.compile(rf"{re.escape(base.stem)}\.slot(\d+){re.escape(base.suffix)}")
    if not base.parent.is_dir():
        return []
    return sorted(int(m[1]) for p in base.parent.iterdir() if (m := name.fullmatch(p.name)))


def pool() -> dict[str, Any]:
    """The pool now: its slots, its reserve, what's available, and who holds each slot, every slot file there
    is included."""
    m = memory()
    slots = heavy_slots(m["total_mb"])
    held = {}
    for i in _slots_on_disk():
        path = _slot(i)
        fd = os.open(path, os.O_RDWR)
        try:
            if not _try(fd, fcntl.LOCK_EX):
                held[str(path)] = _holder(path)
        finally:
            os.close(fd)
    return {
        "slots": slots,
        "slot_mb": SLOT_MB,
        "reserve_mb": heavy_reserve_mb(m["total_mb"]),
        "total_mb": m["total_mb"],
        "available_mb": m["available_mb"],
        "held": held,
    }


@contextlib.contextmanager
def heavy_lock(label: str, wait_s: float, need_mb: float | None = None) -> Generator[Path]:
    """Holds a slot in the machine's pool of heavy jobs, for a job needing `need_mb`, or SLOT_MB if it doesn't
    say, waiting up to `wait_s` for one. Who holds a slot, and what it needs, is in a file beside it."""
    need = SLOT_MB if need_mb is None else int(need_mb)
    base = lock_path()
    base.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + wait_s
    # Every lock taken, from the moment it's taken, so none outlives a failure.
    held: list[int] = []

    def release() -> None:
        while held:
            os.close(held.pop())

    try:
        while True:
            # Only one job decides at a time, briefly, so two can't both count the same free memory.
            gate = os.open(_gate(), os.O_RDWR | os.O_CREAT, 0o644)
            try:
                fcntl.flock(gate, fcntl.LOCK_EX)
                got = _admit(label, need, held)
            finally:
                os.close(gate)
            if isinstance(got, Path):
                break
            release()
            if time.monotonic() > deadline:
                raise TimeoutError(f"no heavy-job slot in {wait_s:.0f} s: {got}")
            time.sleep(2)
        yield got
    finally:
        release()


def _admit(label: str, need: int, held: list[int]) -> Path | str:
    """With the gate held: a free slot, if the pool has room for `need`, or why not. Every lock it takes goes
    in `held` at once, and the caller releases them if it doesn't get a slot."""

    def take(path: Path) -> int:
        fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
        held.append(fd)
        return fd

    def drop(fd: int) -> None:
        held.remove(fd)
        os.close(fd)

    legacy = take(lock_path())
    if not _try(legacy, fcntl.LOCK_SH):
        who = lock_path().with_suffix(".holder")
        said = who.read_text().strip() if who.exists() else ""
        return f"{lock_path()} is held by a checkout on the single lock: {said}"
    total = memory()["total_mb"]
    slots = heavy_slots(total)
    mine: Path | None = None
    others: list[dict[str, Any]] = []
    # Every slot there is, not only this process's count of them, so a job in a slot past it still counts.
    for i in sorted(set(range(slots)) | set(_slots_on_disk())):
        path = _slot(i)
        fd = take(path)
        if not _try(fd, fcntl.LOCK_EX):
            others.append(_holder(path))
            drop(fd)
        elif mine is None and i < slots:
            mine = path
        else:
            drop(fd)
    if mine is None:
        return f"all {slots} slots are held"
    if others:
        # Each running job counts at its whole declared need, on top of what it already holds. What it holds
        # can't be read at the same moment as what's available, and a job that shrank in between could grow
        # back, so crediting it could let in too much. This sets some memory aside twice, never too little.
        reserved = sum(_declared(h) for h in others)
        free = memory()["available_mb"] - reserved
        reserve = heavy_reserve_mb(total)
        if free - need < reserve:
            return (
                f"{free} MB free with {len(others)} running jobs' {reserved} MB set aside, less {need} "
                f"needed, is under {reserve}"
            )
    mine.with_suffix(".holder").write_text(
        json.dumps({"pid": os.getpid(), "label": label, "need_mb": need, "cwd": os.getcwd(), "since": now()})
        + "\n"
    )
    return mine


# ------------------------------------------------------------------------------------------------------------
# Process trees


def tree(root: int) -> list[tuple[int, int, str]]:
    """(pid, RSS in KiB, command) for `root`'s process group and every descendant of `root`."""
    r = subprocess.run(
        ["ps", "-A", "-o", "pid=,ppid=,pgid=,rss=,comm="], capture_output=True, text=True, check=False
    )
    rows = []
    for line in r.stdout.splitlines():
        parts = line.split(None, 4)
        if len(parts) == 5 and parts[0].isdigit():
            rows.append((int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]), parts[4]))
    children: dict[int, list[int]] = {}
    for pid, ppid, *_ in rows:
        children.setdefault(ppid, []).append(pid)
    keep, stack = set(), [root]
    while stack:
        p = stack.pop()
        if p not in keep:
            keep.add(p)
            stack.extend(children.get(p, []))
    return [(pid, rss, comm) for pid, _, pgid, rss, comm in rows if pid in keep or pgid == root]


def kill_group(pgid: int) -> None:
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(pgid, signal.SIGKILL)


def kill_tree(root: int) -> None:
    """Kills `root`'s descendants, each with its process group, then `root`'s own group. A descendant can be
    in a session of its own, so killing `root`'s group isn't enough. They're found by parent, which only works
    while
    `root` is alive, so this runs before it's reaped."""
    mine = os.getpgid(0)
    for _ in range(3):
        pids = [pid for pid, _, _ in tree(root) if pid != root]
        for pid in pids:
            with contextlib.suppress(ProcessLookupError, PermissionError):
                group = os.getpgid(pid)
                if group not in (mine, root):
                    os.killpg(group, signal.SIGKILL)
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(pid, signal.SIGKILL)
        if not pids:
            break
    kill_group(root)


@cache
def scopes_work() -> bool:
    """Whether `systemd-run --user --scope` works here, with the properties a `Scope` sets, which is what one
    needs."""
    if not sys.platform.startswith("linux") or shutil.which("systemd-run") is None:
        return False
    probe = ["systemd-run", "--user", "--scope", "--quiet", *Scope.PROPERTIES, "--", "true"]
    return subprocess.run(probe, capture_output=True, check=False).returncode == 0


@dataclass(frozen=True)
class Scope:
    """A systemd scope of the user's for one command: its unit is `{prefix}-{pid}-{random}.scope`, capped at
    `memory_mb` with no swap. Running out kills everything in it at once, so no process in it can outlive the
    cap and report success. Used where `scopes_work()`, and skipped elsewhere."""

    # What every scope gets besides its cap, which the probe in scopes_work() asks for too.
    PROPERTIES: ClassVar[tuple[str, ...]] = ("--property=MemorySwapMax=0", "--property=OOMPolicy=kill")

    prefix: str
    memory_mb: int
    properties: tuple[str, ...] = ()

    def unit(self) -> str:
        return f"{self.prefix}-{os.getpid()}-{secrets.token_hex(4)}"

    def wrap(self, unit: str, argv: list[str]) -> list[str]:
        properties = [f"MemoryMax={self.memory_mb}M", *self.properties]
        return [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            f"--unit={unit}",
            *self.PROPERTIES,
            *(f"--property={p}" for p in properties),
            "--",
            *argv,
        ]


def kill_scope(unit: str) -> None:
    subprocess.run(
        ["systemctl", "--user", "kill", "--signal=SIGKILL", f"{unit}.scope"], capture_output=True, check=False
    )


# Commands running now, by pid, each with its scope's unit if it has one, so a signal handler can stop them
# all.
_LIVE: dict[int, str | None] = {}
_LIVE_LOCK = threading.Lock()


def kill_live() -> None:
    """Kills every command this process is running through `run` or `spawn`, and their scopes. For a signal
    handler, before the process exits."""
    with _LIVE_LOCK:
        live = dict(_LIVE)
    for pid, unit in live.items():
        kill_tree(pid)
        if unit is not None:
            kill_scope(unit)


# ------------------------------------------------------------------------------------------------------------
# Running a command


class Sampler(threading.Thread):
    """Reads the tree's RSS every `interval` seconds, keeping the peaks, and calls `on_cap` once past
    `cap_mb`."""

    def __init__(self, root: int, interval: float, cap_mb: float | None, on_cap: Any) -> None:
        super().__init__(daemon=True)
        self.root, self.interval, self.cap_mb, self.on_cap = root, interval, cap_mb, on_cap
        self.peak_tree_kib, self.peak_procs = 0, 0
        self.top: dict[str, float] = {}
        self.samples = 0
        self.stop = threading.Event()

    def run(self) -> None:
        while not self.stop.is_set():
            members = tree(self.root)
            total = sum(rss for _, rss, _ in members)
            self.samples += 1
            self.peak_procs = max(self.peak_procs, len(members))
            for _, rss, comm in members:
                name = Path(comm).name
                self.top[name] = max(self.top.get(name, 0.0), rss / 1024)
            self.peak_tree_kib = max(self.peak_tree_kib, total)
            if self.cap_mb is not None and total / 1024 > self.cap_mb:
                self.on_cap()
                return
            self.stop.wait(self.interval)


def _text(data: bytes) -> str:
    return data.decode(errors="replace").replace("\r\n", "\n").replace("\r", "\n")


@dataclass
class Ran:
    """How a command ended, and what it cost."""

    argv: list[str]
    # Its exit code, or minus the signal that killed it.
    exit: int
    stdout: bytes
    stderr: bytes
    seconds: float
    # `time_limit` or `resource_limit`, if one of the limits `run` enforced stopped it.
    limit: str | None = None
    peak_process_mb: float = 0.0
    user_s: float = 0.0
    sys_s: float = 0.0
    # The systemd scope it ran in, if it ran in one.
    unit: str | None = None
    # Its pid, which names nothing once it's reaped, as `run` returns: only for naming what it made, such as a
    # scope of its own.
    pid: int = 0
    # The rest only when sampling.
    peak_tree_mb: float | None = None
    peak_tree_processes: int = 0
    peak_by_command_mb: dict[str, float] = field(default_factory=dict)
    samples: int = 0

    @property
    def out(self) -> str:
        """stdout as text, as `subprocess` gives it with `text=True`: newlines as `\\n`, and anything that
        isn't UTF-8 replaced."""
        return _text(self.stdout)

    @property
    def err(self) -> str:
        return _text(self.stderr)

    @property
    def output(self) -> str:
        """Both streams, stdout first."""
        return self.out + self.err

    @property
    def signal(self) -> int | None:
        return -self.exit if self.exit < 0 else None

    @property
    def ok(self) -> bool:
        """It ended on its own, with exit code 0."""
        return self.exit == 0 and self.limit is None


def _wait(pid: int) -> tuple[int, Any] | None:
    """Waits for `pid` to exit, and leaves it to be reaped, so its pid and its group's can't be reused while
    anything still kills them. Where waitid() can't leave it, reaps it, and returns its status and usage."""
    try:
        os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
        return None
    except (AttributeError, OSError):
        _, status, usage = os.wait4(pid, 0)
        return status, usage


def _open(stream: Stream, mode: str, stack: contextlib.ExitStack) -> tuple[Any, IO[bytes] | None]:
    """What Popen takes for a stream, and the temporary file to read back if it's captured."""
    if stream == CAPTURE:
        # The stack closes it.
        captured = stack.enter_context(tempfile.TemporaryFile())  # noqa: SIM115
        return captured, captured
    if stream == STDOUT:
        return subprocess.STDOUT, None
    if isinstance(stream, Path):
        return stack.enter_context(open(stream, mode)), None
    return stream, None


def run(
    argv: Sequence[str | os.PathLike[str]],
    *,
    timeout: float | None = None,
    cap_mb: float | None = None,
    sample: bool = False,
    interval: float = 0.25,
    scope: Scope | None = None,
    address_mb: int | None = None,
    stdin: bytes | str | IO[Any] | None = None,
    stdout: Stream = CAPTURE,
    stderr: Stream = CAPTURE,
    env: Mapping[str, str] | None = None,
    cwd: str | os.PathLike[str] | None = None,
    on_start: Callable[[int], None] | None = None,
) -> Ran:
    """Runs `argv` in a session of its own until it ends, `timeout` seconds pass, or its tree passes `cap_mb`,
    and returns how it ended. Kills it and everything it started at a limit, and its group, and scope if it
    has one, when it ends. Raises FileNotFoundError or PermissionError if it can't start.

    `stdout` and `stderr` are each CAPTURE, read back into `Ran` as bytes; a path, written there; an open
    file; None, inherited; or, for `stderr`, STDOUT. Captured output goes through temporary files, not pipes,
    so the command is done when it exits, not when everything it started closes its output. `stdin` is bytes
    or text to give it, an open file, INHERIT for this process's own, or None for nothing. `sample` measures
    the tree's RSS without a cap. `env` replaces the environment if given. `Ran.unit` names the scope, if
    `scope` was asked for and systemd could make one. `on_start` is called with its pid once it has started,
    as one that keeps track of what's running needs."""
    argv = [os.fspath(a) for a in argv]
    command = argv
    if address_mb is not None:
        # RLIMIT_AS in KiB, set in the child by the shell, which needs no code to run between fork and exec.
        command = ["/bin/sh", "-c", f'ulimit -v {address_mb << 10} && exec "$@"', "sh", *command]
    unit = None
    if scope is not None and scopes_work():
        unit = scope.unit()
        command = scope.wrap(unit, command)
    started = time.monotonic()
    stopped: list[str] = []
    with contextlib.ExitStack() as stack:
        given: Any = subprocess.DEVNULL if stdin is None else stdin
        if stdin is INHERIT:
            given = None
        elif isinstance(stdin, str | bytes):
            given = stack.enter_context(tempfile.TemporaryFile())
            given.write(stdin.encode() if isinstance(stdin, str) else stdin)
            given.seek(0)
        out, out_file = _open(stdout, "wb", stack)
        err, err_file = _open(stderr, "wb", stack)
        p = subprocess.Popen(
            command,
            stdin=given,
            stdout=out,
            stderr=err,
            env=None if env is None else dict(env),
            cwd=cwd,
            start_new_session=True,
        )
        with _LIVE_LOCK:
            _LIVE[p.pid] = unit

        def kill(reason: str) -> None:
            if not stopped:
                stopped.append(reason)
            kill_tree(p.pid)

        sampler = None
        if sample or cap_mb is not None:
            sampler = Sampler(p.pid, interval, cap_mb, lambda: kill("resource_limit"))
            sampler.start()
        timer = None
        if timeout is not None:
            timer = threading.Timer(max(timeout, 0), lambda: kill("time_limit"))
            timer.daemon = True
            timer.start()
        reaped = None
        try:
            if on_start is not None:
                on_start(p.pid)
            reaped = _wait(p.pid)
        except BaseException:
            kill_tree(p.pid)
            raise
        finally:
            if timer is not None:
                timer.cancel()
                if timer.is_alive():
                    timer.join()
            if sampler is not None:
                sampler.stop.set()
                sampler.join(timeout=5)
            # Whatever it left running goes with it.
            kill_group(p.pid)
            if unit is not None:
                kill_scope(unit)
            if reaped is None:
                _, status, usage = os.wait4(p.pid, 0)
            else:
                status, usage = reaped
            with _LIVE_LOCK:
                _LIVE.pop(p.pid, None)
        p.returncode = code = os.waitstatus_to_exitcode(status)
        seconds = time.monotonic() - started
        captured = []
        for f in (out_file, err_file):
            if f is None:
                captured.append(b"")
            else:
                f.seek(0)
                captured.append(f.read())
    if not stopped and unit is not None and code == -signal.SIGKILL:
        # Nothing here killed it, so the scope did: it ran out of memory, and everything in it was killed.
        stopped.append("resource_limit")
    ran = Ran(
        argv=argv,
        exit=code,
        stdout=captured[0],
        stderr=captured[1],
        seconds=seconds,
        limit=stopped[0] if stopped else None,
        peak_process_mb=maxrss_mib(usage.ru_maxrss),
        user_s=usage.ru_utime,
        sys_s=usage.ru_stime,
        unit=unit,
        pid=p.pid,
    )
    if sampler is not None:
        ran.peak_tree_mb = sampler.peak_tree_kib / 1024
        ran.peak_tree_processes = sampler.peak_procs
        ran.peak_by_command_mb = dict(sorted(sampler.top.items(), key=lambda kv: -kv[1])[:5])
        ran.samples = sampler.samples
    return ran


def spawn(argv: Sequence[str | os.PathLike[str]], **popen: Any) -> subprocess.Popen[Any]:
    """Starts a command that talks to this process while it runs, in a session of its own, for `stop` to end.
    Takes Popen's other arguments, and STDOUT for `stderr`."""
    if popen.get("stderr") == STDOUT:
        popen["stderr"] = subprocess.STDOUT
    p = subprocess.Popen([os.fspath(a) for a in argv], start_new_session=True, **popen)
    with _LIVE_LOCK:
        _LIVE[p.pid] = None
    return p


def stop(p: subprocess.Popen[Any], grace: float = 0) -> None:
    """Ends a command `spawn` started: waits `grace` seconds for it to exit, then kills it and everything it
    started, reaps it, and closes its stdin. Whatever reads its output closes that, as a thread may still be
    reading what it wrote."""
    if grace > 0:
        with contextlib.suppress(subprocess.TimeoutExpired):
            p.wait(timeout=grace)
    if p.poll() is None:
        kill_tree(p.pid)
    kill_group(p.pid)
    p.wait()
    if p.stdin is not None:
        with contextlib.suppress(OSError):
            p.stdin.close()
    with _LIVE_LOCK:
        _LIVE.pop(p.pid, None)


def rss_mb(pid: int) -> float | None:
    """A process's resident memory now, in MiB, or None if it can't be read."""
    with contextlib.suppress(OSError, ValueError):
        if sys.platform.startswith("linux"):
            for line in Path(f"/proc/{pid}/status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) / 1024
            return None
        out = subprocess.run(
            ["ps", "-o", "rss=", "-p", str(pid)], capture_output=True, text=True, check=False
        )
        return int(out.stdout.strip()) / 1024 if out.stdout.strip() else None
    return None


# ------------------------------------------------------------------------------------------------------------
# Measuring a command


def measure(
    argv: list[str],
    *,
    label: str,
    timeout: float,
    cap_mb: float | None,
    interval: float = 0.25,
    cwd: str | None = None,
    stdin: Any = INHERIT,
    stdout: Stream = None,
    stderr: Stream = None,
) -> dict[str, Any]:
    """Runs `argv`, sampling its tree, and returns the measurement record tools/measure.py writes. The command
    reads this process's stdin unless `stdin` says otherwise, as it would run alone."""
    started = now()
    before = memory()
    r = run(
        argv,
        timeout=timeout,
        cap_mb=cap_mb,
        sample=True,
        interval=interval,
        stdin=stdin,
        stdout=stdout,
        stderr=stderr,
        cwd=cwd,
    )
    if r.limit is not None:
        outcome = r.limit
    elif r.exit == 0:
        outcome = "ok"
    else:
        outcome = "failed"
    return {
        "schema": MEASUREMENT,
        "label": label,
        "command": argv,
        "cwd": cwd or os.getcwd(),
        "started": started,
        "host": {
            "name": platform.node().split(".")[0],
            "platform": sys.platform,
            "machine": platform.machine(),
            "release": platform.release(),
            "cpus": os.cpu_count(),
        },
        "outcome": outcome,
        "exit": r.exit,
        "wall_s": round(r.seconds, 2),
        "user_s": round(r.user_s, 2),
        "sys_s": round(r.sys_s, 2),
        "peak_process_mb": round(r.peak_process_mb, 1),
        "peak_tree_mb": round(r.peak_tree_mb or 0, 1),
        "peak_tree_processes": r.peak_tree_processes,
        "peak_by_command_mb": {k: round(v, 1) for k, v in r.peak_by_command_mb.items()},
        "samples": r.samples,
        "sample_interval_s": interval,
        "limits": {"timeout_s": timeout, "max_tree_rss_mb": cap_mb},
        "memory_before": before,
        "memory_after": memory(),
    }
