#!/usr/bin/env python3
"""Runs one command under a time limit and a memory cap, and records what it cost: wall time, CPU time,
and peak resident memory, of the process and of everything it starts. docs/o1-campaign.md says how the
numbers are used.

Two peaks are kept, because neither is enough alone:

- `peak_process_mb` is exact. It's `ru_maxrss` from wait4(), which is the largest of the process and
  every descendant it waited for. macOS gives it in bytes and Linux in KiB, and both become MiB here.
- `peak_tree_mb` is sampled. It's the largest sum of `ps` RSS over the process group and its
  descendants, read every `--interval` seconds, so a shorter spike can be missed. It's what several
  workers cost together.

A cap is enforced by sampling too: when the tree's RSS passes `--max-tree-rss-mb`, the process and
every descendant, with the process groups and sessions they started, are killed, and the record says
`resource_limit`. A timeout does the same. macOS has no cgroups and doesn't enforce
RLIMIT_AS, so this is the cap there; it can overshoot by what the tree allocates in one interval. Lean's
own `-M` is the cap to use per Lean process. A timeout or a cap is never a success.

Heavy jobs take a lock first, shared by every checkout on the machine, so two campaigns don't build at
once: `~/Library/Caches/ir-lean/heavy-job.lock` on macOS, `$XDG_CACHE_HOME/ir-lean/heavy-job.lock`
elsewhere, or `IR_LEAN_HEAVY_LOCK`. It's flock(2), which macOS and Linux both have, and it's released
when the process exits, however it exits.

usage: campaign/o1/measure.py run --label L [--heavy] [--timeout S] [--max-tree-rss-mb MB] [--workers N]
                                  [--cap TEXT ...] [--min-available-mb MB] [--out FILE.jsonl] -- COMMAND ...
       campaign/o1/measure.py memory
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import json
import os
import platform
import re
import shlex
import signal
import subprocess
import sys
import threading
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

SCHEMA = "ir-lean.o1.measurement/1"
# EX_TEMPFAIL: the machine is too busy to start, which says nothing about the command.
BUSY = 75


def maxrss_mib(ru_maxrss: int) -> float:
    """`ru_maxrss` in MiB: macOS reports bytes, Linux KiB."""
    return ru_maxrss / (1 << 20) if sys.platform == "darwin" else ru_maxrss / 1024


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
    m = memory()
    if m["pressure_level"] not in (None, 1):
        return f"memory pressure level {m['pressure_level']}, not normal"
    if m["available_mb"] < min_available_mb:
        return f"{m['available_mb']} MB available, under {min_available_mb}"
    return None


def lock_path() -> Path:
    if env := os.environ.get("IR_LEAN_HEAVY_LOCK"):
        return Path(env)
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Caches" / "ir-lean" / "heavy-job.lock"
    return Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "ir-lean" / "heavy-job.lock"


@contextlib.contextmanager
def heavy_lock(label: str, wait_s: float):
    """Holds the machine's heavy-job lock, waiting up to `wait_s` for it. Who holds it is in a file
    beside it."""
    path = lock_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
    deadline = time.monotonic() + wait_s
    try:
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() > deadline:
                    holder = path.with_suffix(".holder")
                    who = holder.read_text().strip() if holder.exists() else "unknown"
                    raise TimeoutError(f"{path} is held: {who}") from None
                time.sleep(2)
        path.with_suffix(".holder").write_text(
            json.dumps({"pid": os.getpid(), "label": label, "cwd": os.getcwd(), "since": now()}) + "\n"
        )
        yield path
    finally:
        os.close(fd)


def now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds")


def _tree(root: int) -> list[tuple[int, int, str]]:
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


def kill_tree(root: int) -> None:
    """Kills `root`'s descendants, each with its process group, then `root`'s own group. A descendant can be
    in a session of its own, as every step tools/binding.py runs is, so killing `root`'s group isn't enough.
    They're found by parent, which only works while `root` is alive, so this runs before it's reaped."""
    mine = os.getpgid(0)
    for _ in range(3):
        pids = [pid for pid, _, _ in _tree(root) if pid != root]
        for pid in pids:
            with contextlib.suppress(ProcessLookupError, PermissionError):
                group = os.getpgid(pid)
                if group not in (mine, root):
                    os.killpg(group, signal.SIGKILL)
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(pid, signal.SIGKILL)
        if not pids:
            break
    with contextlib.suppress(ProcessLookupError, PermissionError):
        os.killpg(root, signal.SIGKILL)


class Sampler(threading.Thread):
    def __init__(self, root: int, interval: float, cap_mb: float | None, on_cap) -> None:
        super().__init__(daemon=True)
        self.root, self.interval, self.cap_mb, self.on_cap = root, interval, cap_mb, on_cap
        self.peak_tree_kib, self.peak_procs = 0, 0
        self.top: dict[str, float] = {}
        self.samples = 0
        self.stop = threading.Event()

    def run(self) -> None:
        while not self.stop.is_set():
            tree = _tree(self.root)
            total = sum(rss for _, rss, _ in tree)
            self.samples += 1
            self.peak_procs = max(self.peak_procs, len(tree))
            for _, rss, comm in tree:
                name = Path(comm).name
                self.top[name] = max(self.top.get(name, 0.0), rss / 1024)
            if total > self.peak_tree_kib:
                self.peak_tree_kib = total
            if self.cap_mb is not None and total / 1024 > self.cap_mb:
                self.on_cap()
                return
            self.stop.wait(self.interval)


def run(
    argv: list[str],
    *,
    label: str,
    timeout: float,
    cap_mb: float | None,
    interval: float = 0.25,
    cwd: str | None = None,
    stdin: Any = None,
    stdout: Any = None,
    stderr: Any = None,
) -> dict[str, Any]:
    """Runs `argv` in its own process group and returns its measurement record. Kills it and everything it
    started on a limit."""
    started, wall = now(), time.monotonic()
    before = memory()
    p = subprocess.Popen(argv, cwd=cwd, stdin=stdin, stdout=stdout, stderr=stderr, start_new_session=True)
    stopped: list[str] = []

    def kill(reason: str) -> None:
        if not stopped:
            stopped.append(reason)
        kill_tree(p.pid)

    sampler = Sampler(p.pid, interval, cap_mb, lambda: kill("resource_limit"))
    sampler.start()
    timer = threading.Timer(timeout, lambda: kill("time_limit"))
    timer.start()
    try:
        _, status, usage = os.wait4(p.pid, 0)
    finally:
        timer.cancel()
        sampler.stop.set()
        # Whatever it left running goes with it.
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(p.pid, signal.SIGKILL)
    sampler.join(timeout=5)
    p.returncode = code = os.waitstatus_to_exitcode(status)
    elapsed = time.monotonic() - wall
    if stopped:
        outcome = stopped[0]
    elif code == 0:
        outcome = "ok"
    else:
        outcome = "failed"
    top = sorted(sampler.top.items(), key=lambda kv: -kv[1])[:5]
    return {
        "schema": SCHEMA,
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
        "exit": code,
        "wall_s": round(elapsed, 2),
        "user_s": round(usage.ru_utime, 2),
        "sys_s": round(usage.ru_stime, 2),
        "peak_process_mb": round(maxrss_mib(usage.ru_maxrss), 1),
        "peak_tree_mb": round(sampler.peak_tree_kib / 1024, 1),
        "peak_tree_processes": sampler.peak_procs,
        "peak_by_command_mb": {k: round(v, 1) for k, v in top},
        "samples": sampler.samples,
        "sample_interval_s": interval,
        "limits": {"timeout_s": timeout, "max_tree_rss_mb": cap_mb},
        "memory_before": before,
        "memory_after": memory(),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("memory", help="print what the machine has now")
    r = sub.add_parser("run", help="run a command and record what it cost")
    r.add_argument("--label", required=True)
    r.add_argument("--heavy", action="store_true", help="hold the machine's heavy-job lock while it runs")
    r.add_argument("--lock-wait", type=float, default=3600)
    r.add_argument("--timeout", type=float, default=3600)
    r.add_argument("--max-tree-rss-mb", type=float, default=None)
    r.add_argument("--min-available-mb", type=int, default=0)
    r.add_argument("--workers", type=int, default=1, help="how many workers the command was told to use")
    r.add_argument("--cap", action="append", default=[], help="a limit the command was given, as text")
    r.add_argument("--interval", type=float, default=0.25)
    r.add_argument("--out", type=Path, help="append the record to this JSON Lines file")
    r.add_argument("--log", type=Path, help="write the command's output here")
    r.add_argument("argv", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    if args.cmd == "memory":
        print(json.dumps(memory(), indent=2))
        return 0
    argv = args.argv[1:] if args.argv[:1] == ["--"] else args.argv
    if not argv:
        ap.error("no command")
    if why := too_busy(args.min_available_mb):
        print(f"not started: {why}", file=sys.stderr)
        return BUSY
    with contextlib.ExitStack() as stack:
        lock = str(stack.enter_context(heavy_lock(args.label, args.lock_wait))) if args.heavy else None
        log = stack.enter_context(args.log.open("wb")) if args.log else None
        record = run(
            argv,
            label=args.label,
            timeout=args.timeout,
            cap_mb=args.max_tree_rss_mb,
            interval=args.interval,
            stdout=log,
            stderr=subprocess.STDOUT if log else None,
        )
    record["workers"] = args.workers
    record["caps"] = args.cap
    record["heavy_lock"] = lock
    record["command_text"] = shlex.join(argv)
    line = json.dumps(record, sort_keys=True)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with args.out.open("a") as f:
            f.write(line + "\n")
    print(
        f"{record['label']}: {record['outcome']} exit={record['exit']} wall={record['wall_s']}s "
        f"peak_process={record['peak_process_mb']}MiB peak_tree={record['peak_tree_mb']}MiB",
        file=sys.stderr,
    )
    return 0 if record["outcome"] == "ok" else (record["exit"] or 1)


if __name__ == "__main__":
    sys.exit(main())
