#!/usr/bin/env python3
"""Runs one command under a time limit and a memory cap, and records what it cost: wall time, CPU time, and
peak resident memory, of the process and of everything it starts. docs/corpus.md says how to use it, and
tools/irlean/proc.py, which does the work, what each number means and how the limits are kept.

A cap or a timeout kills the process and every descendant, with the process groups and sessions they started,
and the record says `resource_limit` or `time_limit`. Neither is ever a success. `--heavy` takes a slot in
the machine's pool of heavy jobs first, shared by every checkout, declaring `--max-tree-rss-mb` as what it
needs, or 3.5 GB without one, and waits while running it would leave too little memory. `pool` says how many
slots there are and who holds them.

usage: tools/measure.py run --label L [--heavy] [--timeout S] [--max-tree-rss-mb MB] [--workers N]
                            [--cap TEXT ...] [--min-available-mb MB] [--out FILE.jsonl] -- COMMAND ...
       tools/measure.py memory
       tools/measure.py pool
"""

from __future__ import annotations

import argparse
import contextlib
import json
import shlex
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from irlean import proc


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("memory", help="print what the machine has now")
    sub.add_parser("pool", help="print the pool of heavy jobs: its slots, its reserve and who holds each")
    r = sub.add_parser("run", help="run a command and record what it cost")
    r.add_argument("--label", required=True)
    r.add_argument("--heavy", action="store_true", help="hold a slot in the machine's pool of heavy jobs")
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
        print(json.dumps(proc.memory(), indent=2))
        return 0
    if args.cmd == "pool":
        print(json.dumps(proc.pool(), indent=2))
        return 0
    argv = args.argv[1:] if args.argv[:1] == ["--"] else args.argv
    if not argv:
        ap.error("no command")
    if why := proc.too_busy(args.min_available_mb):
        print(f"not started: {why}", file=sys.stderr)
        return proc.BUSY
    with contextlib.ExitStack() as stack:
        try:
            lock = (
                str(stack.enter_context(proc.heavy_lock(args.label, args.lock_wait, args.max_tree_rss_mb)))
                if args.heavy
                else None
            )
        except TimeoutError as error:
            # No slot within --lock-wait is the machine being busy, as too little memory is, not the command
            # failing.
            print(f"not started: {error}", file=sys.stderr)
            return proc.BUSY
        log = stack.enter_context(args.log.open("wb")) if args.log else None
        record = proc.measure(
            argv,
            label=args.label,
            timeout=args.timeout,
            cap_mb=args.max_tree_rss_mb,
            interval=args.interval,
            stdout=log,
            stderr=proc.STDOUT if log else None,
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
