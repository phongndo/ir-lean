#!/usr/bin/env python3
"""How many of InstCombine's changed pairs an emitter translates, compared with a baseline, for
docs/float.md.

Stage 1's `pairs` stage (bench/instcombine/stage1.py, on the branch `feat/stage1-benchmark`) runs `opt` on
every InstCombine test and keeps each changed function's source and target. This runs only the emitter again,
on those saved pairs, with stage 1's own `classify`, so `opt` runs once and every emitter is judged on the
same pairs.

usage: prototypes/float/coverage.py --stage1 CHECKOUT --work DIR --tool EMITTER [--out FILE] [--jobs N]

  CHECKOUT  a checkout of feat/stage1-benchmark, whose bench/instcombine/stage1.py this imports
  DIR       where `stage1.py --work DIR pairs` wrote pairs.jsonl and pairs/
  EMITTER   the ir-lean binary to classify with

It prints the counts by status, the moves from the baseline in DIR/pairs.jsonl, the emitter's refusals
grouped as stage 1 groups them, and the commonest floating-point reasons left. Run it in `nix develop`.
"""

import argparse
import collections
import concurrent.futures
import importlib.util
import json
import re
import sys
from pathlib import Path
from typing import Any

CLASSIFIED = (
    "emitter",
    "emitter_detail",
    "signature",
    "lean_name",
    "pure",
    "undef_arguments",
    "trusted_promise",
    "trusted_promise_in_function",
    "vector",
    "status",
    "reason",
)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage1", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--tool", type=Path, required=True)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--jobs", type=int, default=12)
    args = ap.parse_args()
    sys.path.insert(0, str(args.stage1 / "tests"))
    spec = importlib.util.spec_from_file_location(
        "stage1", args.stage1 / "bench" / "instcombine" / "stage1.py"
    )
    if spec is None or spec.loader is None:
        sys.exit(f"can't load {args.stage1}/bench/instcombine/stage1.py")
    s1: Any = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s1)
    s1.TOOL = args.tool.resolve()

    with open(args.work / "pairs.jsonl") as f:
        base = [json.loads(line) for line in f]

    def again(p: dict) -> dict:
        if p["status"] not in ("candidate", "unsupported"):
            return p
        d = args.work / "pairs" / p["id"]
        rec = {k: v for k, v in p.items() if k not in CLASSIFIED}
        return s1.classify(rec, d, (d / "src.ll").read_text(), (d / "tgt.ll").read_text(), p["function"])

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        new = list(pool.map(again, base))
    if args.out:
        with open(args.out, "w") as f:
            for p in new:
                f.write(json.dumps(p) + "\n")

    def key(p: dict) -> str:
        return f"{p['status']}:{p['reason']}"

    print("pairs:", len(new))
    print("before:", dict(collections.Counter(map(key, base))))
    print("after: ", dict(collections.Counter(map(key, new))))
    moves = collections.Counter(
        f"{key(a)} -> {key(b)}" for a, b in zip(base, new, strict=True) if key(a) != key(b)
    )
    print("moves:", json.dumps(dict(moves.most_common()), indent=1))
    refused = s1.refusals(args.work, new)
    print("refusals by first reason:", json.dumps(refused["by_first_reason"], indent=1))
    fp = re.compile(next(rx for name, rx in s1.REFUSAL_GROUPS if name == "floating point"))
    left = collections.Counter()
    for p in new:
        if p["status"] == "unsupported" and p["reason"] == "emitter":
            side = "src" if p["emitter"]["src"] != "ok" else "tgt"
            why = p["emitter_detail"][side].split("\t")[-1].strip()
            if fp.search(why):
                left[re.sub(r"%[-\w.$\"]+", "%v", re.sub(r"\b\d+\b", "N", why))[:90]] += 1
    print("floating-point reasons left:", json.dumps(dict(left.most_common(40)), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
