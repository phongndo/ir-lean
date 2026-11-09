#!/usr/bin/env python3
"""Replay retained llama.cpp timing evidence without downloading or running a model.

Reads the archive in place, without extraction. Checks duplicate JSON records,
every stdout hash and logged inference duration, complete pairs, session point
estimates, and the pooled bootstrap using its recorded seed. Full process time
(wall_ms) comes from the driver's timing rows and cannot be recovered from stderr.
Session bootstrap seeds were not archived, so their intervals are only checked
for consistency between copies, not recomputed. The exploratory nibble-trial
keeps its historical ir-baseline label; every other session requires clang.
"""

import argparse
import json
import math
import random
import re
import statistics
import sys
import tarfile
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2] / "tools"))
from irlean import hashing

METRICS = ("wall_ms", "total_ms", "eval_ms", "prompt_ms")
LOG_PATTERNS = {
    "total_ms": r"total time =\s*([\d.]+) ms",
    "eval_ms": r"(?<!prompt )\beval time =\s*([\d.]+) ms",
    "prompt_ms": r"prompt eval time =\s*([\d.]+) ms",
    "eval_runs": r"(?<!prompt )\beval time =[^\n]+/\s+(\d+) runs",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def archive_bytes(archive, name):
    member = archive.getmember(name)
    require(member.isfile(), f"archive member is not a regular file: {name}")
    handle = archive.extractfile(member)
    require(handle is not None, f"cannot read archive member: {name}")
    if handle is None:
        raise ValueError(f"cannot read archive member: {name}")
    with handle:
        return handle.read()


def check_session(name, session, archive):
    for filename, key in (("rows.json", "rows"), ("summary.json", "summary"), ("command.json", "command")):
        archived = json.loads(archive_bytes(archive, f"{name}/{filename}"))
        require(archived == session[key], f"{name}: {filename} differs from sessions.json")
    baseline = "ir-baseline" if name == "nibble-trial" else "clang"
    rows, warmups = session["rows"], session["warmups"]
    variants = {row["variant"] for row in rows}
    require(len(variants) == 2 and baseline in variants, f"{name}: expected {baseline} and one target")
    require(all(re.fullmatch(r"[a-z0-9-]+", label) for label in variants), f"{name}: invalid variant label")
    target = next(label for label in variants if label != baseline)
    require(bool(rows) and len(rows) % 2 == 0, f"{name}: incomplete or empty paired rows")
    pairs = len(rows) // 2
    require(all(type(row["pair"]) is int for row in rows + warmups), f"{name}: noninteger pair ID")
    expected = {(pair, variant) for pair in range(pairs) for variant in variants}
    require({(row["pair"], row["variant"]) for row in rows} == expected, f"{name}: missing or duplicate pair")
    require(
        len(warmups) == 2
        and {(row["pair"], row["variant"]) for row in warmups} == {(-1, v) for v in variants},
        f"{name}: expected one warmup per variant",
    )
    reference_hash = None
    eval_runs = None
    for row in warmups + rows:
        stem = f"{name}/{row['pair']:03d}-{row['variant']}"
        for metric in METRICS:
            value = row[metric]
            require(
                type(value) in (int, float) and math.isfinite(value) and value > 0,
                f"{stem}: {metric} must be finite and positive",
            )
        output_hash = hashing.sha256(archive_bytes(archive, stem + ".txt"))
        require(output_hash == row["stdout_sha256"], f"{stem}: stdout hash differs from timing row")
        require(reference_hash in (None, output_hash), f"{stem}: generated output differs within session")
        reference_hash = output_hash
        log = archive_bytes(archive, stem + ".log").decode()
        for key, pattern in LOG_PATTERNS.items():
            matches = re.findall(pattern, log)
            require(len(matches) == 1, f"{stem}: expected one logged {key}")
            value = int(matches[0]) if key == "eval_runs" else float(matches[0])
            require(value == row[key], f"{stem}: logged {key} differs from timing row")
        require(type(row["eval_runs"]) is int and row["eval_runs"] > 0, f"{stem}: invalid eval run count")
        require(eval_runs in (None, row["eval_runs"]), f"{stem}: eval run count changed within session")
        eval_runs = row["eval_runs"]
    require(set(session["summary"]) == set(METRICS), f"{name}: unexpected session metrics")
    by_pair = {(row["pair"], row["variant"]): row for row in rows}
    ratios = {}
    for metric in METRICS:
        values = [by_pair[pair, baseline][metric] / by_pair[pair, target][metric] for pair in range(pairs)]
        recomputed = {
            "paired_ratios": values,
            "median_speedup": statistics.median(values),
            "range": [min(values), max(values)],
        }
        for key, expected_value in recomputed.items():
            require(session["summary"][metric][key] == expected_value, f"{name}: {metric} {key} differs")
        ratios[metric] = values
    return ratios


def replay(results):
    sessions = json.loads((results / "sessions.json").read_text())
    pooled = json.loads((results / "pooled-confirmation.json").read_text())
    require(bool(sessions), "no retained sessions")
    with tarfile.open(results / "raw-measurements.tar.gz", "r:gz") as archive:
        names = archive.getnames()
        require(len(names) == len(set(names)), "duplicate archive member names")
        ratios = {name: check_session(name, session, archive) for name, session in sessions.items()}
    selected = pooled["sessions"]
    require(bool(selected) and len(selected) == len(set(selected)), "invalid pooled session selection")
    require(
        set(selected)
        == {name for name, session in sessions.items() if session["classification"] == "confirmation"},
        "pooled sessions differ from the complete confirmation set",
    )
    require(type(pooled["bootstrap_seed"]) is int, "pooled bootstrap seed must be an integer")
    require(pooled["bootstrap_resamples"] == 20000, "expected 20000 pooled bootstrap resamples")
    require(set(pooled["metrics"]) == {"wall_ms", "total_ms", "eval_ms"}, "unexpected pooled metrics")
    rng = random.Random(pooled["bootstrap_seed"])
    # The original pool consumed one RNG sequentially in stored metric order.
    for metric, stored in pooled["metrics"].items():
        values = [ratio for name in selected for ratio in ratios[name][metric]]
        samples = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(20000))
        recomputed = {
            "paired_ratios": values,
            "median_speedup": statistics.median(values),
            "range": [min(values), max(values)],
            "faster_pairs": sum(value > 1 for value in values),
            "pairs": len(values),
            "bootstrap_median_95_percent": [samples[499], samples[19499]],
        }
        require(stored == recomputed, f"pooled {metric}: recomputed statistics differ")
    return {
        "consistent": True,
        "sessions": len(sessions),
        "timed_pairs": sum(len(session["rows"]) // 2 for session in sessions.values()),
        "warmup_runs": sum(len(session["warmups"]) for session in sessions.values()),
        "pooled_pairs": pooled["metrics"]["total_ms"]["pairs"],
        "pooled_bootstrap_recomputed": True,
        "limits": [
            "wall_ms is recorded by the timing driver; stderr cannot independently reconstruct it.",
            "Session confidence intervals agree between copies but are not recomputed: no archived seeds.",
            "nibble-trial retains its historical ir-baseline label; all other baselines are clang.",
            "Consistency of recorded evidence does not establish fresh-run performance or proof correctness.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=Path(__file__).parent / "results/2026-11-07")
    args = parser.parse_args()
    try:
        result = replay(args.results)
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print(f"replay_results: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
