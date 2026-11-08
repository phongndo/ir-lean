#!/usr/bin/env python3
"""Linux-only randomized paired measurements of stock completion on a real prompt.

Uses the baseline executable for both variants, selecting the CPU library through
LD_LIBRARY_PATH and verifying the runtime implementation's dependency resolution.
The sampling seed remains 1234; --seed controls randomized order and bootstrap
resampling. The output directory must not already exist, so retained runs cannot
be mixed or overwritten. Raw stdout, stderr, measurements and loader evidence are
retained there, including both warmups.
"""

import argparse
import hashlib
import json
import os
import random
import re
import resource
import statistics
import subprocess
import sys
import time
from pathlib import Path


def file_hash(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def completion_command(args, executable):
    mask = hex(((1 << args.threads) - 1) << args.first_cpu)
    cpus = f"{args.first_cpu}-{args.first_cpu + args.threads - 1}"
    return [
        "taskset",
        "-c",
        cpus,
        str(executable),
        "-m",
        str(args.model),
        "-ngl",
        "0",
        "-t",
        str(args.threads),
        "-tb",
        str(args.threads),
        "--cpu-mask",
        mask,
        "--cpu-strict",
        "1",
        "--cpu-mask-batch",
        mask,
        "--cpu-strict-batch",
        "1",
        "-c",
        "4096",
        "-b",
        "512",
        "-ub",
        "512",
        "-n",
        str(args.tokens),
        "--seed",
        "1234",
        "--temp",
        "0.7",
        "--top-k",
        "20",
        "--top-p",
        "0.8",
        "--min-p",
        "0",
        "--no-conversation",
        "--simple-io",
        "--no-display-prompt",
        "-f",
        str(args.prompt),
    ]


def checked_environments(build_bin, variant_dir, executable, output):
    environments = {}
    for variant, directory in [("clang", build_bin), ("rewrite", variant_dir)]:
        library = directory / "libggml-cpu.so.0"
        if not library.is_file():
            raise ValueError(f"missing CPU library: {library}")
        environment = {**os.environ, "LD_LIBRARY_PATH": str(directory) + ":" + str(build_bin)}
        environments[variant] = environment
        mapping = subprocess.check_output(["ldd", str(executable)], text=True, env=environment)
        (output / (variant + "-ldd.txt")).write_text(mapping)
        # The completion launcher loads its implementation at runtime. Check that too.
        implementation = build_bin / "libllama-completion-impl.so"
        mapping = subprocess.check_output(["ldd", str(implementation)], text=True, env=environment)
        (output / (variant + "-impl-ldd.txt")).write_text(mapping)
        match = re.search(r"^\s*libggml-cpu\.so\.0 => (.+) \(", mapping, re.MULTILINE)
        if match is None or Path(match[1]).resolve() != library.resolve():
            raise RuntimeError(f"{variant} implementation does not resolve to the requested CPU library")
        (output / (variant + "-library.sha256")).write_text(file_hash(library) + "\n")
    return environments


def measure(command, environment, output, variant, pair, reference):
    stem = f"{pair:03d}-{variant}"
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter()
    result = subprocess.run(command, capture_output=True, env=environment, check=False)
    wall_ms = (time.perf_counter() - started) * 1000
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    (output / (stem + ".txt")).write_bytes(result.stdout)
    (output / (stem + ".log")).write_bytes(result.stderr)
    if result.returncode != 0:
        raise RuntimeError(f"completion {stem} failed with exit code {result.returncode}; raw logs retained")
    if reference is not None and reference != result.stdout:
        raise RuntimeError(f"completion output differs: {stem}; raw outputs retained")
    log = result.stderr.decode()
    row = {
        "pair": pair,
        "variant": variant,
        "wall_ms": wall_ms,
        "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
        "cpu_user_ms": (usage_after.ru_utime - usage_before.ru_utime) * 1000,
        "cpu_system_ms": (usage_after.ru_stime - usage_before.ru_stime) * 1000,
        "involuntary_switches": usage_after.ru_nivcsw - usage_before.ru_nivcsw,
        "voluntary_switches": usage_after.ru_nvcsw - usage_before.ru_nvcsw,
    }
    for key, pattern in [
        ("eval_ms", r"(?<!prompt )\beval time =\s*([\d.]+) ms"),
        ("prompt_ms", r"prompt eval time =\s*([\d.]+) ms"),
        ("total_ms", r"total time =\s*([\d.]+) ms"),
    ]:
        match = re.search(pattern, log)
        if match is None:
            raise RuntimeError(f"missing {key} in {stem}; raw logs retained")
        value = float(match[1])
        if value <= 0:
            raise RuntimeError(f"nonpositive {key} in {stem}")
        row[key] = value
    match = re.search(r"(?<!prompt )\beval time =[^\n]+/\s+(\d+) runs", log)
    if match is None:
        raise RuntimeError(f"missing eval run count in {stem}; raw logs retained")
    row["eval_runs"] = int(match[1])
    with (output / "rows.jsonl").open("a") as handle:
        handle.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)
    return row, result.stdout


def summarize(rows, pairs, rng):
    summary = {}
    for metric in ["wall_ms", "total_ms", "eval_ms", "prompt_ms"]:
        ratios = [
            next(row[metric] for row in rows if row["pair"] == pair and row["variant"] == "clang")
            / next(row[metric] for row in rows if row["pair"] == pair and row["variant"] == "rewrite")
            for pair in range(pairs)
        ]
        bootstrap = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(20000))
        summary[metric] = {
            "paired_ratios": ratios,
            "median_speedup": statistics.median(ratios),
            "bootstrap_median_95_percent": [bootstrap[499], bootstrap[19499]],
            "range": [min(ratios), max(ratios)],
        }
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, required=True, help="baseline CMake build directory")
    parser.add_argument(
        "--variant-dir", type=Path, required=True, help="directory containing rewritten libggml-cpu.so.0"
    )
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--prompt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="new directory for all retained evidence")
    parser.add_argument("--pairs", type=int, default=12)
    parser.add_argument("--threads", type=int, default=8)
    parser.add_argument("--first-cpu", type=int, default=8)
    parser.add_argument("--tokens", type=int, default=512)
    parser.add_argument(
        "--seed", type=int, default=20261107, help="pair-order and bootstrap seed; sampling uses 1234"
    )
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("this measurement driver requires Linux taskset, ldd, and resource usage accounting")
    if min(args.pairs, args.threads, args.tokens) < 1 or args.first_cpu < 0:
        parser.error("pairs, threads and tokens must be positive; first-cpu must be nonnegative")
    requested_cpus = set(range(args.first_cpu, args.first_cpu + args.threads))
    if not requested_cpus.issubset(os.sched_getaffinity(0)):
        parser.error("requested CPU range is outside this process's allowed affinity")
    args.build_dir = args.build_dir.resolve()
    args.variant_dir = args.variant_dir.resolve()
    args.model = args.model.resolve()
    args.prompt = args.prompt.resolve()
    args.output = args.output.resolve()
    build_bin = args.build_dir / "bin"
    executable = build_bin / "llama-completion"
    for path in [executable, args.model, args.prompt]:
        if not path.is_file():
            parser.error(f"missing input file: {path}")
    args.output.mkdir(parents=True, exist_ok=False)
    command = completion_command(args, executable)
    write_json(args.output / "command.json", command)
    write_json(
        args.output / "run.json",
        {
            "platform": sys.platform,
            "pairs": args.pairs,
            "threads": args.threads,
            "first_cpu": args.first_cpu,
            "requested_tokens": args.tokens,
            "pair_order_seed": args.seed,
            "sampling_seed": 1234,
            "bootstrap_samples": 20000,
            "bootstrap_method": "percentile interval for the median of paired clang/rewrite duration ratios",
            "model_sha256": file_hash(args.model),
            "prompt_sha256": file_hash(args.prompt),
            "executable_sha256": file_hash(executable),
            "driver_sha256": file_hash(Path(__file__)),
        },
    )
    environments = checked_environments(build_bin, args.variant_dir, executable, args.output)
    variants = ["clang", "rewrite"]
    reference = None
    warmups = []
    for variant in variants:
        row, reference = measure(command, environments[variant], args.output, variant, -1, reference)
        warmups.append(row)
        write_json(args.output / "warmups.json", warmups)
    if warmups[0]["eval_runs"] != warmups[1]["eval_runs"]:
        raise RuntimeError("warmup eval run count differs despite identical stdout")
    rng = random.Random(args.seed)
    rows = []
    for pair in range(args.pairs):
        order = list(variants)
        rng.shuffle(order)
        for variant in order:
            row, _ = measure(command, environments[variant], args.output, variant, pair, reference)
            if row["eval_runs"] != warmups[0]["eval_runs"]:
                raise RuntimeError("completion eval run count differs despite identical stdout")
            rows.append(row)
            write_json(args.output / "rows.json", rows)
    summary = summarize(rows, args.pairs, rng)
    write_json(args.output / "summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
