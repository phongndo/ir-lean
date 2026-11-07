#!/usr/bin/env python3
"""Times checking real proofs, one Lean process at a time, and what each one takes in memory.

This generates the Lean the proofs import from the same compiler output the tests use, compiles everything
they import, and then checks each proof `--runs` times, with the flags the tests use. Each round checks every
proof once, in an order that rotates, so a change in load on the machine falls on all of them alike. It prints
the median, fastest and slowest wall time, the median user and system time, the largest peak resident memory
of any run, and the load average before and after, which says how much else the machine was doing.

`--proof NAME=FILE` checks FILE in place of proof NAME, against the same generated code, and
`--variant NAME=FILE` checks it as well, as `NAME+1`, so two versions of a proof can be compared on the same
obligations. The first round of a proof reads its imports from disk, unless something read them recently, and
the rest from the page cache, so the first round is reported apart.

On macOS, peak resident memory counts the pages of the `.olean` files Lean maps: about 650 MB for IRLean.

usage: tests/proof_bench.py path/to/ir-lean [--runs N] [--llvm MODULE ...] [--proof NAME=FILE ...]
                            [--variant NAME=FILE ...] [--json FILE] [NAME ...]

With no NAME it checks every proof in tests/proofs and those of the `--llvm` targets. Run it in the dev shell.
"""

import argparse
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
# The zlib proofs, after what they import from each other.
ZLIB_PROOFS = ["Popcount", "Adler32", "CrcTables", "CrcSpec", "Crc32"]
MEMORY_MB = os.environ.get("LEAN_MAX_MB", "4000")


def run(command: list[str], env: dict[str, str] | None = None) -> str:
    result = subprocess.run(command, env=env, capture_output=True, text=True, check=False)
    if result.returncode != 0:
        sys.exit(f"{' '.join(command)} failed:\n{result.stdout[-4000:]}{result.stderr[-4000:]}")
    return result.stdout


def lean_env(path: list[Path]) -> dict[str, str]:
    return {**os.environ, "LEAN_PATH": ":".join(str(p) for p in [*path, LIBRARY])}


def imports(file: Path) -> list[str]:
    return re.findall(r"^import (\S+)", file.read_text(), re.MULTILINE)


def compile_generated(directory: Path) -> None:
    """Compiles every module `tests/proofs.sh --generate` wrote, each after what it imports."""
    modules = {
        ".".join(f.relative_to(directory).with_suffix("").parts): f for f in sorted(directory.rglob("*.lean"))
    }
    done: set[str] = set()
    while len(done) < len(modules):
        ready = [
            m
            for m, f in modules.items()
            if m not in done and all(i in done or i not in modules for i in imports(f))
        ]
        if not ready:
            sys.exit(f"modules in {directory} import each other")
        for module in ready:
            file = modules[module]
            olean = file.with_suffix(".olean")
            run(
                ["lean", "-M", MEMORY_MB, "-R", str(directory), "-o", str(olean), str(file)],
                lean_env([directory]),
            )
            done.add(module)


class Proof:
    def __init__(self, name: str, file: Path, path: list[Path], flags: list[str]) -> None:
        self.name, self.file, self.path, self.flags = name, file, path, flags
        self.samples: list[dict[str, float]] = []

    def command(self, output: Path) -> list[str]:
        return ["lean", *self.flags, "-R", str(self.file.parent), "-o", str(output), str(self.file)]

    def check(self, output: Path) -> dict[str, float]:
        """Checks the proof once, and returns its wall, user and system seconds and peak resident memory."""
        started = time.monotonic()
        process = subprocess.Popen(
            self.command(output),
            env=lean_env(self.path),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        assert process.stdout is not None
        log = process.stdout.read()
        _, status, usage = os.wait4(process.pid, 0)
        wall = time.monotonic() - started
        process.returncode = os.waitstatus_to_exitcode(status)
        if process.returncode != 0:
            sys.exit(f"{self.name} failed:\n{log.decode(errors='replace')[-4000:]}")
        # Linux counts it in KiB, and macOS in bytes.
        rss = usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)
        return {"wall": wall, "user": usage.ru_utime, "system": usage.ru_stime, "rss_mb": rss / 2**20}


def zlib_proofs(tool: Path, work: Path, overrides: dict[str, Path]) -> list[Proof]:
    generated = work / "generated"
    run([str(ROOT / "tests" / "proofs.sh"), str(tool), "--generate", str(generated)])
    compile_generated(generated)
    compiled = work / "proofs"
    compiled.mkdir()
    proofs = []
    for name in ZLIB_PROOFS:
        source = ROOT / "tests" / "proofs" / f"{name}.lean"
        path = [compiled, generated]
        # Later proofs import the repo's version of earlier ones, whatever version is timed.
        run(
            [
                "lean",
                "-M",
                MEMORY_MB,
                "-R",
                str(source.parent),
                "-o",
                str(compiled / f"{name}.olean"),
                str(source),
            ],
            lean_env(path),
        )
        proofs.append(Proof(name, overrides.get(name, source), path, ["-M", MEMORY_MB]))
    return proofs


def llvm_proofs(tool: Path, work: Path, modules: list[str], overrides: dict[str, Path]) -> list[Proof]:
    if not modules:
        return []
    sys.path.insert(0, str(ROOT / "tests"))
    import llvm

    config = tomllib.loads((llvm.PROOFS / "targets.toml").read_text())
    targets = {t["module"]: t for t in config["target"]}
    if unknown := [m for m in modules if m not in targets]:
        sys.exit(f"no targets {unknown} in targets.toml")
    directory = work / "llvm"
    directory.mkdir()
    pipeline = llvm.Pipeline(tool.resolve(), directory, config)
    for module in config.get("support", []):
        pipeline.compile_lean(directory, llvm.PROOFS / f"{module}.lean", llvm.PROOFS)
    proofs = []
    for module in modules:
        target = targets[module]
        try:
            pipeline.generate(target, directory)
        except RuntimeError as error:
            sys.exit(f"{module}: {str(error)[:4000]}")
        name = target["proof"]
        source = overrides.get(name, llvm.PROOFS / f"{name}.lean")
        proofs.append(
            Proof(name, source, [directory], ["-M", MEMORY_MB, "-s", "65536", "-DwarningAsError=true"])
        )
    return proofs


def versions() -> dict[str, str]:
    return {
        "lean": run(["lean", "--version"]).strip(),
        "clang": run(["clang", "--version"]).splitlines()[0],
        "host": f"{platform.system()} {platform.machine()}, {os.cpu_count()} CPUs",
    }


def summary(proof: Proof) -> dict[str, Any]:
    rest = proof.samples[1:] or proof.samples
    return {
        "file": str(proof.file),
        "runs": len(proof.samples),
        "first": proof.samples[0]["wall"],
        "median": statistics.median(s["wall"] for s in rest),
        "min": min(s["wall"] for s in rest),
        "max": max(s["wall"] for s in rest),
        "user": statistics.median(s["user"] for s in rest),
        "system": statistics.median(s["system"] for s in rest),
        "rss_mb": max(s["rss_mb"] for s in proof.samples),
        "samples": proof.samples,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    parser.add_argument("names", nargs="*", help="only these proofs")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--llvm", nargs="*", default=[], help="targets.toml modules, such as CrtUdivmoddi4")
    parser.add_argument("--proof", action="append", default=[], help="NAME=FILE: check FILE in place of NAME")
    parser.add_argument(
        "--variant",
        action="append",
        default=[],
        help="NAME=FILE: check FILE as well as NAME, against its code",
    )
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    overrides = {}
    for spec in args.proof:
        name, _, file = spec.partition("=")
        overrides[name] = Path(file).resolve()

    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        proofs = []
        if not args.names or set(args.names) & set(ZLIB_PROOFS):
            proofs += zlib_proofs(args.tool.resolve(), work, overrides)
        proofs += llvm_proofs(args.tool.resolve(), work, args.llvm, overrides)
        if args.names:
            proofs = [p for p in proofs if p.name in args.names]
        if unknown := sorted(set(args.names) - {p.name for p in proofs}):
            sys.exit(f"no proofs {unknown}")
        for i, spec in enumerate(args.variant, 1):
            name, _, file = spec.partition("=")
            of = next((p for p in proofs if p.name == name), None)
            if of is None:
                sys.exit(f"no proof {name} for --variant")
            proofs.append(Proof(f"{name}+{i}", Path(file).resolve(), of.path, of.flags))
            print(f"{name}+{i} is {Path(file).resolve()}")
        before = os.getloadavg()[0]
        for i in range(args.runs):
            for proof in proofs[i % len(proofs) :] + proofs[: i % len(proofs)]:
                proof.samples.append(proof.check(work / "timed.olean"))
        after = os.getloadavg()[0]

    results = {p.name: summary(p) for p in proofs}
    print(f"load average {before:.1f} before, {after:.1f} after")
    print(f"{'proof':<14}{'first':>8}{'median':>8}{'min':>8}{'max':>8}{'user':>8}{'sys':>8}{'peak MB':>9}")
    for name, r in results.items():
        print(
            f"{name:<14}{r['first']:>8.2f}{r['median']:>8.2f}{r['min']:>8.2f}{r['max']:>8.2f}"
            f"{r['user']:>8.2f}{r['system']:>8.2f}{r['rss_mb']:>9.0f}"
        )
    if args.json:
        report = {"versions": versions(), "load": {"before": before, "after": after}, "proofs": results}
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
