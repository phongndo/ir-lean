#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Times the dev cycle: what a person waits for after each kind of change, and fails if a test fails.

usage: tests/bench.py [--json FILE] [SCENARIO ...]

With no scenarios it runs all of them, in the order below, and prints their total. Each edit is real, and
different on every run, so nothing can come from a cache that shouldn't. Every edit is undone afterwards, even
if the run fails. `cold` deletes .lake/build and build first. Run it in the dev shell, at a quiet moment.

    cold     From nothing: build the library and the translator, then run the tests
    noop     Nothing changed: run the tests
    emitter  An edit to the translator that doesn't change what it emits: rebuild it, run the tests
    proof    An edit to a proof: run the proofs
    use      Compile a C file, translate it, and check the Lean, as the quickstart does
    model    An edit to the Lean library: rebuild it, run the tests, which recompile what they emit
"""

import json
import os
import resource
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TESTS = ["ctest", "--test-dir", "build", "-LE", "slow", "--output-on-failure"]
BUILD_LIBRARY = ["lake", "build", "--no-ansi"]
BUILD_TOOL = ["ninja", "-C", "build"]


def run(args, **kw):
    r = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=False, **kw)
    if r.returncode != 0:
        sys.exit(f"{' '.join(args)} failed:\n{r.stdout[-8000:]}{r.stderr[-2000:]}")
    return r.stdout


class Edit:
    """Appends to a file, and puts it back afterwards."""

    def __init__(self, path, text):
        self.path, self.text = os.path.join(ROOT, path), text

    def __enter__(self):
        with open(self.path) as f:
            self.original = f.read()
        with open(self.path, "a") as f:
            f.write(self.text)

    def __exit__(self, *_):
        with open(self.path, "w") as f:
            f.write(self.original)


def token():
    return f"{time.time_ns():x}"


def scenario_cold(timed):
    for path in [os.path.join(ROOT, ".lake", "build"), os.path.join(ROOT, "build")]:
        shutil.rmtree(path, ignore_errors=True)
    timed(
        BUILD_LIBRARY,
        ["cmake", "-S", ".", "-B", "build", "-G", "Ninja"],
        BUILD_TOOL,
        TESTS,
    )


def scenario_noop(timed):
    timed(TESTS)


def scenario_emitter(timed):
    with Edit("src/Emitter.cpp", f"\n// bench {token()}\n"):
        timed(BUILD_TOOL, TESTS)
    run(BUILD_TOOL)


def scenario_proof(timed):
    with Edit("tests/proofs/Crc32.lean", f"\ntheorem bench_{token()} : True := trivial\n"):
        timed(["ctest", "--test-dir", "build", "-R", "^proofs$", "--output-on-failure"])


def scenario_use(timed):
    with tempfile.TemporaryDirectory() as work:
        ll, lean = os.path.join(work, "popcount.ll"), os.path.join(work, "Popcount.lean")
        timed(
            [
                "clang",
                "-O2",
                "-fno-strict-aliasing",
                "-S",
                "-emit-llvm",
                "-fno-discard-value-names",
                "tests/real/bi_reverse.c",
                "-o",
                ll,
            ],
            ["build/ir-lean", ll, "-o", lean],
            ["lake", "env", "lean", lean],
        )


def scenario_model(timed):
    with Edit("IRLean/Mem.lean", f"\ntheorem bench_{token()} : True := trivial\n"):
        timed(BUILD_LIBRARY, TESTS)
    run(BUILD_LIBRARY)
    # The cache holds one version of each module, so this brings back the one for the code as it was.
    run(TESTS)


SCENARIOS = {
    "cold": scenario_cold,
    "noop": scenario_noop,
    "emitter": scenario_emitter,
    "proof": scenario_proof,
    "use": scenario_use,
    "model": scenario_model,
}


def measure(scenario):
    wall = [0.0]
    before = resource.getrusage(resource.RUSAGE_CHILDREN)

    def timed(*commands):
        start = time.monotonic()
        for command in commands:
            run(command)
        wall[0] += time.monotonic() - start

    scenario(timed)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return wall[0], after.ru_utime - before.ru_utime, after.ru_stime - before.ru_stime


def main():
    args = sys.argv[1:]
    out = None
    if "--json" in args:
        i = args.index("--json")
        out = args[i + 1]
        del args[i : i + 2]
    names = args or list(SCENARIOS)
    for name in names:
        if name not in SCENARIOS:
            sys.exit(f"no scenario {name}: {' '.join(SCENARIOS)}")
    if names[0] != "cold":
        run(BUILD_LIBRARY)
        run(BUILD_TOOL)
        run(TESTS)
    results = {}
    print(f"{'scenario':<10}{'wall s':>9}{'user s':>9}{'sys s':>9}{'load':>7}")
    for name in names:
        load = os.getloadavg()[0]
        wall, user, system = measure(SCENARIOS[name])
        results[name] = {"wall": wall, "user": user, "system": system, "load": load}
        print(f"{name:<10}{wall:>9.1f}{user:>9.1f}{system:>9.1f}{load:>7.1f}", flush=True)
    total = sum(r["wall"] for r in results.values())
    print(f"{'total':<10}{total:>9.1f}")
    if out:
        with open(out, "w") as f:
            json.dump(results, f, indent=2)


if __name__ == "__main__":
    main()
