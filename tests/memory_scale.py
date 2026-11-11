#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Measures how long real zlib takes to run in the model as its input grows, on `IRLean.Mem` and on
`IRLean.ExecMem`, and checks each result against native code. docs/memory.md#what-it-costs has what it
measured.

usage: tests/memory_scale.py path/to/ir-lean [--sizes N,N,...] [--memory model,exec] [--level L]
                             [--timeout S] [--json FILE]

Each run is one call of `harness_big_sized` in tests/real/zlib_harness.c: `n` bytes that repeat from
about 32 KiB back, deflated at level `L`, 6 by default, with a 32 KiB window and inflated back 4 KiB at a
time. It runs in its own `lean --run`, with the library native as tests/differential.py runs it, and the
time and peak memory are that process's, so compiling isn't counted. Sizes go up in order, and a
representation stops at the first that takes longer than `--timeout`, 600 s by default. Run it through
`tools/measure.py run --heavy`.
"""

import json
import os
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
sys.path.append(os.path.join(ROOT, "tests"))
import differential  # noqa: E402
from irlean import proc  # noqa: E402

FILES = [
    "adler32",
    "compress",
    "crc32",
    "deflate",
    "infback",
    "inffast",
    "inflate",
    "inftrees",
    "trees",
    "uncompr",
    "zutil",
]
FLAGS = ["-O2", "-fno-strict-aliasing", "-S", "-emit-llvm", "-fno-discard-value-names"]
SEED = 12345


def zlib_ll(work):
    """All of zlib and the harness, linked, as tests/zlib.sh builds it."""
    src = (
        os.environ.get("ZLIB_SRC")
        or differential.sh(
            ["nix", "build", "--inputs-from", ROOT, "--no-link", "--print-out-paths", "nixpkgs#zlib.src"]
        ).out.strip()
    )
    zdir = os.path.join(work, "zlib")
    os.makedirs(zdir)
    differential.sh(["tar", "-xf", src, "-C", zdir, "--strip-components=1"])
    lls = []
    for f in FILES:
        out = os.path.join(work, f + ".ll")
        differential.sh(
            [
                "clang",
                *FLAGS,
                "-D_LARGEFILE64_SOURCE=1",
                "-U__ARM_FEATURE_CRC32",
                f"-I{zdir}",
                "-o",
                out,
                f"{zdir}/{f}.c",
            ]
        )
        lls.append(out)
    harness = os.path.join(work, "harness.ll")
    differential.sh(
        ["clang", *FLAGS, f"-I{zdir}", "-o", harness, os.path.join(ROOT, "tests", "real", "zlib_harness.c")]
    )
    linked = os.path.join(work, "zlib.ll")
    differential.sh(["llvm-link", "-S", "-o", linked, *lls, harness])
    return linked


def native(ll, work, sizes, level):
    """What native code returns for each size."""
    driver = os.path.join(work, "driver.c")
    with open(driver, "w") as f:
        f.write(
            "#include <stdio.h>\n"
            "unsigned harness_big_sized(unsigned, unsigned, unsigned);\n"
            "int main(void) {\n"
        )
        for n in sizes:
            f.write(f'  printf("%u\\n", harness_big_sized({SEED}u, {n}u, {level}u));\n')
        f.write("  return 0;\n}\n")
    exe = os.path.join(work, "native")
    differential.sh(["clang", "-O1", "-Wno-override-module", ll, driver, "-o", exe])
    return [int(x) for x in differential.sh([exe]).out.split()]


def build(tool, ll, work, model_memory):
    """The split module on `Mem` or `ExecMem`, compiled."""
    os.makedirs(work)
    differential.emit_lean(tool, ll, work, True, model_memory)
    differential.compile_lean(work, True)


def run_one(work, n, level, timeout):
    """One call in its own process: its result, seconds and peak MiB, or None past `timeout`."""
    drive = os.path.join(work, f"Size{n}.lean")
    memory = "M.initial"
    with open(drive, "w") as f:
        f.write(
            "import M\nopen IRLean\nset_option maxRecDepth 1000000\n"
            "def main : IO Unit := do\n"
            f"  match andThen (M.harness_big_sized (some (BitVec.ofNat 32 {SEED}))"
            f" (some (BitVec.ofNat 32 {n})) (some (BitVec.ofNat 32 {level})) {memory})"
            " (fun r => Outcome.ok r.1) with\n"
            "  | some (.ok (some v)) => IO.println (toString v.toNat)\n"
            '  | some (.ok none) => IO.println "poison"\n'
            '  | some (.error e) => IO.println ("stopped: " ++ reprStr e)\n'
            '  | none => IO.println "diverged"\n'
        )
    command = ["lean", "-M", differential.LEAN_MAX_MB, *differential.NATIVE, "--run", drive]
    r = proc.run(command, env=differential.lean_env(work), timeout=timeout)
    if r.limit is not None:
        return None, r.seconds, r.peak_process_mb
    if r.exit != 0:
        sys.exit(f"lean failed:\n{r.output[:3000]}")
    return r.out.strip(), r.seconds, r.peak_process_mb


def main():
    args = sys.argv[1:]

    def option(name, default):
        if name in args:
            i = args.index(name)
            value = args[i + 1]
            del args[i : i + 2]
            return value
        return default

    sizes = [int(s) for s in option("--sizes", "1024,4096,16384,32768,65536,131072").split(",")]
    memories = option("--memory", "model,exec").split(",")
    level = int(option("--level", "5"))
    timeout = float(option("--timeout", "600"))
    out = option("--json", None)
    tool = os.path.abspath(args[0])
    rows, failed = [], False
    with tempfile.TemporaryDirectory(prefix="scale-") as work:
        ll = zlib_ll(work)
        expected = native(ll, work, sizes, level)
        for memory in memories:
            mwork = os.path.join(work, memory)
            build(tool, ll, mwork, memory == "model")
            for n, want in zip(sizes, expected, strict=True):
                got, seconds, peak = run_one(mwork, n, level, timeout)
                row = {"memory": memory, "bytes": n, "seconds": round(seconds, 2), "peak_mib": round(peak, 1)}
                if got is None:
                    row["result"] = f"over {timeout:g} s"
                else:
                    row["result"] = (
                        "same as native" if got == str(want) else f"MISMATCH lean={got} native={want}"
                    )
                    failed |= got != str(want)
                rows.append(row)
                seconds, peak = row["seconds"], row["peak_mib"]
                print(f"{memory:6} {n:>8} bytes  {seconds:>9} s  {peak:>8} MiB  {row['result']}")
                sys.stdout.flush()
                if got is None:
                    break
    if out:
        with open(out, "w") as f:
            json.dump(rows, f, indent=2)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
