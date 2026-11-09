#!/usr/bin/env python3
"""Measures tests/llama.py's rewrite on real llama.cpp inference, against the same clang -O3 build.

This builds the pinned llama.cpp with its own CMake, the way its README says, in Release with GGML_NATIVE on,
its default, using the dev shell's clang. Then:

1. Takes the IR of ggml's x86 kernels from that build's own compile command, checks that `llc -O3` gives the
   machine code the build has, and that its functions are the ones tests/llama.py proves things about.
2. Rewrites it with tests/llama/vnni.py, and links a second libggml-cpu.so from it with the build's own link
   command. The two libraries differ only in the two q4_K kernels, which this checks.
3. For each model, runs llama-perplexity with each library and checks the logits are the same, bit for bit.
4. Times each workload with each library, alternating which goes first, on the same binaries with only
   libggml-cpu.so.0 swapped, under `perf stat`.

It needs an x86 processor with AVX-512 VNNI, and GGUF models: docs/llama.md says which were used.

usage: tests/llama_bench.py MODEL.gguf... [--rounds N] [--cpus 0-7] [--threads 8] [--text FILE]
                            [--workloads pp512,ppl,tg128] [--work DIR] [--csv FILE] [--skip-logits]
       tests/llama_bench.py --summary FILE.csv
"""

import argparse
import csv
import json
import os
import re
import shlex
import shutil
import statistics
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import llama  # noqa: E402

sys.path.append(str(ROOT / "tools"))
from irlean import hashing, proc  # noqa: E402

ENV = {
    **os.environ,
    # The dev shell's compiler wrapper drops -march=native, and adds hardening and frame pointers that stock
    # clang doesn't. Nix also sets SOURCE_DATE_EPOCH, which turns GGML_NATIVE off. Undo all of it.
    "NIX_ENFORCE_NO_NATIVE": "0",
    "NIX_HARDENING_ENABLE": "",
    "CC": "clang",
    "CXX": "clang++",
    "CFLAGS": "-fomit-frame-pointer -momit-leaf-frame-pointer",
    "CXXFLAGS": "-fomit-frame-pointer -momit-leaf-frame-pointer",
}
ENV.pop("SOURCE_DATE_EPOCH", None)
OBJECT = "ggml/src/CMakeFiles/ggml-cpu.dir/ggml-cpu/arch/x86/repack.cpp.o"
LIBRARY = "bin/libggml-cpu.so.0"


def sh(args, cwd=None, env=ENV, check=True, **kw) -> proc.Ran:
    r = proc.run([str(a) for a in args], cwd=cwd, env=env, **kw)
    if check and r.exit != 0:
        raise SystemExit(f"{' '.join(map(str, args))}\n{r.out[-3000:]}{r.err[-3000:]}")
    return r


def bodies(ll: Path) -> str:
    """The IR without attribute groups, which only differ in how target features are spelled."""
    return "\n".join(
        line
        for line in ll.read_text().splitlines()
        if not line.startswith(("attributes #", "; ModuleID", "source_filename"))
    )


def build(work: Path) -> tuple[Path, Path, Path]:
    """Builds llama.cpp, and the second library. Returns the build, and the two libraries."""
    src = Path(os.environ["LLAMA_CPP_SRC"])
    b = work / "build"
    if not (b / "bin" / "llama-bench").exists():
        sh(
            [
                "cmake",
                "-S",
                src,
                "-B",
                b,
                "-G",
                "Ninja",
                "-DCMAKE_BUILD_TYPE=Release",
                "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                "-DLLAMA_CURL=OFF",
                "-DGGML_CCACHE=OFF",
            ]
        )
        sh(["ninja", "-C", b, "llama-bench", "llama-perplexity"])
    command = next(
        e for e in json.loads((b / "compile_commands.json").read_text()) if e["file"].endswith(llama.SOURCE)
    )
    args = shlex.split(command["command"])
    if "-march=native" not in args:
        raise SystemExit(f"the build didn't use -march=native: {command['command']}")
    out = args.index("-o")
    del args[out : out + 2]
    args.remove("-c")
    ll = work / "repack.ll"
    sh([*args, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", ll], cwd=b)
    built = b / OBJECT
    llc = work / "repack.llc.o"
    sh(["llc", "-O3", "-relocation-model=pic", "-filetype=obj", ll, "-o", llc])
    if llama.disassembly(built) != llama.disassembly(llc):
        raise SystemExit("llc on the IR doesn't give the build's machine code")
    proved = work / "proved"
    proved.mkdir(exist_ok=True)
    proved_ll, _ = llama.compile_kernels(src, proved)
    if bodies(ll) != bodies(proved_ll):
        raise SystemExit("this build's kernels aren't the IR tests/llama.py proves things about")
    rw, report = work / "repack.rw.ll", work / "report.json"
    llama.rewrite(ll, rw, report)
    rw_obj = work / "repack.rw.o"
    sh(["llc", "-O3", "-relocation-model=pic", "-filetype=obj", rw, "-o", rw_obj])
    link = (
        sh(["ninja", "-C", b, "-t", "commands", "bin/" + os.readlink(b / LIBRARY)])
        .out.strip()
        .splitlines()[-1]
    )
    if OBJECT not in link:
        raise SystemExit(f"can't find {OBJECT} in the link command")
    libs = work / "libs"
    for v in ("base", "rw"):
        (libs / v).mkdir(parents=True, exist_ok=True)
    out_lib = libs / "rw" / "libggml-cpu.so.0"
    link = link.replace(OBJECT, str(rw_obj)).replace(f"-o bin/{os.readlink(b / LIBRARY)}", f"-o {out_lib}")
    sh(["bash", "-c", link], cwd=b)
    shutil.copy(b / LIBRARY, libs / "base" / "libggml-cpu.so.0")
    changed = llama.changed_functions(libs / "base" / "libggml-cpu.so.0", out_lib)
    if sorted(changed) != sorted(llama.FUNCTIONS):
        raise SystemExit(f"the libraries differ in {changed}")
    print(f"ok   built both libraries; they differ only in {', '.join(changed)}", flush=True)
    return b, libs / "base", libs / "rw"


def logits_match(b: Path, libs: dict, model: Path, text: Path, work: Path, cpus: str, threads: int) -> bool:
    files = {}
    for v, lib in libs.items():
        files[v] = work / f"logits-{v}.bin"
        sh(
            [
                "taskset",
                "-c",
                cpus,
                b / "bin" / "llama-perplexity",
                "-m",
                model,
                "-f",
                text,
                "-t",
                threads,
                "-c",
                "512",
                "--chunks",
                "16",
                "--kl-divergence-base",
                files[v],
            ],
            env={**ENV, "LD_LIBRARY_PATH": lib},
        )
    same = sh(["cmp", files["base"], files["rw"]], check=False).exit == 0
    size = files["base"].stat().st_size
    for f in files.values():
        f.unlink()
    print(
        f"{'ok  ' if same else 'FAIL'} {model.name}: logits for 16 chunks of 512 tokens, {size} bytes, "
        f"{'the same' if same else 'differ'}",
        flush=True,
    )
    return same


def perf(path: Path) -> dict:
    v = {}
    for line in path.read_text().splitlines():
        p = line.split(",")
        if len(p) > 2 and p[0] and p[0][0].isdigit():
            v[p[2].split(":")[0]] = float(p[0])
    return v


def timed(
    b: Path, lib: Path, model: Path, workload: str, text: Path, cpus: str, threads: int, work: Path
) -> dict:
    stat = work / "perf.csv"
    pre = ["perf", "stat", "-x,", "-e", "cycles,task-clock", "-o", stat, "taskset", "-c", cpus]
    env = {**ENV, "LD_LIBRARY_PATH": lib}
    load = Path("/proc/loadavg").read_text().split()[0]
    t0 = time.monotonic()
    if workload in ("pp512", "tg128"):
        p, n = ("512", "0") if workload == "pp512" else ("0", "128")
        out = sh(
            [
                *pre,
                b / "bin" / "llama-bench",
                "-m",
                model,
                "-t",
                threads,
                "-p",
                p,
                "-n",
                n,
                "-r",
                "3",
                "-o",
                "csv",
            ],
            env=env,
        ).out
        metric = float(list(csv.DictReader(out.splitlines()))[-1]["avg_ts"])
    else:
        out = sh(
            [
                *pre,
                b / "bin" / "llama-perplexity",
                "-m",
                model,
                "-f",
                text,
                "-t",
                threads,
                "-c",
                "512",
                "--chunks",
                "24",
            ],
            env=env,
        ).err
        metric = float(re.findall(r"PPL = ([0-9.]+)", out)[-1])
    wall = time.monotonic() - t0
    p = perf(stat)
    return {
        "metric": metric,
        "wall_s": round(wall, 3),
        "cycles": p.get("cycles", 0),
        "task_clock_ms": p.get("task-clock", 0),
        "load1": load,
    }


def summary(rows: list[dict]) -> list[str]:
    """For each model and workload: the median of each variant, the rewritten one's speedup in each round
    (median, least and most), and in how many rounds it was faster."""
    out = ["model, workload: median base, median rewritten, speedups (median, least, most), rounds faster"]
    for model in dict.fromkeys(x["model"] for x in rows):
        for workload in dict.fromkeys(x["workload"] for x in rows):
            picked = [x for x in rows if x["model"] == model and x["workload"] == workload]
            a = {int(x["round"]): x for x in picked if x["variant"] == "base"}
            c = {int(x["round"]): x for x in picked if x["variant"] == "rw"}
            rounds = sorted(set(a) & set(c))
            if not rounds:
                continue
            # Perplexity is a fixed amount of work, so its speed is in wall time. The others report tokens/s.
            key = "wall_s" if workload == "ppl" else "metric"
            value = {r: (float(a[r][key]), float(c[r][key])) for r in rounds}
            if workload == "ppl":
                speedups = [x / y for x, y in value.values()]
                unit = "s"
                perplexities = {a[r]["metric"] for r in rounds} | {c[r]["metric"] for r in rounds}
                note = f", perplexity {sorted(perplexities)}"
            else:
                speedups = [y / x for x, y in value.values()]
                unit = "tokens/s"
                note = ""
            base = statistics.median(x for x, _ in value.values())
            rewritten = statistics.median(y for _, y in value.values())
            out.append(
                f"{model}, {workload}: {base:.2f} {unit}, {rewritten:.2f} {unit}, "
                f"{statistics.median(speedups):.3f} ({min(speedups):.3f}, {max(speedups):.3f}), "
                f"{sum(s > 1 for s in speedups)}/{len(rounds)}{note}"
            )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("models", type=Path, nargs="*")
    parser.add_argument("--summary", type=Path, help="print the summary of an earlier run's --csv, and stop")
    parser.add_argument("--rounds", type=int, default=10)
    parser.add_argument("--cpus", default="0-7")
    parser.add_argument("--threads", type=int, default=8)
    parser.add_argument("--text", type=Path, help="text for perplexity, such as WikiText-2's wiki.test.raw")
    parser.add_argument("--workloads", default="pp512,ppl,tg128")
    parser.add_argument("--work", type=Path)
    parser.add_argument("--csv", type=Path)
    parser.add_argument("--skip-logits", action="store_true")
    args = parser.parse_args()
    if args.summary:
        with open(args.summary, newline="") as f:
            print("\n".join(summary(list(csv.DictReader(f)))))
        return 0
    if "avx512_vnni" not in Path("/proc/cpuinfo").read_text():
        raise SystemExit("this processor has no AVX-512 VNNI, which the rewritten kernels use")
    work = (args.work or Path(tempfile.mkdtemp(prefix="llama-bench-"))).resolve()
    work.mkdir(parents=True, exist_ok=True)
    b, base, rw = build(work)
    libs = {"base": base, "rw": rw}
    for m in args.models:
        print(f"     {m.name}: sha256 {hashing.sha256_file(m)}", flush=True)
    workloads = args.workloads.split(",")
    if "ppl" in workloads and not args.text:
        raise SystemExit("perplexity needs --text")
    if not args.skip_logits:
        if not args.text:
            raise SystemExit("checking logits needs --text")
        if not all(logits_match(b, libs, m, args.text, work, args.cpus, args.threads) for m in args.models):
            return 1
    rows = []
    for r in range(1, args.rounds + 1):
        order = ["base", "rw"] if r % 2 else ["rw", "base"]
        for m in args.models:
            for w in workloads:
                for v in order:
                    row = {
                        "round": r,
                        "variant": v,
                        "model": m.name,
                        "workload": w,
                        **timed(b, libs[v], m, w, args.text, args.cpus, args.threads, work),
                    }
                    rows.append(row)
                    print(",".join(str(x) for x in row.values()), flush=True)
        if args.csv:
            with open(args.csv, "w", newline="") as f:
                writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
                writer.writeheader()
                writer.writerows(rows)
    print("\n".join(summary(rows)), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
