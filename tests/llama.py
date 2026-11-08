#!/usr/bin/env python3
"""Proves a rewrite of llama.cpp's q4_K matrix kernels that clang -O3 misses, and writes down what it did.

From the pinned llama.cpp release, this compiles ggml's x86 kernels with the flags llama.cpp's own build uses
on a Zen 5 machine, and then:

1. Checks that `llc -O3` on the IR gives the same machine code as clang -O3, so the IR is what ships.
2. Rewrites each `pmaddwd` of eight summed `pmaddubsw` in the q4_K kernels as a chain of VNNI `vpdpbusd` and a
   multiply, with tests/llama/vnni.py, and checks that no other function's machine code changes.
3. Cuts each rewritten place out, before and after, with tests/llama/slices.py, and checks that every changed
   line is in one of those slices.
4. Translates each slice to Lean, and checks a theorem that the rewritten one gives the same result as clang's
   on every input, poison included, with only the standard axioms and what `bv_decide` adds.
5. Runs each slice pair natively against each other on random and extreme inputs, if this processor has
   AVX-512 VNNI. That's testing and not proof, but it doesn't depend on the Lean model.
6. Makes three wrong rewrites, and one change to clang's IR that breaks what the rewrite relies on, and checks
   that each stops the theorems, and that the native run catches it.

docs/llama.md has what this shows and what it assumes, and tests/llama_bench.py measures the speed.

usage: tests/llama.py path/to/ir-lean [--manifest FILE] [--keep DIR] [--no-mutants]
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "llama"
SOURCE = "ggml/src/ggml-cpu/arch/x86/repack.cpp"
FUNCTIONS = ["ggml_gemm_q4_K_8x8_q8_K", "ggml_gemv_q4_K_8x8_q8_K"]
PLACES = 34
# What llama.cpp's CMake passes for this file in a Release build with GGML_NATIVE, its default. On the Ryzen 9
# 9950X these were taken from, -march=native gives the same function bodies as -march=znver5, and naming the
# CPU makes the IR the same on any host. The frame pointer flags undo what the dev shell's compiler wrapper
# adds.
DEFINES = [
    "GGML_BACKEND_BUILD",
    "GGML_BACKEND_SHARED",
    "GGML_SCHED_MAX_COPIES=4",
    "GGML_SHARED",
    "GGML_USE_CPU_REPACK",
    "GGML_USE_LLAMAFILE",
    "_GNU_SOURCE",
    "_XOPEN_SOURCE=600",
    "ggml_cpu_EXPORTS",
]
INCLUDES = ["ggml/src/..", "ggml/src/.", "ggml/src/ggml-cpu", "ggml/src/../include"]
FLAGS = [
    "-fomit-frame-pointer",
    "-momit-leaf-frame-pointer",
    "-O3",
    "-DNDEBUG",
    "-std=gnu++17",
    "-fPIC",
    "-march=znver5",
]
LIMITS = ["-M", os.environ.get("LEAN_MAX_MB", "6000"), "-s", "65536"]


def found(m: re.Match[str] | None, what: str) -> re.Match[str]:
    """A match that has to be there."""
    if m is None:
        raise SystemExit(f"no {what}")
    return m


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(
    args: list, env: dict | None = None, cwd: Path | None = None, check: bool = True
) -> subprocess.CompletedProcess:
    r = subprocess.run([str(a) for a in args], env=env, cwd=cwd, capture_output=True, text=True, check=False)
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(map(str, args))}\n{r.stdout[-4000:]}{r.stderr[-4000:]}")
    return r


def compile_kernels(src: Path, work: Path) -> tuple[Path, Path]:
    """The IR, with use-list order so llc can reproduce clang's code exactly, and clang's own object."""
    env = {**os.environ, "NIX_HARDENING_ENABLE": ""}
    base = ["clang++", *[f"-D{d}" for d in DEFINES], *[f"-I{src / i}" for i in INCLUDES], *FLAGS]
    ll, obj = work / "repack.ll", work / "repack.clang.o"
    run([*base, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", ll, src / SOURCE], env)
    run([*base, "-c", "-o", obj, src / SOURCE], env)
    return ll, obj


def disassembly(obj: Path, function: str | None = None) -> str:
    """Machine code, without addresses or what only says where things are, so moving code isn't a change."""
    args = ["objdump", "-d", "--no-show-raw-insn", "--no-addresses"]
    if function:
        args.append(f"--disassemble={function}")
    text = run([*args, obj]).stdout
    text = "\n".join(text.splitlines()[6:])
    text = re.sub(r"\b[0-9a-f]+ <([^>+]+)(\+0x[0-9a-f]+)?>", r"<\1\2>", text)
    text = re.sub(r"-?0x[0-9a-f]+\(%rip\)", "D(%rip)", text)
    return re.sub(r"#.*$", "", text, flags=re.M)


def changed_functions(a: Path, b: Path) -> list[str]:
    names = sorted(
        {
            line.split()[2]
            for line in run(["nm", "--defined-only", a]).stdout.splitlines()
            if len(line.split()) == 3 and line.split()[1] in "Tt"
        }
    )
    return [f for f in names if disassembly(a, f) != disassembly(b, f)]


def rewrite(ll: Path, out: Path, report: Path, mutant: str | None = None) -> None:
    run(
        [
            sys.executable,
            HERE / "vnni.py",
            ll,
            out,
            *FUNCTIONS,
            "--report",
            report,
            *(["--mutant", mutant] if mutant else []),
        ]
    )
    run(["opt", "-passes=verify", "-disable-output", out])


def prove(tool: Path, slices: Path, work: Path) -> dict[str, dict]:
    """Translates each slice pair and checks its theorem. Returns, for each, its statement and axioms, or why
    it failed."""
    work.mkdir(parents=True, exist_ok=True)
    shutil.copy(ROOT / "lean-toolchain", work)
    env = {**os.environ, "LEAN_PATH": f"{work}:{ROOT}/.lake/build/lib/lean"}

    def lean(*a, stdin: str | None = None) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["lean", *LIMITS, *map(str, a)],
            cwd=work,
            env=env,
            input=stdin,
            capture_output=True,
            text=True,
            check=False,
        )

    shutil.copy(HERE / "Vnni.lean", work)
    r = lean("-DwarningAsError=true", "-o", work / "Vnni.olean", work / "Vnni.lean")
    if r.returncode != 0:
        raise RuntimeError(f"Vnni.lean:\n{r.stdout[-4000:]}{r.stderr[-4000:]}")
    index = json.loads((slices / "slices.json").read_text())
    check_axioms = (ROOT / "tests" / "check_axioms.lean").read_text()

    def one(entry: dict) -> tuple[str, dict]:
        name = entry["name"]
        S, T = f"{name.upper()}Src", f"{name.upper()}Tgt"
        for ns, kind in ((S, "src"), (T, "tgt")):
            run(
                [
                    tool,
                    slices / f"{name}.{kind}.ll",
                    "--namespace",
                    ns,
                    "--no-code",
                    "-o",
                    work / f"{ns}.lean",
                ]
            )
            r = lean("-o", work / f"{ns}.olean", work / f"{ns}.lean")
            if r.returncode != 0:
                return name, {"failure": f"{ns}: {r.stdout[-2000:]}"}
        src = (work / f"{S}.lean").read_text()
        sig = found(
            re.search(rf"noncomputable def {name}_src (.*?) : Outcome .* :=\n", src), "signature"
        ).group(1)
        args = " ".join(re.findall(r"\((\w+) : ", sig))
        theorem = f"T{name}"
        (work / f"{theorem}.lean").write_text(
            f"import Vnni\nimport {S}\nimport {T}\n\nopen IRLean Llama.Vnni\n\n"
            f"/-- {entry['value']} of `{entry['function']}`, rewritten, is what clang's IR computes. -/\n"
            f"theorem {name}_same {sig} :\n    {T}.{name}_tgt {args} = {S}.{name}_src {args} := by\n"
            f"  vnni_slice {T}.{name}_tgt {S}.{name}_src {T}.{name}_tgt.step {S}.{name}_src.step\n"
        )
        r = lean("-DwarningAsError=true", "-o", work / f"{theorem}.olean", work / f"{theorem}.lean")
        if r.returncode != 0:
            return name, {"failure": r.stdout[-3000:] + r.stderr[-1000:]}
        axioms = lean("--stdin", stdin=check_axioms.replace("MODULE", theorem))
        if axioms.returncode != 0:
            return name, {"failure": f"axioms: {axioms.stdout[-2000:]}{axioms.stderr[-2000:]}"}
        statement = lean(
            "--stdin", stdin=f"import {theorem}\nset_option pp.fullNames true\n#check @{name}_same\n"
        )
        return name, {
            "function": entry["function"],
            "value": entry["value"],
            "axioms": axioms.stdout.strip(),
            "statement": statement.stdout.strip(),
            "lean_sha256": {k: sha256(work / f"{k}.lean") for k in (S, T, theorem)},
        }

    jobs = int(os.environ.get("LEAN_JOBS", "4"))
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        return dict(pool.map(one, index))


def has_vnni() -> bool:
    try:
        return "avx512_vnni" in Path("/proc/cpuinfo").read_text()
    except OSError:
        return False


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument(
        "--keep", type=Path, help="work here and leave everything, instead of a temporary directory"
    )
    parser.add_argument("--no-mutants", action="store_true")
    args = parser.parse_args()
    tool = args.tool.resolve()
    src = Path(os.environ["LLAMA_CPP_SRC"])
    if args.keep:
        args.keep.mkdir(parents=True, exist_ok=True)
    work = args.keep.resolve() if args.keep else Path(tempfile.mkdtemp(prefix="llama-"))
    failures: list[str] = []
    manifest: dict = {
        "llama_cpp": str(src),
        "source": SOURCE,
        "source_sha256": sha256(src / SOURCE),
        "defines": DEFINES,
        "flags": FLAGS,
        "functions": FUNCTIONS,
        "clang": run(["clang++", "--version"]).stdout.splitlines()[0],
        "lean": run(["lean", "--version"]).stdout.strip(),
    }
    try:
        ll, clang_obj = compile_kernels(src, work)
        manifest["ir_sha256"] = sha256(ll)
        llc_obj = work / "repack.llc.o"
        run(["llc", "-O3", "-relocation-model=pic", "-filetype=obj", ll, "-o", llc_obj])
        same = disassembly(clang_obj) == disassembly(llc_obj)
        print(f"{'ok  ' if same else 'FAIL'} llc on the IR gives clang -O3's machine code", flush=True)
        if not same:
            failures.append("llc doesn't reproduce clang's machine code")

        rw, report = work / "repack.rw.ll", work / "report.json"
        rewrite(ll, rw, report)
        manifest["rewritten_ir_sha256"] = sha256(rw)
        places = len(json.loads(report.read_text()))
        rw_obj = work / "repack.rw.o"
        run(["llc", "-O3", "-relocation-model=pic", "-filetype=obj", rw, "-o", rw_obj])
        manifest["rewritten_object_sha256"] = sha256(rw_obj)
        changed = changed_functions(llc_obj, rw_obj)
        ok = places == PLACES and sorted(changed) == sorted(FUNCTIONS)
        print(
            f"{'ok  ' if ok else 'FAIL'} rewrote {places} places, and only these functions' code changed: "
            f"{', '.join(changed)}",
            flush=True,
        )
        if not ok:
            failures.append(f"{places} places, changed {changed}")

        slices = work / "slices"
        cover = run([sys.executable, HERE / "slices.py", ll, rw, report, slices], check=False)
        print(
            ("ok   " if cover.returncode == 0 else "FAIL ") + cover.stderr.strip().replace("\n", "\n     "),
            flush=True,
        )
        if cover.returncode != 0:
            failures.append("slices")
        manifest["slices_sha256"] = {p.name: sha256(p) for p in sorted(slices.glob("*.ll"))}

        results = prove(tool, slices, work / "lean")
        proved = [n for n, r in results.items() if "failure" not in r]
        print(
            f"{'ok  ' if len(proved) == PLACES else 'FAIL'} {len(proved)}/{PLACES} slice theorems checked, "
            f"{next(iter(results.values())).get('axioms', '')}",
            flush=True,
        )
        for name, r in sorted(results.items()):
            if "failure" in r:
                print(f"FAIL {name}:\n{r['failure'][:3000]}", flush=True)
        if len(proved) != PLACES:
            failures.append("theorems")
        manifest["theorems"] = results

        vnni = has_vnni()
        if vnni:
            native = run([sys.executable, HERE / "native_check.py", slices, work / "native"], check=False)
            print(
                f"{'ok  ' if native.returncode == 0 else 'FAIL'} natively: {native.stdout.strip()}",
                flush=True,
            )
            manifest["native"] = native.stdout.strip()
            if native.returncode != 0:
                failures.append("native")
        else:
            print("skip native comparison: this processor has no AVX-512 VNNI", flush=True)

        if not args.no_mutants:
            manifest["mutants"] = {}
            # A wrong rewrite, or IR that doesn't mask the weights to four bits, has to stop every theorem.
            masked = work / "repack.mask.ll"
            masked.write_text(
                ll.read_text()
                .replace("splat (i32 252645135)", "splat (i32 522133279)")
                .replace("splat (i16 3855)", "splat (i16 7967)")
            )
            for mutant, base in (("signs", ll), ("seven", ll), ("scale", ll), ("mask", masked)):
                d = work / f"mutant-{mutant}"
                d.mkdir(exist_ok=True)
                m_rw, m_report = d / "rw.ll", d / "report.json"
                rewrite(base, m_rw, m_report, None if mutant == "mask" else mutant)
                s = run([sys.executable, HERE / "slices.py", base, m_rw, m_report, d / "slices"], check=False)
                if s.returncode != 0:
                    print(f"FAIL mutant {mutant}: couldn't slice: {s.stderr[-1000:]}", flush=True)
                    failures.append(f"mutant {mutant}")
                    continue
                r = prove(tool, d / "slices", d / "lean")
                stopped = [n for n, x in r.items() if "failure" in x]
                caught = None
                if vnni:
                    caught = (
                        run(
                            [
                                sys.executable,
                                HERE / "native_check.py",
                                d / "slices",
                                d / "native",
                                "--runs",
                                "20000",
                            ],
                            check=False,
                        ).returncode
                        != 0
                    )
                ok = len(stopped) == len(r) and caught is not False
                print(
                    f"{'ok  ' if ok else 'FAIL'} mutant {mutant}: stops {len(stopped)}/{len(r)} theorems"
                    + (
                        ""
                        if caught is None
                        else f", and the native run {'catches' if caught else 'misses'} it"
                    ),
                    flush=True,
                )
                manifest["mutants"][mutant] = {"stopped": len(stopped), "of": len(r), "native_caught": caught}
                if not ok:
                    failures.append(f"mutant {mutant}")
                if not args.keep:
                    shutil.rmtree(d)
    except RuntimeError as error:
        failures.append(str(error)[:4000])
        print(f"FAIL {str(error)[:4000]}", flush=True)
    manifest["failures"] = failures
    if args.manifest:
        args.manifest.write_text(json.dumps(manifest, indent=1) + "\n")
    if not args.keep:
        shutil.rmtree(work, ignore_errors=True)
    print("ok" if not failures else f"FAIL: {failures}", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
