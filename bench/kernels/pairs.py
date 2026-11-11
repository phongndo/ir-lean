#!/usr/bin/env python3
"""Scalar and SIMD versions of one function from the kernel corpus, run against each other by tier-1 proof
tests' equivalence property. docs/proof-tests.md#memory-and-simd-measured has what it found.

zlib-ng ships a scalar CRC-32, `crc32_braid`, and SIMD ones, `crc32_pclmulqdq`, with SSE4.2 and PCLMULQDQ, and
`crc32_vpclmulqdq`, with AVX-512 and VPCLMULQDQ, all `uint32_t (uint32_t crc, const uint8_t *buf, size_t
len)`. libsodium ships BLAKE2b's compression function as `blake2b_compress_ref` and `blake2b_compress_avx2`,
both `int (blake2b_state *S, const uint8_t block[128])`, which update `S` in place. This:

1. Fetches each project at the pin bench/kernels/manifest.toml gives it, through Nix, and runs its configure
   step for the headers it generates, as bench/kernels/demand.py does.
2. Compiles each file to IR, with the flags the project's build gives that file, at the corpus's -O3 and
   relaxed, as demand.py's `relaxed` does, and links a project's files into one module with llvm-link, so both
   functions of a pair are in it.
3. Runs `tools/prooftest/prooftest.py` with `equivalence` on each pair: wherever the scalar one returns, the
   SIMD one returns the same and leaves the same memory.
4. Plants a bug, one 32-bit lane of the folding constant in `crc32_fold_pclmulqdq` wrong, `0x54442bd4` as
   `0x54442bd5`, the way a typo in `_mm_set_epi32` would make it, and runs the first pair again: it has to
   come back a counterexample.

Nothing it fetches or compiles is written into the repo: the work goes to build/kernels/pairs.

usage: bench/kernels/pairs.py [--max-inputs N] [--max-length N] [--seed N] [--workers N] [--work DIR]
                              [--check] [--offline]

`--check` exits 1 unless each pair passes tier 1 and the planted bug is refuted. `--offline` fetches nothing,
leaves out a project whose source isn't in the Nix store, and exits 77, which ctest takes as a skip, if
neither is.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
import demand  # noqa: E402
import kernels  # noqa: E402
from irlean import proc  # noqa: E402

PROOFTEST = ROOT / "tools" / "prooftest" / "prooftest.py"
WORK = ROOT / "build" / "kernels" / "pairs"
SKIP = 77
AVX512 = ["-mavx512f", "-mavx512dq", "-mavx512bw", "-mavx512vl", "-mbmi2", "-mtune=cascadelake", "-fno-lto"]
# Each project's pair: its files, with the flags its build gives each on x86-64, zlib-ng's read from its
# build.ninja and libsodium's from the manifest, on 2026-11-10; the module's namespace; the scalar function;
# and the SIMD ones.
PROJECTS: dict[str, dict[str, Any]] = {
    "zlib-ng": {
        "units": {
            "arch/generic/crc32_braid_c.c": [],
            "arch/x86/crc32_pclmulqdq.c": ["-msse4.2", "-mpclmul", "-fno-lto"],
            "arch/x86/crc32_vpclmulqdq.c": ["-mpclmul", "-mvpclmulqdq", *AVX512],
        },
        "namespace": "CrcPair",
        "reference": "crc32_braid",
        "simd": ["crc32_pclmulqdq", "crc32_vpclmulqdq"],
    },
    "libsodium": {
        "units": {
            "src/libsodium/crypto_generichash/blake2b/ref/blake2b-compress-ref.c": [],
            "src/libsodium/crypto_generichash/blake2b/ref/blake2b-compress-avx2.c": [
                "-msse2",
                "-mssse3",
                "-msse4.1",
                "-mavx",
                "-mavx2",
            ],
        },
        "namespace": "BlakePair",
        "reference": "blake2b_compress_ref",
        "simd": ["blake2b_compress_avx2"],
    },
}
# The planted bug: lane 2 of `xmm_fold4 = _mm_set_epi32(1, 0x54442bd4, 1, 0xc6e41596)`, which the IR holds as
# the high i64 of a <2 x i64>, 0x154442bd4.
PLANTED_IN = "crc32_fold_pclmulqdq"
PLANTED = ("i64 5708721108", "i64 5708721109")


def build(name: str, work: Path, offline: bool) -> Path | None:
    """A project's module, with each function of its pair, or None if `offline` and the source isn't in the
    Nix
    store."""
    manifest = kernels.load()
    project = manifest["project"][name]
    src = kernels.source(name, project, offline)
    if src is None:
        return None
    work.mkdir(parents=True, exist_ok=True)
    configured = demand.configure(name, project, src, work)
    where = {"src": str(src), "build": str(configured)}
    parts = []
    for source, flags in PROJECTS[name]["units"].items():
        ll = work / f"{Path(source).stem}.ll"
        argv = demand.command(manifest["corpus"], project, {"source": source, "flags": flags}, where, ll)
        argv[-5:-5] = [*demand.RELAX, *project.get("relax", [])]
        ran = proc.run(argv, env=demand.environment(), timeout=600)
        if not ran.ok:
            raise RuntimeError(f"{source} didn't compile\n{' '.join(argv)}\n{ran.err[-3000:]}")
        parts.append(ll)
    module = work / f"{PROJECTS[name]['namespace']}.ll"
    ran = proc.run(["llvm-link", "-S", "-o", module, *parts], timeout=600)
    if not ran.ok:
        raise RuntimeError(f"llvm-link failed\n{ran.err[-3000:]}")
    return module


def plant(module: Path) -> Path:
    """The module with one lane of the folding constant in `crc32_fold_pclmulqdq` wrong."""
    text = module.read_text()
    start = text.index(f"@{PLANTED_IN}(")
    start = text.rindex("\ndefine ", 0, start)
    end = text.index("\n}\n", start)
    body = text[start:end]
    if PLANTED[0] not in body:
        raise RuntimeError(f"{PLANTED_IN} doesn't have the constant this plants a bug in, {PLANTED[0]}")
    bug = module.with_name(f"{module.stem}Bug.ll")
    bug.write_text(text[:start] + body.replace(*PLANTED) + text[end:])
    return bug


def equivalence(
    module: Path, namespace: str, reference: str, simd: str, args: argparse.Namespace, work: Path
) -> dict[str, Any]:
    request = {
        "input": {"ir": str(module)},
        "namespace": namespace,
        "function": reference,
        "equivalence": {"with": simd, "max_length": args.max_length},
        "seed": args.seed,
        "max_inputs": args.max_inputs,
        "store": None,
        "limits": {"timeout_seconds": args.timeout},
    }
    directory = work / f"{module.stem}-{simd}"
    ran = proc.run(
        [sys.executable, PROOFTEST, "run", "-", "--work-dir", directory],
        stdin=json.dumps(request),
        timeout=args.timeout + 120,
    )
    try:
        return json.loads(ran.out)
    except json.JSONDecodeError:
        return {"status": "error", "reason": "no_json", "detail": ran.output[-2000:]}


def summary(name: str, result: dict[str, Any]) -> dict[str, Any]:
    inputs = result.get("inputs") or {}
    counterexample = result.get("counterexample") or {}
    return {
        "pair": name,
        "status": result.get("status"),
        "reason": result.get("reason"),
        "detail": result.get("detail"),
        "tried": inputs.get("tried"),
        "satisfied": inputs.get("satisfied"),
        "discarded": inputs.get("discarded"),
        "by_phase": inputs.get("by_phase"),
        "memory": inputs.get("memory"),
        "counterexample": counterexample.get("shown"),
        "evidence": counterexample.get("evidence"),
        "found": counterexample.get("found", {}).get("phase") if counterexample else None,
        "timing": result.get("timing"),
        "calls": (result.get("memory") or {}).get("calls"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--max-inputs", type=int, default=10_000)
    parser.add_argument("--max-length", type=int, default=2048)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--workers", type=int, default=2, help="proof tests at once, each one Lean at a time")
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    if demand.pinned_clang() is None:
        print("skip: this needs the pinned clang: run it in `nix develop`")
        return SKIP
    # (name, module, namespace, reference, simd, whether it's the planted bug)
    runs: list[tuple[str, Path, str, str, str, bool]] = []
    for name, pair in PROJECTS.items():
        module = build(name, args.work / name, args.offline)
        if module is None:
            print(f"skip {name}: its source isn't in the Nix store. `bench/kernels/pairs.py` fetches it")
            continue
        ns, reference = pair["namespace"], pair["reference"]
        runs += [(f"{reference} = {simd}", module, ns, reference, simd, False) for simd in pair["simd"]]
        if module.read_text().find(f"@{PLANTED_IN}(") >= 0:
            simd = pair["simd"][0]
            runs.append((f"{reference} = {simd}, planted bug", plant(module), ns, reference, simd, True))
    if not runs:
        return SKIP
    runs_dir = args.work / "runs"
    shutil.rmtree(runs_dir, ignore_errors=True)
    runs_dir.mkdir(parents=True)
    with ThreadPoolExecutor(max(1, args.workers)) as pool:
        results = list(
            pool.map(lambda r: summary(r[0], equivalence(r[1], r[2], r[3], r[4], args, runs_dir)), runs)
        )
    print(json.dumps(results, indent=2))
    if not args.check:
        return 0
    failed = [
        r["pair"]
        for r, run in zip(results, runs, strict=True)
        if r["status"] != ("counterexample" if run[5] else "passed_tier1")
    ]
    for name in failed:
        print(f"FAIL {name}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
