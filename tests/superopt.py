#!/usr/bin/env python3
"""Looks for smaller code than clang -O3 leaves, and only keeps what's proved to do the same.

For each function below, this runs the real compiled function on test inputs, and searches expressions over
LLVM's integer instructions, smallest first, for one that agrees. What it finds is written out as LLVM IR, and
has to pass Alive2, an independent checker, and a Lean theorem in tests/llvm/Rewrites.lean saying it gives the
same result as what clang left, for every input, with neither one undefined or poison. Agreeing on test inputs
says nothing by itself. `--bench` measures whether it's faster, and docs/llvm.md has the results.

usage: tests/superopt.py path/to/ir-lean [--bench] [--write]

`--write` updates tests/llvm/rewrites/ with what the search found. Without it, a difference is a failure.
"""

import argparse
import ctypes
import itertools
import os
import random
import re
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import alive
from llvm import LEAN_ERROR, LIMIT, PROOFS, ROOT, TIMEOUT_SECONDS, Pipeline, run

sys.path.append(str(ROOT / "tools"))
from irlean import proc
from irlean import verdict as core

REWRITES = PROOFS / "rewrites"

# module of tests/llvm/targets.toml, symbol, parameter width, result width, and the proof that module has
FUNCTIONS = [
    ("CrtClzsi2", "__clzsi2", 32, 32, "Clzsi2"),
    ("CrtCtzsi2", "__ctzsi2", 32, 32, "Ctzsi2"),
    ("CrtPopcountsi2", "__popcountsi2", 32, 32, "Popcountsi2"),
    ("CrtParitysi2", "__paritysi2", 32, 32, "Paritysi2"),
]


@dataclass(frozen=True)
class Expr:
    """An expression, with the IR for it as instructions leading up to `value`."""

    outputs: tuple[int, ...]
    ir: tuple[str, ...]
    value: str
    size: int


def inputs(width: int) -> list[int]:
    """Values that tell functions on bits apart: the edges, single bits, runs, and some random ones."""
    mask = (1 << width) - 1
    edge = {0, 1, 2, 3, mask, mask - 1, 1 << (width - 1)}
    edge |= {1 << i for i in range(width)} | {(1 << i) - 1 for i in range(width + 1)}
    rng = random.Random(0)
    edge |= {rng.getrandbits(width) for _ in range(256)}
    return sorted(edge)


def unary_ops(width: int) -> list[tuple[str, Callable[[int], int]]]:
    mask = (1 << width) - 1

    def clz(x: int) -> int:
        return width - x.bit_length()

    def ctz(x: int) -> int:
        return width if x == 0 else (x & -x).bit_length() - 1

    def rev(x: int) -> int:
        return int(f"{x:0{width}b}"[::-1], 2)

    return [
        (f"call i{width} @llvm.ctlz.i{width}(i{width} {{a}}, i1 false)", clz),
        (f"call i{width} @llvm.cttz.i{width}(i{width} {{a}}, i1 false)", ctz),
        (f"call i{width} @llvm.ctpop.i{width}(i{width} {{a}})", lambda x: x.bit_count()),
        (f"call i{width} @llvm.bitreverse.i{width}(i{width} {{a}})", rev),
        (f"xor i{width} {{a}}, -1", lambda x: ~x & mask),
        (f"sub i{width} 0, {{a}}", lambda x: -x & mask),
    ]


def binary_ops(width: int) -> list[tuple[str, Callable[[int, int], int | None]]]:
    mask = (1 << width) - 1
    return [
        (f"add i{width} {{a}}, {{b}}", lambda x, y: (x + y) & mask),
        (f"sub i{width} {{a}}, {{b}}", lambda x, y: (x - y) & mask),
        (f"and i{width} {{a}}, {{b}}", lambda x, y: x & y),
        (f"or i{width} {{a}}, {{b}}", lambda x, y: x | y),
        (f"xor i{width} {{a}}, {{b}}", lambda x, y: x ^ y),
        (f"shl i{width} {{a}}, {{b}}", lambda x, y: (x << y) & mask if y < width else None),
        (f"lshr i{width} {{a}}, {{b}}", lambda x, y: x >> y if y < width else None),
    ]


def search(goal: tuple[int, ...], values: list[int], width: int, limit: int = 3) -> Expr | None:
    """Enumerates expressions by size, keeping one per behavior on `values`, until one matches `goal`."""
    mask = (1 << width) - 1
    constants = [0, 1, 2, width - 1, width, mask]
    seed = [Expr(tuple(values), (), "%a", 0)] + [
        Expr(tuple(c for _ in values), (), str(c if c != mask else -1), 0) for c in constants
    ]
    # Only `%a` counts as an answer of size 0: a constant can't be what's wanted of a function of its input.
    seen = {e.outputs: e for e in seed}
    by_size: dict[int, list[Expr]] = {0: seed}
    counter = itertools.count()

    def fresh(template: str, a: Expr, b: Expr | None, outputs: tuple[int, ...]) -> Expr:
        name = f"%v{next(counter)}"
        line = f"{name} = " + template.format(a=a.value, b=b.value if b else "")
        return Expr(outputs, (*a.ir, *(b.ir if b else ()), line), name, a.size + (b.size if b else 0) + 1)

    for size in range(1, limit + 1):
        found: list[Expr] = []
        for template, f in unary_ops(width):
            for a in by_size.get(size - 1, []):
                outputs = tuple(f(x) for x in a.outputs)
                if outputs not in seen:
                    seen[outputs] = fresh(template, a, None, outputs)
                    found.append(seen[outputs])
        for template, g in binary_ops(width):
            for left in range(size):
                for a, b in itertools.product(by_size.get(left, []), by_size.get(size - 1 - left, [])):
                    results = [g(x, y) for x, y in zip(a.outputs, b.outputs, strict=True)]
                    if None in results:
                        continue
                    outputs = tuple(r for r in results if r is not None)
                    if outputs not in seen:
                        seen[outputs] = fresh(template, a, b, outputs)
                        found.append(seen[outputs])
        by_size[size] = found
        if goal in seen and seen[goal].size == size:
            return seen[goal]
    return None


def module_text(symbol: str, width: int, result: int, expr: Expr) -> str:
    declares = {
        f"declare i{width} @llvm.{name}.i{width}({args})"
        for name, args in [
            ("ctlz", f"i{width}, i1"),
            ("cttz", f"i{width}, i1"),
            ("ctpop", f"i{width}"),
            ("bitreverse", f"i{width}"),
        ]
        if any(f"@llvm.{name}." in line for line in expr.ir)
    }
    # The search numbers everything it tries. These are the ones that ended up here.
    body = "\n".join(f"  {line}" for line in expr.ir)
    value = expr.value
    names = re.findall(r"^%v\d+", "\n".join(expr.ir), re.M)
    for i, name in enumerate(names):
        body = re.sub(rf"{name}\b", f"%r{i}", body)
        value = re.sub(rf"{name}\b", f"%r{i}", value)
    return (
        f"; What tests/superopt.py found for {symbol}, which tests/llvm/Rewrites.lean proves does the same.\n"
        + 'target triple = "x86_64-unknown-linux-gnu"\n\n'
        + "".join(f"{d}\n" for d in sorted(declares))
        + f"\ndefine i{result} @{symbol}(i{width} noundef %a) {{\nentry:\n{body}\n"
        + f"  ret i{result} {value}\n}}\n"
    )


def native(pipeline: Pipeline, target: dict, directory: Path, name: str) -> ctypes.CDLL:
    """The function as clang compiled it, to run."""
    flags = pipeline.config["flags"][target["flags"]]
    includes = [f"-I{pipeline.src / i}" for i in flags.get("include", [])]
    library = directory / f"{name}.so"
    source = pipeline.src / target["source"]
    run(
        [
            "clang",
            "-shared",
            *flags["args"],
            *includes,
            "-fvisibility=default",
            "-o",
            str(library),
            str(source),
        ]
    )
    return ctypes.CDLL(str(library))


def bench(
    symbol: str, directory: Path, target: dict, pipeline: Pipeline, rewrite: Path, march: list[str]
) -> tuple[list[float], int, int]:
    """Times both versions through a pointer, on the same inputs, in separate runs of a driver, since one
    run can land on a lucky or unlucky code layout. Returns how many times faster each run was, and
    instruction counts."""
    flags = pipeline.config["flags"][target["flags"]]
    includes = [f"-I{pipeline.src / i}" for i in flags.get("include", [])]
    source = pipeline.src / target["source"]
    src = directory / "src.o"
    tgt = directory / "tgt.o"
    run(
        [
            "clang",
            *march,
            *flags["args"],
            *includes,
            "-fvisibility=default",
            "-c",
            "-o",
            str(src),
            str(source),
        ]
    )
    run(["clang", *march, "-O3", "-Wno-override-module", "-c", "-o", str(tgt), str(rewrite)])
    run(["objcopy", "--redefine-sym", f"{symbol}=src_fn", str(src)])
    run(["objcopy", "--redefine-sym", f"{symbol}=tgt_fn", str(tgt)])
    driver = directory / "driver.c"
    driver.write_text(DRIVER)
    program = directory / "driver"
    run(["clang", "-O3", "-o", str(program), str(driver), str(src), str(tgt)])
    ratios = []
    for _ in range(BENCH_RUNS):
        report = [float(v) for v in run([str(program)]).split()]
        ratios.append(report[0] / report[1])

    def instructions(path: Path) -> int:
        return sum(
            1 for line in run(["objdump", "-d", str(path)]).splitlines() if re.match(r"\s+[0-9a-f]+:\t", line)
        )

    return sorted(ratios), instructions(src), instructions(tgt)


BENCH_RUNS = 15

DRIVER = """
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
extern int src_fn(int), tgt_fn(int);
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}
static int cmp(const void *a, const void *b) {
  double x = *(double *)a, y = *(double *)b;
  return x < y ? -1 : x > y;
}
int main(void) {
  enum { N = 1 << 20, R = 41 };
  static int in[N];
  uint64_t s = 88172645463325252ULL;
  for (int i = 0; i < N; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    in[i] = (int)(((uint32_t)s) >> ((s >> 58) % 32)) | 1;
  }
  static double a[R], b[R];
  volatile int sink = 0;
  int (*volatile fa)(int) = src_fn;
  int (*volatile fb)(int) = tgt_fn;
  for (int r = 0; r < R; r++) {
    int (*f)(int) = fa; int acc = 0; double t0 = now();
    for (int i = 0; i < N; i++) acc += f(in[i]);
    a[r] = (now() - t0) / N; sink += acc;
    f = fb; acc = 0; t0 = now();
    for (int i = 0; i < N; i++) acc += f(in[i]);
    b[r] = (now() - t0) / N; sink += acc;
  }
  qsort(a, R, sizeof(double), cmp);
  qsort(b, R, sizeof(double), cmp);
  printf("%.3f %.3f\\n", a[R / 2], b[R / 2]);
  return sink == 123456789;
}
"""


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    parser.add_argument("--bench", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    config = tomllib.loads((PROOFS / "targets.toml").read_text())
    targets = {t["module"]: t for t in config["target"]}
    failed = False

    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        pipeline = Pipeline(args.tool.resolve(), work, config)
        (work / "support").mkdir()
        for module in config.get("support", []):
            pipeline.compile_lean(work, PROOFS / f"{module}.lean", PROOFS)

        # Each theorem in Rewrites.lean says a rewrite does what clang left, so it has to name both functions.
        theorems = []
        for module, symbol, width, result, proof in FUNCTIONS:
            target = targets[module]
            library = native(pipeline, target, work, module)
            function = getattr(library, symbol)
            function.argtypes = [ctypes.c_uint32]
            function.restype = ctypes.c_uint32
            values = inputs(width)
            started = time.monotonic()
            found = search(tuple(function(x) for x in values), values, width)
            if found is None:
                print(f"none  {symbol}: nothing that small agrees")
                continue
            seconds = time.monotonic() - started
            text = module_text(symbol, width, result, found)
            rewrite = REWRITES / f"{proof}.ll"
            if args.write:
                rewrite.write_text(text)
            elif not rewrite.exists() or rewrite.read_text() != text:
                print(f"FAIL  {symbol}: the search now finds something else:\n{text}")
                failed = True
                continue
            print(f"found {symbol} in {seconds:.1f}s, {found.size} instructions: {'; '.join(found.ir)}")

            # An independent check of what the search found, against what clang left.
            original = pipeline.generate(target, work).get(symbol, (False, "it isn't in the IR"))
            try:
                output = run(["alive-tv", "--disable-undef-input", str(work / f"{module}.ll"), str(rewrite)])
            except RuntimeError as error:
                print(f"FAIL  {symbol}: Alive2 didn't accept it: {str(error)[:1000]}")
                failed = True
                continue
            # alive-tv exits 0 when its solver times out, so only its count of what it proved says it agrees.
            if alive.verdict(output) != "correct":
                print(f"FAIL  {symbol}: Alive2 doesn't prove it:\n{output[-1000:]}")
                failed = True
                continue
            print(f"ok    {symbol}: Alive2 agrees")
            pipeline.compile_lean(work, PROOFS / f"{proof}.lean", PROOFS)
            generated = work / f"Rw{proof}.lean"
            subprocess.run(
                [
                    str(pipeline.tool),
                    str(rewrite),
                    "--namespace",
                    f"Rw{proof}",
                    "-o",
                    str(generated),
                    "--no-code",
                ],
                check=True,
                capture_output=True,
            )
            pipeline.lean(work, "-R", str(work), "-o", str(work / f"Rw{proof}.olean"), str(generated))
            report = run([str(pipeline.tool), str(rewrite), "--namespace", f"Rw{proof}", "--report"])
            lean_name = next(
                (f[2] for f in (line.split("\t") for line in report.splitlines()) if f[:2] == ["ok", symbol]),
                None,
            )
            if not original[0] or lean_name is None:
                print(f"FAIL  {symbol}: ir-lean left out what clang left or the rewrite: {original[1]}")
                failed = True
                continue
            same = f"{symbol.lstrip('_')}_same"
            theorems += [f"{same} {module}.{original[1]}", f"{same} Rw{proof}.{lean_name}"]

            if args.bench:
                for march in ([], ["-march=x86-64-v3"]):
                    ratios, before, after = bench(symbol, work, target, pipeline, rewrite, march)
                    verdict = "faster in every run" if ratios[0] > 1 else "not clearly faster"
                    median = statistics.median(ratios)
                    print(
                        f"bench {symbol} {' '.join(march) or 'x86-64'}: {before} instructions to {after}, "
                        f"{ratios[0]:.2f}x to {ratios[-1]:.2f}x, median {median:.2f}x, {verdict}"
                    )

        try:
            compiled = pipeline.compile_ran(work, PROOFS / "Rewrites.lean", PROOFS)
            namespaces = " ".join(n for f in FUNCTIONS for n in (f[0], f"Rw{f[4]}"))
            axioms, proved = pipeline.proved(
                work, compiled, "Rewrites", namespaces, "\n".join(theorems), tuple(config.get("support", []))
            )
            if not proved.granted:
                raise RuntimeError(f"Rewrites.lean isn't proved: {proved.detail}")
            print(f"ok    Rewrites.lean (axioms: {axioms})")
        except RuntimeError as error:
            print(f"FAIL  Rewrites.lean\n{str(error)[:4000]}")
            failed = True

        # The theorem has to depend on the rewrite. A wrong one must stop it, and Alive2 has to say so too.
        wrong = work / "wrong"
        wrong.mkdir()
        wrong_ir = wrong / "RwClzsi2.ll"
        wrong_ir.write_text((REWRITES / "Clzsi2.ll").read_text().replace("ctlz", "cttz"))
        subprocess.run(
            [
                str(pipeline.tool),
                str(wrong_ir),
                "--namespace",
                "RwClzsi2",
                "-o",
                str(wrong / "RwClzsi2.lean"),
                "--no-code",
            ],
            check=True,
            capture_output=True,
        )
        pipeline.lean(
            wrong, "-R", str(wrong), "-o", str(wrong / "RwClzsi2.olean"), str(wrong / "RwClzsi2.lean")
        )
        result = proc.run(
            ["lean", "-M", pipeline.memory, str(PROOFS / "Rewrites.lean")],
            env={**os.environ, "LEAN_PATH": f"{wrong}:{work}:{ROOT}/.lake/build/lib/lean"},
            timeout=TIMEOUT_SECONDS,
        )
        wrong_alive = proc.run(
            ["alive-tv", "--disable-undef-input", str(work / "CrtClzsi2.ll"), str(wrong_ir)],
            timeout=alive.TIMEOUT_SECONDS,
        )
        # Running out of time or memory says the theorem might still check, so only another error counts.
        errors = [line for line in result.out.splitlines() if LEAN_ERROR.match(line)]
        own = [e for e in errors if not LIMIT.search(e)]
        lean_caught = core.decide(
            core.Verdict.CAUGHT,
            core.Evidence(step=core.Step.of("lean", result), finding=own[0] if own else None),
        )
        # alive-tv exits 0 whatever it found, so what it found is in its summary.
        alive_caught = core.decide(
            core.Verdict.CAUGHT,
            core.Evidence(
                step=core.Step.of("alive-tv", wrong_alive),
                found_exit=0,
                finding="incorrect" if alive.verdict(wrong_alive.out) == "incorrect" else None,
            ),
        )
        if result.exit == 0:
            print("FAIL  a wrong rewrite still passes the Lean theorem")
            failed = True
        elif not lean_caught.granted:
            print(
                f"FAIL  unknown whether a wrong rewrite stops the theorem, since {lean_caught.detail}:\n"
                f"{result.out[:1000]}"
            )
            failed = True
        elif not alive_caught.granted:
            print(f"FAIL  Alive2 didn't reject a wrong rewrite:\n{wrong_alive.out[:1000]}")
            failed = True
        else:
            print("ok    a wrong rewrite stops the theorem, and Alive2 rejects it")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
