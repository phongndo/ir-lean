#!/usr/bin/env python3
"""Checks the kernel corpus's benchmark harness, bench/kernels/harness.py, and the rule it reads comparisons
by, bench/kernels/protocol.py, with no project downloaded. docs/kernels.md, "The harness".

First, on numbers alone: a ratio is above 1 when the candidate is faster, for a time and for a rate; the
bootstrap gives the interval tests/llama/measure.py recorded for the Q5 rewrite from the same pairs and seed;
the Q5 rewrite's confirmation sessions are measurably faster by the rule, as docs/kernels.md says; each of
the rule's four conditions, and the protocol's minimums, turns a win into an inconclusive verdict when it
fails; and a mirror image of a win is slower.

Then, on Linux, the harness end to end on tests/kernels_bench/, a tiny make project whose hot unit is
kernel.c. It builds the baseline, and candidates, each through the checks a real one passes: a control the
same as the baseline, which has to differ from it in nothing, and a rewrite of `kernel` with a deliberate
extra loop, given as IR. A rewrite that declares the wrong function, and one whose output is wrong, have to
be refused. Then it times them by the protocol, on one core of the first CCD, with runs repeated to 0.05 s
instead of 2 s, so it takes seconds: the control the same as the baseline has to come out inconclusive, the
extra loop slower, and the baseline against the extra loop faster, with the project's other workload measured
and not slower. Read by the protocol's own rule, none of these is by the protocol, and the board refuses a
win that cites one.

Exits 77, which ctest takes as a skip, if the numbers pass and the end-to-end part can't run here: not on
Linux, or without clang, llc, opt, objdump and make on PATH.

usage: tests/kernels_bench_test.py
"""

from __future__ import annotations

import contextlib
import copy
import importlib.util
import json
import shutil
import sys
import tempfile
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "bench" / "kernels"
sys.path.append(str(ROOT / "tools"))
# The harness's scripts import each other as scripts beside each other do.
sys.path.append(str(HERE))
from irlean import hashing, pins, proc, schemas  # noqa: E402


def load(name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


kernels = load("kernels")
protocol = load("protocol")
harness = load("harness")
board = load("board")

SPEC = ROOT / "tests" / "kernels_bench" / "project.toml"
Q5 = ROOT / "tests" / "llama" / "results" / "2026-11-07"
SKIP = 77
# The test's own rule: the protocol's, but for how long a run is repeated to, so the test takes seconds.
FAST = protocol.Rule(min_seconds=0.05)

failures: list[str] = []


def expect(ok: bool, what: str, detail: Any = "") -> None:
    print(f"{'ok  ' if ok else 'FAIL'} {what}" + (f": {detail}" if detail and not ok else ""), flush=True)
    if not ok:
        failures.append(what)


# ------------------------------------------------------------------------------------------------------------
# The rule, on numbers


def wobble(center: float, n: int, spread: float = 0.004) -> list[float]:
    """`n` ratios around `center`, spread evenly, as a session's might be."""
    return [center + spread * ((i * 7) % n - n / 2) / n for i in range(n)]


def numbers() -> None:
    expect(protocol.ratio(2.0, 1.0, protocol.TIME) == 2.0, "a time halved is a ratio of 2")
    expect(protocol.ratio(100.0, 200.0, protocol.RATE) == 2.0, "a rate doubled is a ratio of 2")
    for bad in ((0.0, 1.0), (1.0, -1.0)):
        with contextlib.suppress(ValueError):
            protocol.ratio(*bad, protocol.TIME)
            expect(False, f"a ratio of {bad} is refused")

    # The Q5 rewrite's pooled interval of inference time, the first metric tests/llama/measure.py pooled, from
    # a fresh generator with its recorded seed: the same pairs and seed give the same interval here.
    pooled = json.loads((Q5 / "pooled-confirmation.json").read_text())
    expect(next(iter(pooled["metrics"])) == "total_ms", "the Q5 record pooled inference time first")
    total = pooled["metrics"]["total_ms"]
    got = protocol.interval(total["paired_ratios"], pooled["bootstrap_seed"])
    expect(
        list(got) == total["bootstrap_median_95_percent"],
        "the bootstrap gives the Q5 rewrite's recorded interval from its pairs and seed",
        f"{got} against {total['bootstrap_median_95_percent']}",
    )

    # Its two confirmation sessions of 12 and 18 pairs, by the rule.
    sessions = json.loads((Q5 / "sessions.json").read_text())
    picked = [sessions[name]["summary"]["total_ms"]["paired_ratios"] for name in pooled["sessions"]]
    q5 = protocol.verdict(picked, [protocol.CONFIRMATION] * 2, pooled["bootstrap_seed"], {})
    expect(
        q5["verdict"] == protocol.FASTER and [len(s) for s in picked] == [12, 18],
        "the Q5 rewrite's 30 pairs of inference time are measurably faster, as docs/kernels.md says",
        q5["conditions"],
    )
    expect(
        round(q5["pooled"]["median"], 3) == 1.049
        and q5["pooled"]["interval"] == total["bootstrap_median_95_percent"],
        "with the 1.049 and the interval docs/llama-q5.md has",
        q5["pooled"],
    )

    win = [wobble(1.02, 15), wobble(1.021, 15)]
    kinds = [protocol.CONFIRMATION] * 2
    cases: list[tuple[str, list[list[float]], list[str], dict[str, Any], str, str | None]] = [
        ("2% faster in 30 pairs over 2 confirmation sessions", win, kinds, {}, protocol.FASTER, None),
        ("29 pairs", [win[0], win[1][:14]], kinds, {}, protocol.INCONCLUSIVE, "pairs"),
        ("one session of 30 pairs", [win[0] + win[1]], kinds[:1], {}, protocol.INCONCLUSIVE, "pairs"),
        (
            "an exploratory session",
            win,
            [protocol.EXPLORATORY, protocol.CONFIRMATION],
            {},
            protocol.INCONCLUSIVE,
            "confirmation",
        ),
        (
            "0.4% faster, under the 1.005 threshold",
            [wobble(1.004, 15, 0.001), wobble(1.004, 15, 0.001)],
            kinds,
            {},
            protocol.INCONCLUSIVE,
            "interval",
        ),
        (
            "a session whose median is under 1",
            [[0.999] * 8 + [1.1] * 7, [1.1] * 15],
            kinds,
            {},
            protocol.INCONCLUSIVE,
            "sessions",
        ),
        ("another workload not measured", win, kinds, {"other": None}, protocol.INCONCLUSIVE, "others"),
        ("another workload slower", win, kinds, {"other": [0.97, 0.999]}, protocol.INCONCLUSIVE, "others"),
        ("another workload that reaches 1", win, kinds, {"other": [0.98, 1.0]}, protocol.FASTER, None),
        ("3% slower", [wobble(0.97, 15), wobble(0.971, 15)], kinds, {}, protocol.SLOWER, None),
        (
            "3% slower in one session and 3% faster in the other",
            [wobble(0.97, 15), wobble(1.03, 15)],
            kinds,
            {},
            protocol.INCONCLUSIVE,
            None,
        ),
    ]
    for what, ratios, ks, others, want, failed in cases:
        v = protocol.verdict(ratios, ks, 7, others)
        missed = [k for k, c in v["conditions"].items() if not c["held"]]
        ok = v["verdict"] == want and (failed is None or failed in missed)
        if want == protocol.FASTER:
            ok = ok and not missed
        expect(
            ok,
            f"the rule calls {what} {want}" + (f", for {failed}" if failed else ""),
            (v["verdict"], missed),
        )
    again = protocol.verdict(win, kinds, 7, {})
    expect(again == protocol.verdict(win, kinds, 7, {}), "the same seed gives the same verdict and intervals")


def pieces() -> None:
    where = {"build": "/b", "src": "/s", "inputs": "/i", "work": "/w", "out": "/o", "threads": "1"}
    filled = harness.fill(
        ["{build}/x", "{input:silesia.zip}/silesia.tar", "{input:1.webp}", "-t{threads}"], where
    )
    expect(
        filled == ["/b/x", "/i/silesia.tar", "/i/1.webp", "-t1"], "a workload's places are filled in", filled
    )
    try:
        harness.fill(["{model}"], where)
        expect(False, "a place the harness doesn't fill is refused")
    except harness.Refused:
        expect(True, "a place the harness doesn't fill is refused")
    expect(harness.repeated(["a"], 1) == ["a"], "a run that's long enough is run once")
    expect(
        harness.repeated(["a", "b"], 3)[-3:] == ["3", "a", "b"], "a short run is repeated inside one command"
    )
    expect(harness.level(["clang", "-O3", "-O2", "-c"]) == "-O2", "a compile's level is its last -O")
    expect(harness.relocation(["-fPIC", "-fno-pic"]) == "static", "-fno-pic last makes it static")
    expect(harness.relocation(["clang"]) == "pic", "and clang's default on Linux is PIE")
    c = harness.Compile(["clang", "-O3", "-MD", "-MF", "x.d", "-c", "-o", "x.o", "x.c"], ROOT, ROOT / "x.o")
    ir = harness.ir_argv(c, Path("x.ll"))
    expect(
        ir == ["clang", "-O3", "x.c", "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", "x.ll"],
        "a compile to IR drops -c, its object and its dependency files",
        ir,
    )
    # harness.toml's projects are the manifest's, approved, and each workload is one the harness can run.
    manifest = kernels.load()
    table = tomllib.loads(harness.HARNESS.read_text())
    for name, entry in table.items():
        project = manifest["project"].get(name)
        ok = project is not None and name in manifest["corpus"]["approved"]
        try:
            harness.workloads(entry.get("workload", {}), (project or {}).get("workload"))
        except harness.Refused as error:
            ok = False
            print(f"     {error}")
        expect(ok, f"harness.toml's {name} is an approved project, with workloads the harness can run")


# ------------------------------------------------------------------------------------------------------------
# The harness, end to end


def run(*args: str | Path) -> proc.Ran:
    return proc.run([sys.executable, HERE / "harness.py", *map(str, args)], timeout=900)


def ok_run(*args: str | Path) -> proc.Ran:
    r = run(*args)
    if not r.ok:
        raise RuntimeError(f"harness.py {' '.join(map(str, args))} failed\n{r.output[-3000:]}")
    return r


def can_run() -> str | None:
    if not sys.platform.startswith("linux"):
        return "pinning to cores needs Linux"
    missing = [t for t in ("clang", "llc", "opt", "objdump", "make") if pins.which(t) is None]
    return f"{', '.join(missing)} isn't on PATH" if missing else None


def end_to_end(work: Path) -> None:
    common = ["--spec", SPEC, "--work", work]
    ok_run("build", *common)
    print("ok   the synthetic project's baseline builds its own way, at -O3", flush=True)
    r = ok_run("candidate", *common, "same", "--unit", "kernel.c", "--unchanged", "--control", "a/a")
    record = schemas.read(work / "synthetic" / "O3" / "same" / "build.json", schemas.KERNELS_BUILD)
    obj = record["candidate"]["objects"][0]
    expect(obj["llc_reproduces"], "llc on kernel.c's unchanged IR gives the build's machine code")
    expect(
        record["candidate"]["differ_from_baseline_in"] == {"hot": []}, "the A/A control differs in nothing"
    )

    # Rewrites of `kernel`, as IR from the unit's own compile command.
    def rewrite(name: str, define: str) -> Path:
        out = work / f"{name}.ll"
        argv = [a for a in obj["compile"]["argv"] if a != "-c"]
        o = argv.index("-o")
        del argv[o : o + 2]
        r = proc.run(
            [*argv[:-1], define, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", out, argv[-1]],
            cwd=work / "synthetic" / "O3" / "baseline" / "src",
            env=harness.environment(),
            timeout=300,
        )
        if not r.ok:
            raise RuntimeError(f"kernel.c didn't compile with {define}\n{r.output[-2000:]}")
        return out

    extra = rewrite("extra", "-DEXTRA_LOOP")
    r = run("candidate", *common, "extra", "--unit", "kernel.c", "--ir", extra, "--functions", "kernel")
    expect(r.ok, "a rewrite of kernel with an extra loop passes the checks, as IR", r.output[-2000:])
    r = run("candidate", *common, "declared", "--unit", "kernel.c", "--ir", extra, "--functions", "main")
    expect(
        not r.ok and "the builds differ in ['kernel'], and the candidate declares ['main']" in r.err,
        "a rewrite that declares another function than it changes is refused",
        r.output[-2000:],
    )
    wrong = rewrite("wrong", "-DWRONG_RESULT")
    r = run("candidate", *common, "wrong", "--unit", "kernel.c", "--ir", wrong, "--functions", "kernel")
    expect(
        not r.ok and "output with the candidate isn't the baseline's" in r.err,
        "a rewrite whose output isn't the baseline's is refused before it's timed",
        r.output[-2000:],
    )
    r = run("candidate", *common, "unlabeled", "--unit", "kernel.c", "--recompile=-O0")
    expect(not r.ok and "is a control" in r.err, "a unit compiled at another level is only a control")

    # Timed, on one core of the first CCD, so it stays off the last, where real measurements run.
    cpu = str(harness.ccds()[0][0])
    plans = work / "plans"

    def measured(label: str, workload: str, pairs: int, *roles: str) -> list[Path]:
        plan = plans / f"{label}.json"
        ok_run(
            "plan",
            *common,
            *roles,
            "--workload",
            workload,
            "--pairs",
            str(pairs),
            "--cpus",
            cpu,
            "--min-seconds",
            str(FAST.min_seconds),
            "--out",
            plan,
        )
        ok_run("measure", *common, plan)
        return [plan.with_name(f"{label}.session-{n}.json") for n in (1, 2)]

    def compared(sessions: list[Path], *others: Path, rule: protocol.Rule = FAST) -> dict[str, Any]:
        out = sessions[0].with_name(sessions[0].name.replace(".session-1", ".comparison"))
        extra_args = [x for o in others for x in ("--other", o)]
        ok_run(
            "compare",
            "--spec",
            SPEC,
            "--min-seconds",
            str(rule.min_seconds),
            *sessions,
            *extra_args,
            "--out",
            out,
        )
        return schemas.read(out, schemas.KERNELS_COMPARISON)

    same = measured("same", "sum", 20, "--candidate", "same")
    c = compared(same)
    # Inconclusive because its interval isn't above the threshold, not only because `mix` wasn't measured.
    expect(
        c["verdict"] == protocol.INCONCLUSIVE
        and c["control"] == "a/a"
        and not c["conditions"]["interval"]["held"],
        "the baseline against itself is inconclusive, its interval short of 1.005",
        harness.describe(c),
    )
    print(harness.describe(c))
    slow = measured("slower", "sum", 15, "--candidate", "extra")
    c = compared(slow)
    expect(c["verdict"] == protocol.SLOWER, "the extra loop is slower", harness.describe(c))
    print(harness.describe(c))
    fast = measured("faster", "sum", 15, "--baseline", "extra", "--candidate", "baseline")
    other = measured("faster-mix", "mix", 15, "--baseline", "extra", "--candidate", "baseline")
    c = compared(fast, *other)
    expect(
        c["verdict"] == protocol.FASTER and c["control"] == "faster" and c["conditions"]["others"]["held"],
        "the baseline against the extra loop is faster, and the other workload isn't slower",
        harness.describe(c),
    )
    print(harness.describe(c))
    session = schemas.read(fast[0], schemas.KERNELS_SESSION)
    runs = [p[role] for p in session["pairs"] for role in ("baseline", "candidate")]
    expect(
        all(r["cpus"] == [int(cpu)] and len(r["load"]) == 3 for r in runs) and session["repeats"] >= 1,
        "every run records its cores and the load average, and short runs are repeated",
    )
    orders = {tuple(p["order"]) for p in session["pairs"]}
    expect(len(orders) == 2, "the pairs' order is drawn, so both orders occur", orders)
    expect(len(session["pairs"]) == 15, "no pair is removed")

    # By the protocol's own rule, none of this is by the protocol, and the board won't take it as a win.
    strict = compared(fast, *other, rule=protocol.PROTOCOL)
    expect(
        not strict["by_the_protocol"] and any("not 2.0" in p for p in strict["protocol_problems"]),
        "read by the protocol, runs repeated to 0.05 s aren't by it",
        strict["protocol_problems"],
    )
    comparison = fast[0].with_name("faster.comparison.json")
    entry = copy.deepcopy(schemas.read(HERE / "board" / "llama-q5.json", schemas.BOARD_WIN))
    entry.update(
        id="synthetic",
        project="zlib-ng",
        counts=True,
        labels={**entry["labels"], "found_by": "rule search"},
        found={"on": "2026-12-01", "after_lock": True},
        review={"statement": "a review", "mutant": "a mutant"},
        measured={
            "summary": "",
            "comparisons": [{"path": str(comparison), "sha256": hashing.sha256_file(comparison)}],
        },
    )
    found = board.problems(work / "synthetic.json", entry, kernels.load())
    for reason in ("not fixed", "a control", "isn't by the protocol", "isn't against the baseline"):
        expect(any(reason in p for p in found), f"the board refuses that as a win, as it's {reason}", found)


def main() -> int:
    numbers()
    pieces()
    why = can_run()
    if why is None:
        work = Path(tempfile.mkdtemp(prefix="kernels-bench-"))
        try:
            end_to_end(work)
        except RuntimeError as error:
            expect(False, "the harness runs end to end", error)
        finally:
            shutil.rmtree(work, ignore_errors=True)
    for f in failures:
        print(f"FAIL {f}")
    if failures:
        return 1
    if why is not None:
        print(f"skip the harness end to end: {why}")
        return SKIP
    return 0


if __name__ == "__main__":
    sys.exit(main())
