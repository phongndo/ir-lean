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
extra loop, given as IR. A rewrite that declares the wrong function, one whose output is wrong, one that
also changes what another function loads, or a table's contents, named or a switch's with no name, and a
check that builds the candidate again without the build's arguments, as xxHash's `make check` would, have to
be refused. Then it times them by the protocol, on one core of the first CCD, with runs repeated to 0.05 s
instead of 2 s, so it takes seconds: the control the same as the baseline has to come out inconclusive, the
extra loop slower, and the baseline against the extra loop faster, with the project's other workload measured
and not slower. Read by the protocol's own rule, none of these is by the protocol, and the board refuses a
win that cites one.

Then what a comparison or the board must not take, made from those sessions by hand: another workload's
evidence from other builds or an exploratory plan, a planned session left out, a seed, an order, a kind or a
ratio that isn't what the plan and the runs give, a run under the minimum, one that failed or ran on other
cores, and the sessions in another order; the compared workload's sessions given as another's; a session run
a second time, after it failed, or from a copy of its plan, and a second record of one; a comparison
relabeled, copied to another level, or leaving out a workload; and an entry whose proof or functions aren't
its candidate's, that's another's, or whose candidate is an object.

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
    try:
        filled = harness.fill(
            ["make", "-C", "{build}", "{build_args}", "check"], where, ["CFLAGS=-O3", "X=1"]
        )
    except harness.Refused as error:
        filled = [str(error)]
    expect(
        filled == ["make", "-C", "/b", "CFLAGS=-O3", "X=1", "check"],
        "a check takes the build's own arguments as {build_args}",
        filled,
    )
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
    def rewrite(name: str, *defines: str) -> Path:
        out = work / f"{name}.ll"
        argv = [a for a in obj["compile"]["argv"] if a != "-c"]
        o = argv.index("-o")
        del argv[o : o + 2]
        r = proc.run(
            [*argv[:-1], *defines, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", out, argv[-1]],
            cwd=work / "synthetic" / "O3" / "baseline" / "src",
            env=harness.environment(),
            timeout=300,
        )
        if not r.ok:
            raise RuntimeError(f"kernel.c didn't compile with {defines}\n{r.output[-2000:]}")
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

    # Beside the declared rewrite, `pick` loads another table and `scale` another constant, by the same
    # instructions: what each refers to is compared, by name, and a constant by what it holds.
    refs = rewrite("refs", "-DEXTRA_LOOP", "-DOTHER_REFS")
    r = run("candidate", *common, "refs", "--unit", "kernel.c", "--ir", refs, "--functions", "kernel")
    expect(
        not r.ok and "the builds differ in ['kernel', 'pick', 'scale']" in r.err,
        "a rewrite that also changes what another function loads, a global or a constant, is refused",
        r.output[-2000:],
    )
    table = rewrite("table", "-DEXTRA_LOOP", "-DOTHER_TABLE")
    r = run("candidate", *common, "table", "--unit", "kernel.c", "--ir", table, "--functions", "kernel")
    expect(
        not r.ok and "changes kernel.c's data ['third']" in r.err,
        "a rewrite that also changes a table another function reads is refused",
        r.output[-2000:],
    )
    # `table_pick`'s switch is a table of its results with no name or size, which only an offset in .rodata
    # points to: what it holds is compared, and with -DOTHER_SWITCH its first entry is 7, not 19.
    switch = rewrite("switch", "-DEXTRA_LOOP", "-DOTHER_SWITCH")
    r = run("candidate", *common, "switch", "--unit", "kernel.c", "--ir", switch, "--functions", "kernel")
    expect(
        not r.ok and "the builds differ in ['kernel', 'table_pick']" in r.err,
        "a rewrite that also changes another function's switch table, which has no name, is refused",
        r.output[-2000:],
    )
    # A check that drives make without the build's arguments builds hot again from the source, as xxHash's
    # flag-keyed Makefile would, so what would be timed isn't what was checked.
    unflagged = ["--spec", SPEC.with_name("unflagged.toml"), "--work", work]
    ok_run("build", *unflagged)
    r = run("candidate", *unflagged, "same", "--unit", "kernel.c", "--unchanged", "--control", "a/a")
    expect(
        not r.ok and "check, make -C '{build}' check, changed the candidate's" in r.err,
        "a check that builds the candidate again is refused",
        r.output[-2000:],
    )

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
    last = (session.get("calibration") or [{}])[-1]
    expect(
        last.get("repeats") == session["repeats"]
        and all(last[role]["wall_s"] >= FAST.min_seconds for role in ("baseline", "candidate")),
        "how many times a run is repeated is checked warm, before the pairs, at the minimum or over",
        last,
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

    by_hand(work, plans, fast, other, slow)
    again(work, common, plans)


def read_sessions(paths: list[Path]) -> list[dict[str, Any]]:
    out = []
    for path in paths:
        s = schemas.read(path, schemas.KERNELS_SESSION)
        s["_sha256"] = hashing.sha256_file(path)
        out.append(s)
    return out


def by_hand(work: Path, plans_dir: Path, fast: list[Path], other: list[Path], slow: list[Path]) -> None:
    """What a comparison, and the board, must not take, made from the timed sessions by hand."""
    plans = harness.read_plans(plans_dir)
    main = read_sessions(fast)
    mix = read_sessions(other)
    names = ["mix", "sum"]

    def compared(m: list[dict[str, Any]], o: list[dict[str, Any]], p: dict[str, Any] | None = None) -> Any:
        return harness.compare(copy.deepcopy(m), {"mix": copy.deepcopy(o)}, names, FAST, p or plans)

    good = compared(main, mix)
    expect(
        good["verdict"] == protocol.FASTER,
        "the faster control, read again, is faster",
        good["protocol_problems"],
    )
    flipped = compared(list(reversed(main)), mix)
    expect(flipped == good, "the sessions in another order give the same comparison, bootstrap included")

    # Condition 4 takes another workload's sessions only of the same builds, level and kind.
    for what, change in (
        ("an exploratory plan", {"kind": protocol.EXPLORATORY}),
        ("other builds", {"candidate": {"variant": "same", "record_sha256": "0" * 64}}),
        ("another level", {"opt": harness.OWN_OPT}),
    ):
        plan = copy.deepcopy(plans[mix[0]["plan_sha256"]])
        plan.update(change)
        forged = copy.deepcopy(mix)
        for s in forged:
            s["plan_sha256"] = "f" * 64
            s["kind"] = plan["kind"]
        got = compared(main, forged, {**plans, "f" * 64: plan})
        expect(
            got["verdict"] != protocol.FASTER
            and not got["conditions"]["others"]["held"]
            and any("isn't the comparison's" in p for p in got["protocol_problems"]),
            f"another workload's sessions from {what} don't stand for it",
            (got["verdict"], got["protocol_problems"]),
        )

    def problem(what: str, want: str, change: Any, sessions: list[dict[str, Any]] = main) -> None:
        forged = copy.deepcopy(sessions)
        change(forged)
        got = compared(forged, mix)
        expect(
            not got["by_the_protocol"] and any(want in p for p in got["protocol_problems"]),
            f"a comparison with {what} isn't by the protocol",
            got["protocol_problems"],
        )

    def ratio(s: list[dict[str, Any]]) -> None:
        s[0]["pairs"][0]["ratio"] = 5.0

    def short(s: list[dict[str, Any]]) -> None:
        p = s[0]["pairs"][0]
        p["baseline"]["wall_s"] = p["candidate"]["wall_s"] = 0.01
        p["ratio"] = 1.0

    problem("a planned session left out", "its sessions are [1], and its plan has [1, 2]", lambda s: s.pop())
    problem(
        "a seed that isn't its plan's", "its seed isn't the one its plan drew", lambda s: s[1].update(seed=7)
    )
    problem(
        "a pair's order that isn't its seed's",
        "order isn't the one its seed draws",
        lambda s: s[0]["pairs"][0].update(order=list(reversed(s[0]["pairs"][0]["order"]))),
    )
    problem("a ratio that isn't its runs'", "a pair's ratio isn't what its runs give", ratio)
    problem(
        "an exploratory session in a confirmation plan",
        "its kind isn't its plan's",
        lambda s: s[0].update(kind="exploratory"),
    )
    problem("a pair given twice", "aren't numbered 1 to", lambda s: s[0]["pairs"].append(s[0]["pairs"][-1]))
    problem("a run under the minimum", "2 of its runs took under 0.05 s", short)

    # A timed run that crashed or hit a limit, or ran on other cores than its plan's, isn't by the protocol,
    # and its pair stays.
    def failed(s: list[dict[str, Any]]) -> None:
        s[0]["pairs"][0]["candidate"].update(exit=1, limit="time_limit")

    problem("a run that failed", "1 of its runs didn't exit 0 within its limits", failed)
    problem(
        "a run on other cores",
        "1 of its runs weren't on its plan's cores",
        lambda s: s[0]["pairs"][0]["baseline"].update(cpus=[s[0]["cpus"][0] + 1]),
    )
    forged = copy.deepcopy(main)
    failed(forged)
    expect(compared(forged, mix)["pooled"] == good["pooled"], "and no pair is dropped for a failed run")

    # The compared workload's own sessions, given again as mix's: what a workload's sessions are of is theirs
    # and their plan's to say, not the name they're given under.
    try:
        relabeled = harness.compare(copy.deepcopy(main), {"mix": copy.deepcopy(main)}, names, FAST, plans)
        why = f"{relabeled['verdict']}, by the protocol: {relabeled['by_the_protocol']}"
    except harness.Refused as error:
        relabeled, why = None, str(error)
    expect(
        relabeled is None and "the sessions given as mix's are sum's" in why,
        "a comparison refuses the compared workload's sessions given as another workload's",
        why,
    )
    forged = copy.deepcopy(main)
    ratio(forged)
    got = compared(forged, mix)
    expect(
        got["pooled"] == good["pooled"], "the statistic is worked out from the runs, not the stored ratios"
    )

    # The board works out all of a comparison again, from its sessions, plan and builds.
    comparison = fast[0].with_name("faster.comparison.json")
    stored = schemas.read(comparison, schemas.KERNELS_COMPARISON)
    expect(
        not board.recompute(comparison),
        "the board works out the faster control again",
        board.recompute(comparison),
    )
    forgeries: list[tuple[str, str, dict[str, Any], str]] = [
        (
            "relabeled",
            "a control relabeled as a comparison against the baseline",
            {**stored, "control": None, "baseline": {**stored["baseline"], "variant": "baseline"}},
            "its control isn't",
        ),
        (
            "level",
            "a copy relabeled at the project's own level",
            {**stored, "opt": harness.OWN_OPT},
            "its opt isn't",
        ),
        (
            "omitted",
            "a workload left out",
            harness.compare(read_sessions(fast), {}, ["sum"], FAST, plans),
            "its unmeasured isn't",
        ),
        (
            "relabeled-mix",
            "the compared workload's sessions cited as mix's",
            {
                **stored,
                "others": {
                    "mix": {
                        **stored["others"]["mix"],
                        "plan_sha256": stored["plan_sha256"],
                        "sessions": [s["sha256"] for s in stored["sessions"]],
                    }
                },
            },
            "the sessions given as mix's are sum's",
        ),
    ]
    for name, what, record, want in forgeries:
        path = comparison.with_name(f"forged-{name}.comparison.json")
        schemas.write(path, record, schemas.KERNELS_COMPARISON, indent=2)
        found = board.recompute(path)
        expect(any(want in p for p in found), f"the board refuses {what}", found)

    # An entry is bound to the candidate its comparisons measured, and its proof to that candidate's IR.
    slower = slow[0].with_name("slower.comparison.json")
    cand = schemas.read(work / "synthetic" / "O3" / "extra" / "build.json", schemas.KERNELS_BUILD)
    entry = copy.deepcopy(schemas.read(HERE / "board" / "llama-q5.json", schemas.BOARD_WIN))
    entry.update(
        id="bound",
        project="zlib-ng",
        unit="kernel.c",
        functions=["kernel"],
        counts=True,
        measured={
            "summary": "",
            "comparisons": [{"path": str(slower), "sha256": hashing.sha256_file(slower)}],
        },
    )
    entry["proof"]["ir"] = [
        {
            "source": str(work / "synthetic" / "O3" / "extra" / "unit" / "1.ll"),
            "target": str(work / "extra.ll"),
        }
    ]
    manifest = kernels.load()
    binding = (
        "its candidate declares",
        "its candidate rewrites",
        "its proof isn't about its candidate",
        "isn't a rewrite",
        "isn't the baseline build",
    )
    found = board.problems(work / "bound.json", entry, manifest)
    expect(
        cand["candidate"]["declared"] == ["kernel"]
        and not [p for p in found if any(b in p for b in binding)],
        "an entry bound to its candidate and its proof's IR passes those checks",
        found,
    )
    expect(
        any("isn't built from zlib-ng at the corpus's pin" in p for p in found),
        "and a build that isn't the corpus's pin is refused",
        found,
    )
    # The same candidate given as the object llc made of its IR: nothing proves an object is its proof's
    # target compiled, so only a rewrite given as IR counts, and the board says so.
    as_object = copy.deepcopy(cand)
    made = work / "synthetic" / "O3" / "extra" / "unit" / "1.candidate.o"
    as_object["candidate"].update(form="object", input_sha256=hashing.sha256_file(made))
    plan = board.plan_of(slower)
    assert plan is not None
    got = board.built("x", entry, manifest["project"]["zlib-ng"], manifest["corpus"], plan)
    plan["_builds"]["candidate"] = as_object
    found = board.built("x", entry, manifest["project"]["zlib-ng"], manifest["corpus"], plan)
    expect(
        not any("is an object" in p for p in got)
        and any("its candidate is an object, and only a rewrite given as IR" in p for p in found),
        "the board doesn't count a candidate given as an object, and says why",
        found,
    )
    for what, change, want in (
        (
            "other functions",
            {"functions": ["main"]},
            "its candidate declares ['kernel'], and the entry's functions are ['main']",
        ),
        ("another unit", {"unit": "hot.c"}, "its candidate rewrites 'kernel.c'"),
        (
            "a proof of other IR",
            {
                "proof": {
                    **entry["proof"],
                    "ir": [{**entry["proof"]["ir"][0], "target": str(work / "refs.ll")}],
                }
            },
            "its proof isn't about its candidate",
        ),
        ("no proof module", {"proof": {**entry["proof"], "modules": []}}, "its proof names no module"),
        (
            "a test that doesn't check its module",
            {"proof": {**entry["proof"], "test": "irlean"}},
            "doesn't name its module",
        ),
    ):
        found = board.problems(work / "bound.json", {**entry, **change}, manifest)
        expect(any(want in p for p in found), f"the board refuses an entry with {what}", found)
    twice = [(work / "a.json", entry), (work / "b.json", {**entry, "id": "b"})]
    expect(
        bool(board.duplicates(twice)), "the board refuses two entries of one rewrite", board.duplicates(twice)
    )
    copied = comparison.with_name("forged-level.comparison.json")
    entry2 = {
        **entry,
        "measured": {
            "summary": "",
            "comparisons": [
                {"path": str(comparison), "sha256": hashing.sha256_file(comparison)},
                {"path": str(copied), "sha256": hashing.sha256_file(copied)},
            ],
        },
    }
    found = board.problems(work / "copies.json", entry2, manifest)
    expect(
        any("is the measurement another of its comparisons is" in p for p in found),
        "the board refuses one measurement cited at two levels",
        found,
    )


def again(work: Path, common: list[Any], plans: Path) -> None:
    """A session is run once: again, or after it failed, is another plan."""
    first = plans / "same.session-1.json"
    before = hashing.sha256_file(first)
    r = run("measure", *common, plans / "same.json", "--session", "1")
    expect(
        not r.ok and "attempted already" in r.err and hashing.sha256_file(first) == before,
        "a session run a second time is refused, and the first is kept",
        r.output[-2000:],
    )
    plan = plans / "broken.json"
    cpu = str(harness.ccds()[0][0])
    ok_run(
        "plan",
        *common,
        "--candidate",
        "same",
        "--workload",
        "sum",
        "--pairs",
        "2",
        "--cpus",
        cpu,
        "--min-seconds",
        str(FAST.min_seconds),
        "--out",
        plan,
    )
    hot = work / "synthetic" / "O3" / "same" / "src" / "hot"
    hot.write_bytes(hot.read_bytes() + b"\0")
    r = run("measure", *common, plan)
    kept = plan.with_name("broken.session-1.json")
    record = schemas.read(kept, schemas.KERNELS_ATTEMPT) if kept.is_file() else {}
    expect(
        not r.ok and record.get("status") == "failed" and "binaries aren't" in record.get("error", ""),
        "a session that fails is kept on record as a failed attempt",
        (r.output[-1000:], record),
    )
    r = run("measure", *common, plan, "--session", "1")
    expect(not r.ok and "attempted already" in r.err, "and isn't run again", r.output[-1000:])
    r = run("compare", "--spec", SPEC, kept, plan.with_name("broken.session-2.json"))
    expect(
        not r.ok and "attempt, failed, not a session" in r.err,
        "and isn't compared as a session",
        r.output[-1000:],
    )

    # A copy of a plan under another name has its hash, so its sessions are the plan's, which ran already.
    copied = plans / "same-copy.json"
    shutil.copy(plans / "same.json", copied)
    r = run("measure", *common, copied, "--session", "1")
    expect(
        not r.ok
        and "attempted already" in r.err
        and not copied.with_name("same-copy.session-1.json").exists(),
        "a copy of a plan under another name can't run its sessions again",
        r.output[-2000:],
    )
    # A second record of one session, as running the copy from another work directory would leave, with
    # other times: compare and the board refuse both.
    second = schemas.read(first, schemas.KERNELS_SESSION)
    for p in second["pairs"]:
        p["candidate"]["wall_s"] *= 0.9
        p["ratio"] = protocol.ratio(p["baseline"]["wall_s"], p["candidate"]["wall_s"], protocol.TIME)
    schemas.write(copied.with_name("same-copy.session-1.json"), second, schemas.KERNELS_SESSION, indent=2)
    r = run(
        "compare",
        "--spec",
        SPEC,
        "--min-seconds",
        str(FAST.min_seconds),
        first,
        plans / "same.session-2.json",
    )
    found = board.recompute(plans / "same.comparison.json")
    expect(
        not r.ok
        and "session 1 of its plan has 2 records" in r.err
        and any("session 1 of its plan has 2 records" in p for p in found),
        "compare and the board refuse two records of one session of a plan",
        (r.output[-1000:], found),
    )


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
