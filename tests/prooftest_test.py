#!/usr/bin/env python3
"""Checks tools/prooftest/prooftest.py, tier-1 proof tests: each status and reason comes back when it should,
a counterexample counts only once it's confirmed, and nothing that wasn't decided comes back as a pass.

The first group needs only Python: the generators, shrinking, the store, the decision and the contract, and
that docs/proof-tests.md names every status and reason. The second runs the tool on the functions in
tests/prooftest/Cases.ll, as a developer would: a wrong spec, a spec stated with `∃`, a buggy loop with and
without a promise to progress, poison inputs, a call the kernel can't follow, a run that never ends with and
without a promise, memory, floating point, a vacuous hypothesis, too few inputs meeting one, a statement about
another function, a memory limit and a stored failure tried first.

usage: tests/prooftest_test.py path/to/ir-lean [--only NAME ...] [--static]
"""

import argparse
import importlib.util
import json
import os
import random
import sys
import tempfile
import textwrap
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc, schemas  # noqa: E402

TOOL = ROOT / "tools" / "prooftest" / "prooftest.py"
CASES = ROOT / "tests" / "prooftest" / "Cases.ll"
DOC = ROOT / "docs" / "proof-tests.md"


def load() -> Any:
    spec = importlib.util.spec_from_file_location("prooftest_tool", TOOL)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


# Python only


def static_checks(pt: Any) -> list[str]:
    failures: list[str] = []

    def check(condition: bool, what: str) -> None:
        if not condition:
            failures.append(what)

    bv32 = {"name": "x", "kind": "bitvec", "width": 32}
    val8 = {"name": "x", "kind": "val", "width": 8}
    edges = pt.edges(bv32)
    check(edges[:3] == [0, 1, 0xFFFFFFFF], f"edges start with 0, 1 and all ones: {edges[:3]}")
    check({0x80000000, 0x7FFFFFFF} <= set(edges), "edges have the signed limits")
    check(None in pt.edges(val8), "a Val binder's edges have poison")
    patterns = pt.patterns(bv32)
    check(all(1 << i in patterns for i in range(32)), "patterns have every single bit")
    check(0x55555555 in patterns and 0xAAAAAAAA in patterns, "patterns have alternating bits")
    rng = random.Random(1)
    values = [pt.random_value(bv32, rng) for _ in range(2000)]
    check(all(0 <= v < 1 << 32 for v in values), "random values fit the width")
    check(any(v >> 31 for v in values), "random values set the top bit")

    a = pt.plan([bv32, bv32], seed=7, max_inputs=2000)
    b = pt.plan([bv32, bv32], seed=7, max_inputs=2000)
    check(a.inputs == b.inputs, "the plan is the same for the same seed")
    check(len(a.inputs) == 2000 and len(set(a.inputs)) == 2000, "the plan has max_inputs distinct inputs")
    check(a.phases[0] == "edges" and a.phases[-1] == "random", "edges first, random last")
    phases = list(dict.fromkeys(a.phases))
    check(phases == ["edges", "patterns", "bytes", "random"], f"the phases in order: {phases}")
    check(all((v, 0) in set(a.inputs) or any(t[0] == v for t in a.inputs) for v in range(256)), "every byte")
    stored = [(5, 6), (7, 8)]
    c = pt.plan([bv32, bv32], seed=7, max_inputs=2000, replay=stored)
    check(c.inputs[:2] == stored and c.phases[:2] == ["replay", "replay"], "stored inputs come first")
    check(len(c.inputs) == 2002, "stored inputs don't use up the budget")
    small = pt.plan([val8], seed=0, max_inputs=1000)
    check(
        small.exhaustive and len(small.inputs) == 257, "a Val 8 binder is tried exhaustively, poison included"
    )
    check(None in small.inputs[0] or (None,) in small.inputs, "the exhaustive plan includes poison")

    def fails_if_bit5(candidates: list[tuple]) -> int | None:
        return next((i for i, (v,) in enumerate(candidates) if v is not None and v >> 5 & 1), None)

    shrunk, steps = pt.shrink((0xFFFFFFFF,), [bv32], fails_if_bit5)
    check(shrunk == (32,) and steps > 0, f"shrinking 0xFFFFFFFF where bit 5 fails gives 32, not {shrunk}")
    again, _ = pt.shrink((0xFFFFFFFF,), [bv32], fails_if_bit5)
    check(again == shrunk, "shrinking is deterministic")
    check(pt.shrink((None,), [val8], lambda c: 0)[0] == (None,), "poison isn't shrunk")

    with tempfile.TemporaryDirectory() as temporary:
        store = pt.Store(Path(temporary))
        binders = [bv32, {"name": "y", "kind": "val", "width": 8}]
        key = pt.property_key("∀ x y, P x y", binders)
        check(key == pt.property_key("∀ x y, P x y", binders), "a property's key doesn't depend on the code")
        store.add(key, {"values": [3, None]}, {"function": "f", "statement": "s"})
        store.add(key, {"values": [3, None]}, {"function": "f", "statement": "s"})
        store.add(key, {"values": [9, 1]}, {"function": "f", "statement": "s"})
        check(
            store.load(key, binders) == [(9, 1), (3, None)], "the store keeps each input once, newest first"
        )
        check(
            store.load(key, [bv32, bv32]) == [(9, 1)],
            "a stored input that doesn't fit the binders is skipped",
        )
        store.path(key).write_text("{not json")
        check(store.load(key, binders) == [], "a broken store file reads as empty")
        check(pt.Store(None).add(key, {"values": [1, 2]}, {}) is False, "no store directory, nothing stored")

    # The decision: nothing undecided, stopped or unconfirmed is ever a pass.
    def decided(**fields: Any) -> tuple[str, str]:
        run = pt.Run({"min_satisfied": 10}, Path(), Path(), 0.0, 0.0)
        run.plan = pt.Plan(inputs=[(0,)] * 100, phases=["random"] * 100, exhaustive=False, domain=1 << 32)
        run.tried, run.satisfied, run.planned_all = 100, 100, True
        for k, v in fields.items():
            setattr(run, k, v)
        status, reason, _ = pt.decide(run)
        return status, reason

    check(decided() == ("passed_tier1", "sampled"), "a full run with no failure passes tier 1")
    check(decided(satisfied=0) == ("vacuous", "no_input_meets_hypotheses"), "no input meeting the hypotheses")
    check(decided(satisfied=3) == ("unknown", "too_few_satisfying"), "too few meeting the hypotheses")
    undecided = [{"index": 4, "phase": "random", "result": "input_timeout", "values": [0]}]
    check(
        decided(undecided=undecided, planned_all=False) == ("unknown", "input_timeout"), "an input that hung"
    )
    check(
        decided(limit_hit="memory_limit", planned_all=False) == ("unknown", "memory_limit"), "a memory limit"
    )
    check(decided(planned_all=False) == ("unknown", "time_limit"), "a run that didn't finish its plan")
    unconfirmed = {"evidence": [], "kernel": {"ok": False, "detail": "stuck"}, "shown": {}}
    check(decided(counterexample=unconfirmed) == ("unknown", "unconfirmed"), "a failure nothing confirmed")
    check(
        decided(counterexample=unconfirmed, disagreement="verify says it holds")
        == ("unknown", "confirmation_disagrees"),
        "a failure the confirmation contradicts",
    )
    confirmed = {"evidence": ["kernel"], "kernel": {"ok": True}, "shown": {"x": "1#8"}}
    clean = {"kernel": pt.core.Step("harness", 0)}
    check(
        decided(counterexample=confirmed, confirmed_by=clean) == ("counterexample", "kernel_refuted"),
        "a confirmed failure",
    )
    # The answer counts only from a harness that then ended cleanly, and so does tools/verify.py's.
    for ended in (None, pt.core.Step("harness", -11), pt.core.Step("harness", -9, limit="stopped")):
        by = {} if ended is None else {"kernel": ended}
        check(
            decided(counterexample=confirmed, confirmed_by=by)[0] != "counterexample",
            f"a kernel answer from a harness that ended {ended} refutes nothing",
        )
    # Where tools/verify.py records how its witness process ended: under reproduce.commands, as each
    # command it ran, which is what the confirmation reads.
    v = pt.verify
    shape = v.Run({"input": {"ir": "x.ll"}, "statement": "True", "witnesses": []}, Path(), Path(), 0.0, 0.0)
    shape.commands = [{"step": "claim:witness", "exit": 0, "timed_out": False}]
    shape.request["limits"] = {"timeout_seconds": 1, "memory_mb": 1}
    recorded = v.build_result(shape)
    check(
        pt.witness_step(recorded) == pt.core.Step("claim:witness", 0),
        "the witness process is found where tools/verify.py records it",
    )
    timed = {"reproduce": {"commands": [{"step": "claim:witness", "exit": -9, "timed_out": True}]}}
    check(
        pt.witness_step(timed) == pt.core.Step("claim:witness", -9, "time_limit"), "a timed-out witness run"
    )
    check(pt.witness_step({"reproduce": None}) is None, "no record, no process")
    evaluated = {**confirmed, "evidence": ["compiled_evaluation"]}
    for ended, want in ((pt.core.Step("claim:witness", 0), "counterexample"), (None, "unknown")):
        by = {} if ended is None else {"compiled_evaluation": ended}
        check(
            decided(counterexample=evaluated, confirmed_by=by)[0] == want,
            f"compiled evaluation, its process {ended}, is {want}",
        )

    # The contract turns a result that breaks it into unknown/internal_error.
    run = pt.Run({"min_satisfied": 10}, Path(), Path(), 0.0, 0.0)
    run.plan = pt.Plan(inputs=[(0,), (1,)], phases=["edges", "edges"], exhaustive=True, domain=2)
    run.tried, run.satisfied, run.planned_all = 2, 2, True
    good = pt.build_result(run, 0.0)
    check(good["status"] == "passed_tier1" and good["proved"] is False, "a pass says it isn't a proof")
    for broken, why in (
        ({"proved": True}, "a pass that says it's proved"),
        ({"exit_code": 2}, "the wrong exit code"),
        (
            {"counterexample": {"evidence": ["kernel"], "kernel": {"ok": True}}},
            "a pass with a counterexample",
        ),
        ({"inputs": {**good["inputs"], "undecided": [{"index": 0}]}}, "a pass with an undecided input"),
    ):
        try:
            pt.assert_contract({**good, **broken})
            failures.append(f"the contract allows {why}")
        except AssertionError:
            pass
    bad = {**good, "status": "counterexample", "reason": "kernel_refuted", "exit_code": 2}
    bad["counterexample"] = {"evidence": [], "kernel": {}}
    try:
        pt.assert_contract(bad)
        failures.append("the contract allows a counterexample with no evidence")
    except AssertionError:
        pass

    text = DOC.read_text() if DOC.exists() else ""
    for word in [*pt.STATUSES, *pt.REASONS, *pt.EVIDENCE]:
        check(f"`{word}`" in text, f"docs/proof-tests.md doesn't mention `{word}`")
    invalid = pt.prooftest({"statement": "True"}, ROOT)
    check(
        invalid["status"] == "unknown"
        and invalid["reason"] == "invalid_request"
        and invalid["exit_code"] == 1,
        "a malformed request is unknown/invalid_request",
    )
    return failures


# The tool on real functions


@dataclass
class Case:
    name: str
    function: str
    statement: str
    status: str
    reason: str
    extra: dict[str, Any] = field(default_factory=dict)
    check: Callable[[dict[str, Any]], str | None] | None = None
    # Runs the tool again with the same store, and checks the second result.
    again: Callable[[dict[str, Any]], str | None] | None = None


def shown(result: dict[str, Any]) -> dict[str, str]:
    return (result.get("counterexample") or {}).get("shown") or {}


def expect(condition: bool, why: str) -> str | None:
    return None if condition else why


def cases() -> list[Case]:
    return [
        Case(
            "wrong_spec_shrinks",
            "low16",
            "∀ (x : BitVec 32), Cases.low16 (some x) = IRLean.Outcome.ok (some x)",
            "counterexample",
            "kernel_refuted",
            check=lambda r: expect(
                shown(r) == {"x": "0x10000#32"} and r["counterexample"]["shrink_steps"] > 0,
                f"shrinks to the least failing input, 0x10000, not {shown(r)}",
            ),
            again=lambda r: expect(
                r["counterexample"]["found"]
                == {"phase": "replay", "index": 0, "assignment": {"x": "65536#32"}},
                f"the stored input is tried first: {r['counterexample']['found']}",
            ),
        ),
        Case(
            "verify_confirms_too",
            "times2",
            "∀ (x : BitVec 8), Cases.times2 (some x) = IRLean.Outcome.ok (some (x * 2#8))",
            "counterexample",
            "kernel_refuted",
            extra={"verify_confirm": "always", "store": None},
            check=lambda r: expect(
                r["counterexample"]["evidence"] == ["kernel", "compiled_evaluation"]
                and r["counterexample"]["verify"]["status"] == "counterexample"
                and set(r["counterexample"]["kernel"]["axioms"])
                <= {"propext", "Classical.choice", "Quot.sound"},
                "the kernel and tools/verify.py both confirm, on the standard axioms only",
            ),
        ),
        Case(
            "relational_spec",
            "low16",
            "∀ (x : BitVec 32), ∃ r : BitVec 32, Cases.low16 (some x) = IRLean.Outcome.ok (some r) ∧ r = x",
            "counterexample",
            "kernel_refuted",
            extra={"store": None},
            check=lambda r: expect(
                shown(r) == {"x": "0x10000#32"},
                f"`∃ r` is decided by running the call once, not by trying every r: {shown(r)}",
            ),
        ),
        Case(
            "loop_through_run_fuel",
            "count",
            "∀ (x : BitVec 32), Cases.count (some x) = IRLean.Outcome.ok (some (x.cpop.setWidth 32))",
            "counterexample",
            "kernel_refuted",
            extra={"store": None},
            check=lambda r: expect(
                shown(r) == {"x": "0x2#32"} and r["counterexample"]["kernel"]["calls_rewritten"] == 1,
                f"the kernel follows the loop through runFuel, at x = 2: {shown(r)}",
            ),
        ),
        Case(
            "loop_under_a_promise",
            "count_promised",
            "∀ (x : BitVec 32), Cases.count_promised (some x) = "
            "IRLean.Outcome.ok (some (x.cpop.setWidth 32))",
            "counterexample",
            "kernel_refuted",
            extra={"store": None},
            check=lambda r: expect(
                shown(r) == {"x": "0x2#32"} and r["counterexample"]["kernel"]["calls_rewritten"] == 1,
                f"the kernel follows `promised (run ...)` through runFuel too, at x = 2: {shown(r)}",
            ),
        ),
        Case(
            "poison_input",
            "ident",
            "∀ (x : IRLean.Val 8), Cases.ident x = IRLean.Outcome.ok x",
            "counterexample",
            "kernel_refuted",
            extra={"store": None},
            check=lambda r: expect(shown(r) == {"x": "poison"}, f"refuted at poison, by noundef: {shown(r)}"),
        ),
        Case(
            "kernel_cant_follow_a_call",
            "outer",
            "∀ (x : BitVec 8), Cases.outer (some x) = IRLean.Outcome.ok (some x)",
            "counterexample",
            "compiled_evaluation",
            extra={"store": None},
            check=lambda r: expect(
                r["counterexample"]["evidence"] == ["compiled_evaluation"]
                and not r["counterexample"]["kernel"]["ok"]
                and r["counterexample"]["verify"]["result"] == "fails",
                "where the kernel can't follow the call, tools/verify.py confirms instead, and says so",
            ),
        ),
        Case(
            "correct_spec_passes",
            "times2",
            "∀ (x : BitVec 8), Cases.times2 (some x) = IRLean.Outcome.ok (some (x * 4#8))",
            "passed_tier1",
            "exhaustive",
            extra={"store": None},
            check=lambda r: expect(
                r["proved"] is False and r["inputs"]["tried"] == 256 and r["exit_code"] == 0,
                "every input of 8 bits ran, and it still isn't a proof",
            ),
        ),
        Case(
            "sampled_pass",
            "low16",
            "∀ (x : BitVec 32), Cases.low16 (some x) = IRLean.Outcome.ok (some (x &&& 0xFFFF#32))",
            "passed_tier1",
            "sampled",
            extra={"store": None, "max_inputs": 300},
            check=lambda r: expect(r["inputs"]["tried"] == 300, "300 inputs ran"),
        ),
        Case(
            "vacuous",
            "times2",
            "∀ (x : BitVec 8), x < 0#8 → Cases.times2 (some x) = IRLean.Outcome.ok (some x)",
            "vacuous",
            "no_input_meets_hypotheses",
            extra={"store": None},
        ),
        Case(
            "too_few_satisfying",
            "low16",
            "∀ (x : BitVec 32), x < 3#32 → Cases.low16 (some x) = IRLean.Outcome.ok (some x)",
            "unknown",
            "too_few_satisfying",
            extra={"store": None, "max_inputs": 40},
        ),
        Case(
            "never_ends",
            "spin",
            "∀ (x : BitVec 8), Cases.spin (some x) = IRLean.Outcome.ok (some x)",
            "unknown",
            "input_timeout",
            extra={"store": None, "limits": {"input_timeout_seconds": 0.5}},
            check=lambda r: expect(
                len(r["inputs"]["undecided"]) == 3 and r["counterexample"] is None,
                "three inputs that never finish, then it stops, and none is a counterexample",
            ),
        ),
        Case(
            "never_ends_under_a_promise",
            "spin_promised",
            "∀ (x : BitVec 8), Cases.spin_promised (some x) = IRLean.Outcome.ok (some x)",
            "unknown",
            "input_timeout",
            extra={"store": None, "limits": {"input_timeout_seconds": 0.5}},
            check=lambda r: expect(
                r["counterexample"] is None and r["status"] != "passed_tier1",
                "breaking a promise to progress is undefined, which running can't show, so it's unknown",
            ),
        ),
        Case(
            "memory",
            "load",
            "∀ (p : IRLean.PtrVal) (m : IRLean.Mem), Cases.load p m ≠ Option.none",
            "unknown",
            "binder_unsupported",
            extra={"store": None},
        ),
        Case(
            "float_unsupported",
            "fadd",
            "∀ (x : BitVec 32), True",
            "unknown",
            "function_unsupported",
            extra={"store": None},
        ),
        Case(
            "about_another_function",
            "times2",
            "∀ (x : BitVec 8), Cases.ident (some x) = IRLean.Outcome.ok (some x)",
            "unknown",
            "statement_not_about_target",
            extra={"store": None},
        ),
        Case(
            "memory_limit",
            "times2",
            "∀ (x : BitVec 8), Cases.times2 (some x) = IRLean.Outcome.ok (some (x * 4#8))",
            "unknown",
            "memory_limit",
            extra={"store": None, "limits": {"memory_mb": 300}},
        ),
    ]


def run_tool(arguments: list[str]) -> dict[str, Any]:
    ran = proc.run([sys.executable, str(TOOL), *arguments])
    try:
        result = json.loads(ran.out)
    except json.JSONDecodeError:
        return {"_exit": ran.exit, "_output": ran.out[-2000:] + ran.err[-2000:]}
    result["_exit"] = ran.exit
    return result


def run_case(case: Case, tool: Path, scratch: Path) -> str | None:
    directory = scratch / case.name
    directory.mkdir()
    request = {
        "input": {"ir": str(CASES)},
        "function": case.function,
        "namespace": "Cases",
        "statement": case.statement,
        "store": str(directory / "store"),
        **case.extra,
    }
    (directory / "request.json").write_text(json.dumps(request, ensure_ascii=False))

    def one(work: str) -> tuple[dict[str, Any], str | None]:
        result = run_tool(
            ["run", str(directory / "request.json"), "--tool", str(tool), "--work-dir", str(directory / work)]
        )
        if "status" not in result:
            return result, f"no JSON: {result['_output']}"
        got = f"{result['status']}/{result['reason']}"
        if got != f"{case.status}/{case.reason}":
            return result, f"{got}, not {case.status}/{case.reason}: {result.get('detail')}"
        if result["_exit"] != result["exit_code"]:
            return result, f"exit {result['_exit']}, where the result says {result['exit_code']}"
        return result, None

    result, failure = one("first")
    if failure is None and case.check:
        failure = case.check(result)
    if failure is None and case.again:
        result, failure = one("second")
        if failure is None:
            failure = case.again(result)
    return failure


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path, nargs="?", default=ROOT / "build" / "ir-lean")
    parser.add_argument("--only", nargs="*", default=None)
    parser.add_argument("--static", action="store_true", help="only the checks that need no Lean")
    args = parser.parse_args()
    pt = load()
    failed = False
    for failure in static_checks(pt):
        print(f"FAIL  static: {failure}")
        failed = True
    if not failed:
        print("ok    static: generators, shrinking, the store, the decision, the contract and the doc")
    capabilities = run_tool(["capabilities"])
    if capabilities.get("schema") != schemas.PROOFTEST or capabilities["_exit"] != 0:
        print("FAIL  capabilities")
        failed = True
    if args.static:
        return 1 if failed else 0
    selected = [c for c in cases() if not args.only or c.name in args.only]
    # Each case runs at most two Lean processes at a time: tools/verify.py's, then the harness.
    jobs = max(1, min(int(os.environ.get("LEAN_JOBS", "4")), 4))
    with tempfile.TemporaryDirectory() as temporary, ThreadPoolExecutor(jobs) as pool:
        scratch = Path(temporary)
        results = list(pool.map(lambda c: (c, run_case(c, args.tool.resolve(), scratch)), selected))
    for case, failure in results:
        if failure:
            print(f"FAIL  {case.name}: {textwrap.shorten(failure, 3000)}")
            failed = True
        else:
            print(f"ok    {case.name}: {case.status}/{case.reason}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
