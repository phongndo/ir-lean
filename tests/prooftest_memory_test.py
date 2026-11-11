#!/usr/bin/env python3
"""Checks tier-1 proof tests on functions that take memory, and the equivalence property, in
tools/prooftest/prooftest.py.

The first group needs only Python: a buffer's edges, patterns and random values, that every input fits its
binders, the encoding the harness reads, shrinking a buffer shorter and then its bytes simpler, the store,
what each argument of an equivalence is, and the statement it's built into.

The second checks that IRLean/Ptf.lean, where `toMem_placeExec` is, rests on the standard axioms with nothing
compiled the kernel didn't check, and that leanchecker replays it. Then it runs the tool on
tests/prooftest/Buffers.ll, as a developer would: a scalar byte sum and a vector
one agree, and a vector one with a lane masked off doesn't, at the least input, `00 00 01 00`, which the
kernel confirms on `Mem`; the same for in-place XORs, where the planted bug returns the same and leaves
different memory, and tools/verify.py confirms it too; a function that reads past what it's given is undefined
where the reference returns; a function that stops the model where the other returns, as the candidate or as
the reference, is unknown, never a pass, and a reference undefined on every input is vacuous; a statement
written by hand over a buffer; a memory the search can't run on `ExecMem`, which runs on `Mem`; a pointer into
no buffer the statement binds; two functions with different signatures; and a stored failure tried first.

usage: tests/prooftest_memory_test.py path/to/ir-lean [--only NAME ...] [--static]
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
from irlean import proc  # noqa: E402

TOOL = ROOT / "tools" / "prooftest" / "prooftest.py"
BUFFERS = ROOT / "tests" / "prooftest" / "Buffers.ll"
DOC = ROOT / "docs" / "proof-tests.md"


def load() -> Any:
    spec = importlib.util.spec_from_file_location("prooftest_tool", TOOL)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BUFFER = {"name": "b", "kind": "buffer", "max": 256}
POINTER = {"name": "p", "kind": "pointer", "of": 0}
LENGTH = {"name": "n", "kind": "length", "of": 1}
VALUE = {"name": "x", "kind": "bitvec", "width": 32}


def decode(flat: list[int], binders: list[dict[str, Any]]) -> list[Any]:
    """What tools/prooftest/Harness.lean's `bytesOf` reads back from an input, in Python."""
    out: list[Any] = []
    for i, b in enumerate(binders):
        if b["kind"] == "buffer":
            start = flat[i]
            out.append(tuple(flat[start + 1 : start + 1 + flat[start]]))
        else:
            out.append(flat[i])
    return out


def static_checks(pt: Any) -> list[str]:
    failures: list[str] = []

    def check(condition: bool, what: str) -> None:
        if not condition:
            failures.append(what)

    binders = [BUFFER, POINTER, LENGTH, VALUE]
    unit = pt.Memory(0, binders)
    check(unit.indices == [0, 1, 2], f"a buffer goes with its pointer and length: {unit.indices}")
    edges = unit.edges()
    lengths = [n for _, _, n in edges]
    offsets = [k for _, k, _ in edges]
    check(edges[0] == ((), 0, 0), f"the empty buffer is the first edge: {edges[0]}")
    check(
        {0, 1, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255, 256} <= set(lengths),
        f"edges have lengths at each side of 16, 32 and 64: {sorted(set(lengths))}",
    )
    check(
        any(len(b) > 0 and n == 0 for b, _, n in edges),
        "an edge has a length of 0 in a buffer that isn't empty",
    )
    check(
        {1, 3, 4, 8, 15} <= {k for k, n in zip(offsets, lengths, strict=True) if n in (16, 32, 64)},
        "edges have unaligned pointers at the block sizes",
    )
    check(all(len(b) <= 256 and k + n <= len(b) for b, k, n in edges), "every edge fits its buffer")
    patterns = unit.patterns()
    check(
        all(
            any(b[k + j] and not any(b[:j] + b[j + 1 :]) for b, k, n in patterns if n == 64)
            for j in range(64)
        ),
        "patterns set each byte of 64 alone",
    )
    rng = random.Random(3)
    drawn = [unit.draw(rng) for _ in range(3000)]
    check(all(len(b) <= 256 and k + n <= len(b) for b, k, n in drawn), "random buffers fit")
    check(len({n for _, _, n in drawn}) > 100, "random lengths vary")
    check(sum(k % 16 != 0 for _, k, _ in drawn) > 500, "random pointers are often unaligned")

    a = pt.plan(binders, seed=5, max_inputs=3000)
    b = pt.plan(binders, seed=5, max_inputs=3000)
    check(a.inputs == b.inputs, "the plan is the same for the same seed")
    check(len(a.inputs) == 3000 and not a.exhaustive, "a buffer is never tried exhaustively")
    check(list(dict.fromkeys(a.phases))[:3] == ["edges", "patterns", "bytes"], "edges, then patterns")
    check(
        all(pt.fits(binders, [pt.stored_value(v) for v in values]) for values in a.inputs),
        "every planned input fits its binders",
    )
    flat = pt.wire(binders, a.inputs[40])
    check(decode(flat, binders)[:3] == list(a.inputs[40][:3]), "the harness reads back the buffer it's sent")
    check(
        pt.jsonable(binders, a.inputs[40])[0] == list(a.inputs[40][0]), "a buffer is a list of bytes in JSON"
    )

    check(pt.fits(binders, [[1, 2, 3], 1, 2, 0]), "a stored buffer, pointer and length that fit")
    check(not pt.fits(binders, [[1, 2, 3], 4, 0, 0]), "a pointer past the buffer doesn't fit")
    check(not pt.fits(binders, [[1, 2, 3], 1, 3, 0]), "a length past the buffer doesn't fit")
    check(not pt.fits(binders, [[256], 0, 1, 0]), "a byte over 255 doesn't fit")
    check(not pt.fits(binders, [[0] * 257, 0, 0, 0]), "a buffer over its most doesn't fit")

    def lane2(candidates: list[tuple]) -> int | None:
        """Fails when a byte the 4-lane loop reads, at 2 modulo 4, isn't zero."""
        for i, (data, k, n, _) in enumerate(candidates):
            read = data[k : k + n]
            if any(read[j] for j in range(2, n - n % 4, 4)):
                return i
        return None

    start = (tuple(range(1, 41)), 3, 33, 0xFFFFFFFF)
    shrunk, steps = pt.shrink(start, binders, lane2)
    check(shrunk == ((0, 0, 1, 0), 0, 4, 0) and steps > 0, f"a lane bug shrinks to 00 00 01 00, not {shrunk}")
    check(pt.shrink(start, binders, lane2)[0] == shrunk, "shrinking a buffer is deterministic")
    check(
        pt.simplicity(((1,), 0, 1, 0)) < pt.simplicity(((0, 0), 0, 2, 0)),
        "a shorter buffer is simpler, whatever its bytes",
    )
    moved = unit.remove(((1, 2, 3, 4, 5, 6), 2, 3, 0)[:3], 0, 3)
    check(
        moved == ((4, 5, 6), 0, 2), f"taking bytes out moves the pointer and keeps the length's end: {moved}"
    )

    with tempfile.TemporaryDirectory() as temporary:
        store = pt.Store(Path(temporary))
        key = pt.property_key("∀ b p n x, P", binders)
        store.add(key, {"values": [[0, 0, 1, 0], 0, 4, 0]}, {"function": "f", "statement": "s"})
        store.add(key, {"values": [[0, 0, 1, 0], 0, 4, 0]}, {"function": "f", "statement": "s"})
        check(
            store.load(key, binders) == [((0, 0, 1, 0), 0, 4, 0)], "the store keeps a buffer once, as a tuple"
        )

    check(
        pt.roles(["i32", "ptr", "i64"], None) == ["value", "buffer", "length"], "(crc, buf, len) by default"
    )
    check(
        pt.roles(["ptr", "ptr", "i64"], None) == ["buffer", "buffer", "length"],
        "a length is of the last buffer",
    )
    for params, given in ((["ptr"], ["value"]), (["i64"], ["length"]), (["i32"], ["buffer"])):
        try:
            pt.roles(params, given)
            failures.append(f"{given} for {params} is refused")
        except pt.Stop:
            pass

    def built(signature: str, roles: list[str] | None = None, memory: bool = True) -> tuple[str, Any]:
        run = pt.Run(
            {
                "function": "f",
                "namespace": "M",
                "input": {"ir": "x.ll"},
                "equivalence": {"with": "g", "arguments": roles, "max_length": 64},
            },
            Path(),
            Path(),
            0.0,
            0.0,
        )
        functions = {
            name: {"lean_name": name, "signature": signature, "uses_memory": memory} for name in ("f", "g")
        }
        original = pt.report
        pt.report = lambda _run: functions
        try:
            return pt.equivalence_statement(run), run
        finally:
            pt.report = original

    statement, run = built("(i32,ptr,i64)->i32")
    f = "(M.f (some x0) (p1.into M.initial 0) n2.toVal (IRLean.Ptf.place M.initial [b1.bytes]))"
    g = "(M.g (some x0) (p1.into M.initial 0) n2.toVal (IRLean.Ptf.place M.initial [b1.bytes]))"
    expected = (
        "∀ (b1 : IRLean.Ptf.Buffer 64) (p1 : IRLean.Ptf.Pointer b1) (n2 : IRLean.Ptf.Length p1) "
        f"(x0 : BitVec 32), IRLean.Ptf.Answers {f} → IRLean.Ptf.Returns {f} → IRLean.Ptf.Answers {g} → "
    )
    check(
        statement.startswith(expected),
        f"the equivalence of (crc, buf, len) is built as expected: {statement}",
    )
    check(
        run.model_hypotheses == {0: "f", 2: "g"},
        "the first and third hypotheses are false only where a function stops the model: "
        f"{run.model_hypotheses}",
    )
    check(
        statement.endswith(
            "→ IRLean.Ptf.Same (IRLean.Ptf.place M.initial [b1.bytes]) (M.f (some x0) (p1.into M.initial 0) "
            "n2.toVal (IRLean.Ptf.place M.initial [b1.bytes])) (M.g (some x0) (p1.into M.initial 0) n2.toVal "
            "(IRLean.Ptf.place M.initial [b1.bytes]))"
        ),
        f"and it claims Same of the two calls: {statement}",
    )
    pure, _ = built("(i8,i8)->i8", memory=False)
    check(
        pure == "∀ (x0 : BitVec 8) (x1 : BitVec 8), IRLean.Ptf.Answers (M.f (some x0) (some x1)) → "
        "IRLean.Ptf.Returns (M.f (some x0) (some x1)) → IRLean.Ptf.Answers (M.g (some x0) (some x1)) → "
        "(M.f (some x0) (some x1)) = (M.g (some x0) (some x1))",
        f"two functions without memory are equal where the first returns: {pure}",
    )

    for raw in (
        {"input": {"ir": str(BUFFERS)}, "function": "f"},
        {"input": {"ir": str(BUFFERS)}, "function": "f", "statement": "True", "equivalence": {"with": "g"}},
        {"input": {"ir": str(BUFFERS)}, "function": "f", "equivalence": {"with": "f"}},
        {
            "input": {"ir": str(BUFFERS)},
            "function": "f",
            "equivalence": {"with": "g", "arguments": ["pointer"]},
        },
    ):
        try:
            pt.load_request(raw, ROOT)
            failures.append(f"{raw} is refused")
        except pt.Stop as stop:
            check(stop.reason == "invalid_request", f"{raw} is invalid_request, not {stop.reason}")
    check("equivalence" in pt.REQUEST_JSON_SCHEMA["properties"], "the JSON Schema has equivalence")
    doc = DOC.read_text()
    for name in ("#### Memory", "IRLean.Ptf.Buffer", "IRLean.Ptf.Same", "toMem_placeExec", "### Equivalence"):
        check(name in doc, f"docs/proof-tests.md has {name}")
    return failures


# The tool, on tests/prooftest/Buffers.ll


@dataclass
class Case:
    name: str
    function: str
    status: str
    reason: str
    statement: str | None = None
    equivalent: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)
    check: Callable[[dict[str, Any]], str | None] | None = None
    again: Callable[[dict[str, Any]], str | None] | None = None


def shown(result: dict[str, Any]) -> dict[str, str]:
    return (result.get("counterexample") or {}).get("shown") or {}


def expect(condition: bool, why: str) -> str | None:
    return None if condition else why


def on_exec_memory(result: dict[str, Any], calls: int) -> bool:
    return (result.get("memory") or {}).get("calls") == {"exec_memory": calls, "mem": 0}


LANE = "4 bytes: 00 00 01 00"
SUM = "Buffers.sum_scalar (p.into Buffers.initial 0) n.toVal (IRLean.Ptf.place Buffers.initial [b.bytes])"


def cases() -> list[Case]:
    return [
        Case(
            "sum_agrees",
            "sum_scalar",
            "passed_tier1",
            "sampled",
            equivalent="sum_vec",
            extra={"max_inputs": 1000},
            check=lambda r: expect(
                r["inputs"]["satisfied"] == 1000
                and on_exec_memory(r, 5)
                and r["inputs"]["memory"]["met_hypotheses"]["n1"]["max"] == 256
                and r["inputs"]["memory"]["met_hypotheses"]["p0"]["unaligned_16"] > 0
                and "search.executable_memory" in {t["id"] for t in r["trusted"]},
                "1000 inputs, every one where the reference returned, up to 256 bytes, some unaligned, run "
                f"on ExecMem, which the result says it rests on: {r['inputs']}, {r['memory']}",
            ),
        ),
        Case(
            "sum_lane_wrong",
            "sum_scalar",
            "counterexample",
            "kernel_refuted",
            equivalent="sum_vec_bad",
            check=lambda r: expect(
                shown(r) == {"b0": LANE, "p0": "0 bytes in", "n1": "4"}
                and set(r["counterexample"]["kernel"]["axioms"])
                <= {"propext", "Classical.choice", "Quot.sound"}
                and r["counterexample"]["found"]["phase"] == "edges",
                f"refuted on an edge, shrunk to {LANE}, and the kernel checks it on Mem: {shown(r)}",
            ),
            again=lambda r: expect(
                r["counterexample"]["found"]["phase"] == "replay"
                and r["counterexample"]["found"]["index"] == 0,
                f"the stored buffer is tried first: {r['counterexample']['found']}",
            ),
        ),
        Case(
            "xor_agrees",
            "xor_scalar",
            "passed_tier1",
            "sampled",
            equivalent="xor_vec",
            extra={"max_inputs": 1000, "store": None},
            check=lambda r: expect(on_exec_memory(r, 5), f"run on ExecMem: {r['memory']}"),
        ),
        Case(
            "xor_lane_stored_wrong",
            "xor_scalar",
            "counterexample",
            "kernel_refuted",
            equivalent="xor_vec_bad",
            extra={"store": None, "verify_confirm": "always"},
            check=lambda r: expect(
                shown(r) == {"b0": LANE, "p0": "0 bytes in", "n1": "4", "x2": "0#8"}
                and r["counterexample"]["evidence"] == ["kernel", "compiled_evaluation"],
                "the same result and different memory is a counterexample, which the kernel and "
                f"tools/verify.py both confirm: {shown(r)}, {r['counterexample']['evidence']}",
            ),
        ),
        Case(
            "reads_past_the_end",
            "sum_scalar",
            "counterexample",
            "compiled_evaluation",
            equivalent="sum_overread",
            extra={"store": None},
            check=lambda r: expect(
                shown(r) == {"b0": "0 bytes: (none)", "p0": "0 bytes in", "n1": "0"}
                and not r["counterexample"]["kernel"]["ok"],
                "undefined where the reference returns, at the empty buffer, which tools/verify.py confirms "
                f"since the kernel can't follow the call inside: {shown(r)}",
            ),
        ),
        Case(
            "candidate_stops_the_model",
            "sum_scalar",
            "unknown",
            "model_stopped",
            equivalent="sum_stops",
            extra={"store": None, "max_inputs": 256},
            check=lambda r: expect(
                r["inputs"]["model_stopped"] > 200
                and r["inputs"]["discarded"] == 0
                and r["inputs"]["satisfied"] + r["inputs"]["model_stopped"] == r["inputs"]["tried"] == 256
                and "@sum_stops on" in r["detail"],
                "the candidate stops the model past 3 bytes, where the reference returns: those inputs are "
                f"counted apart, not discarded, and aren't a pass: {r['inputs']}, {r['detail']}",
            ),
        ),
        Case(
            "reference_stops_the_model",
            "sum_stops",
            "unknown",
            "model_stopped",
            equivalent="sum_scalar",
            extra={"store": None, "max_inputs": 256},
            check=lambda r: expect(
                r["inputs"]["model_stopped"] > 200
                and r["inputs"]["discarded"] == 0
                and "@sum_stops on" in r["detail"],
                f"the same with the functions swapped: {r['inputs']}, {r['detail']}",
            ),
        ),
        Case(
            "reference_always_undefined",
            "sum_undefined",
            "vacuous",
            "no_input_meets_hypotheses",
            equivalent="sum_scalar",
            extra={"store": None, "max_inputs": 256},
            check=lambda r: expect(
                r["inputs"]["discarded"] == r["inputs"]["tried"] == 256 and r["inputs"]["model_stopped"] == 0,
                f"a reference undefined on every input discards every input: {r['inputs']}",
            ),
        ),
        Case(
            "statement_by_hand",
            "sum_scalar",
            "counterexample",
            "kernel_refuted",
            statement="∀ (b : IRLean.Ptf.Buffer 64) (p : IRLean.Ptf.Pointer b) (n : IRLean.Ptf.Length p), "
            f"IRLean.Outcome.map Prod.fst ({SUM}) ≠ IRLean.Outcome.ok (some 255#32)",
            extra={"store": None},
            check=lambda r: expect(
                shown(r) == {"b": "1 bytes: ff", "p": "0 bytes in", "n": "1"} and on_exec_memory(r, 1),
                f"a spec written over a buffer, false where the bytes sum to 255, at one byte: {shown(r)}",
            ),
        ),
        Case(
            "memory_it_cant_copy",
            "sum_scalar",
            "passed_tier1",
            "sampled",
            statement="∀ (b : IRLean.Ptf.Buffer 16) (p : IRLean.Ptf.Pointer b) (n : IRLean.Ptf.Length p), "
            "IRLean.Ptf.Returns (Buffers.sum_scalar (p.into (default : IRLean.Mem) 0) n.toVal "
            "(IRLean.Ptf.place (default : IRLean.Mem) [b.bytes]))",
            extra={"store": None, "max_inputs": 200},
            check=lambda r: expect(
                (r.get("memory") or {}).get("calls") == {"exec_memory": 0, "mem": 1}
                and "search.executable_memory" not in {t["id"] for t in r["trusted"]},
                "a memory the copy can't stand for runs on Mem, and the result doesn't claim ExecMem: "
                f"{r['memory']}",
            ),
        ),
        Case(
            "pointer_into_no_binder",
            "sum_scalar",
            "unknown",
            "binder_unsupported",
            statement="∀ (p : IRLean.Ptf.Pointer (IRLean.Ptf.Buffer.ofList 4 [])), "
            "IRLean.Ptf.Answers (Buffers.sum_scalar (p.into Buffers.initial 0) (some 0#64) Buffers.initial)",
            extra={"store": None},
        ),
        Case(
            "different_signatures",
            "sum_scalar",
            "unknown",
            "invalid_request",
            equivalent="xor_scalar",
            extra={"store": None},
        ),
    ]


def module_checks() -> str | None:
    """IRLean.Ptf on the standard axioms, with no `implemented_by` or `extern`, replayed by leanchecker."""
    env = {**os.environ, "LEAN_PATH": str(ROOT / ".lake" / "build" / "lib" / "lean")}
    axioms = proc.run(
        ["lean", "-M", "2048", str(ROOT / "tests" / "check_axioms.lean")],
        env={**env, "IRLEAN_CHECK_MODULE": "IRLean.Ptf"},
        timeout=300,
        cwd=ROOT,
    )
    if not axioms.ok or "and 0 from bv_decide" not in axioms.output:
        return f"IRLean.Ptf's axioms: {axioms.output[-2000:]}"
    replay = proc.run(["leanchecker", "IRLean.Ptf"], env=env, timeout=300, cwd=ROOT)
    if not replay.ok:
        return f"leanchecker IRLean.Ptf: {replay.output[-2000:]}"
    return None


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
    request: dict[str, Any] = {
        "input": {"ir": str(BUFFERS)},
        "function": case.function,
        "namespace": "Buffers",
        "store": str(directory / "store"),
        **case.extra,
    }
    if case.statement is not None:
        request["statement"] = case.statement
    if case.equivalent is not None:
        request["equivalence"] = {"with": case.equivalent}
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
        if result["proved"] is not False:
            return result, "tier 1 claimed a proof"
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
        print(
            "ok    static: buffers' inputs, their encoding, shrinking, the store and the equivalence's "
            "statement"
        )
    if args.static:
        return 1 if failed else 0
    if not args.only:
        if failure := module_checks():
            print(f"FAIL  module: {textwrap.shorten(failure, 3000)}")
            failed = True
        else:
            print("ok    module: IRLean.Ptf rests on the standard axioms, and leanchecker replays it")
    selected = [c for c in cases() if not args.only or c.name in args.only]
    # Each case runs at most one Lean process at a time.
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
