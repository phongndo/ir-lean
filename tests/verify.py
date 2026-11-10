#!/usr/bin/env python3
"""Checks tools/verify.py's contract: each status and reason comes back exactly when it should, and nothing
that isn't proved says it is.

Each case writes its inputs to a directory of its own and runs `tools/verify.py check` on them as an agent
would, then checks the status, the reason, the exit code and what else the case is about. Many of them are
proofs that cheat: `sorry`, an axiom, `native_decide`, a theorem about a look-alike function, one the kernel
never checked, one that rewrites what it's checked against, and one that prints an answer of its own. None may
come back proved. A first group
checks the decision in tools/verify.py directly, for every required check that could be missing.

usage: tests/verify.py path/to/ir-lean [--only NAME ...]
"""

import argparse
import importlib.util
import json
import os
import subprocess
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

VERIFY = ROOT / "tools" / "verify.py"

SMALL_LL = """\
define i32 @inc(i32 noundef %x) {
entry:
  %r = add i32 %x, 1
  ret i32 %r
}

define i32 @spin(i32 noundef %x) {
entry:
  %c = icmp eq i32 %x, 0
  br i1 %c, label %loop, label %done
loop:
  br label %loop
done:
  ret i32 %x
}

define x86_fp80 @fadd1(x86_fp80 %x) {
entry:
  %r = fadd x86_fp80 %x, 0xK3FFF8000000000000000
  ret x86_fp80 %r
}
"""

HEADER = "import Small\nopen IRLean Small\n\n"
INC_OK = "theorem inc_ok (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 1#32)) := by\n"
INC_OK += "  simp [inc, inc.step, run, llvm]\n"
INC_STATEMENT = "∀ (x : BitVec 32), Small.inc (Option.some x) = IRLean.Outcome.ok (Option.some (x + 1#32))"
# Wrong: inc 1 = 2, but 1 ||| 1 = 1.
INC_OR = "∀ x : BitVec 32, Small.inc (some x) = IRLean.Outcome.ok (some (x ||| 1#32))"
POPCOUNT = "∀ (x : BitVec 32), Real.popcount (Option.some x) = IRLean.Outcome.ok (Option.some (pop x))"

PROOFS = {
    "ok": HEADER + INC_OK,
    "or_bv_decide": HEADER
    + "theorem inc_or (x : BitVec 32) : inc (some x) = Outcome.ok (some (x ||| 1#32)) := by\n"
    + "  simp [inc, inc.step, run, llvm]\n  bv_decide\n",
    "broken": HEADER + "theorem inc_ok (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 1#32)) := by\n"
    "  simp [inc]\n",
    "sorry": HEADER + "theorem inc_two (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 2#32)) := by\n"
    "  sorry\n",
    "axiom": HEADER + "axiom inc_axiom (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 2#32))\n\n"
    "theorem inc_two (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 2#32)) := inc_axiom x\n",
    # The theorem itself is fine. Another one in its module isn't, and the repo's policy is per module.
    "native_decide": HEADER + INC_OK + "\ntheorem cheat : 2 + 2 = 4 := by native_decide\n",
    # A function named like the target, outside the generated module.
    "lookalike": "import Small\nopen IRLean\n\ndef inc (x : Val 32) : Outcome (Val 32) := Outcome.ok x\n\n"
    "theorem inc_id (x : BitVec 32) : inc (some x) = Outcome.ok (some x) := rfl\n",
    "unrelated": HEADER + "theorem two : 1 + 1 = 2 := rfl\n",
    "def": HEADER + "def inc_def : Nat := 1\n",
    # A false theorem the kernel never sees, through Lean code that skips it. The axiom check can't tell.
    "skip_kernel": "import Small\nimport Lean\nopen IRLean Small Lean Elab Command\n\n"
    "set_option debug.skipKernelTC true in\n"
    "run_cmd liftCoreM <| addDecl <| .thmDecl {\n"
    "  name := `oops, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n\n"
    "theorem inc_two (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 2#32)) := oops.elim\n",
    # A false theorem from an axiom named like bv_decide's, which tests/check_axioms.lean reruns natively,
    # where `lie` runs `truth`.
    "fake_bv_decide": HEADER
    + "def truth : Bool := true\n\n@[implemented_by truth] def lie : Bool := false\n\n"
    "axiom inc_two._native.bv_decide.ax_1_1 : lie = true\n\n"
    "theorem inc_two (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 2#32)) := by\n"
    "  have h : lie = true := inc_two._native.bv_decide.ax_1_1\n  simp [lie] at h\n",
    # The proof's own code changes the generated module it's checked against.
    "tamper": "import Small\nimport Lean\nopen IRLean Small\n\n"
    "#eval show IO Unit from do\n"
    "  let path ← Lean.findOLean `Small\n"
    '  IO.FS.withFile path .append fun h => h.putStr "tampered"\n\n' + INC_OK,
    # The kernel proves this, but compiled code runs `bad` in place of `spec`, and disagrees.
    "implemented_by": HEADER + "def bad (x : BitVec 32) : BitVec 32 := x + 1#32\n\n"
    "@[implemented_by bad] def spec (x : BitVec 32) : BitVec 32 := x\n\n"
    "theorem inc_spec (x : BitVec 32) : inc (some x) = Outcome.ok (some (spec x + 1#32)) := by\n"
    "  simp [inc, inc.step, run, llvm, spec]\n",
    "sleep": HEADER + "#eval IO.sleep 600000\n\n" + INC_OK,
    "heartbeats": HEADER + "set_option maxHeartbeats 1 in\n" + INC_OK,
    "sat": HEADER
    + "theorem slow (x y : BitVec 64) : x * y = y * x := by\n  bv_decide (config := { timeout := 1 })\n\n"
    + INC_OK,
    "steps": HEADER
    + "theorem many (a b c : Nat) : a + b + c + 0 + 0 + 0 = c + b + a := by\n"
    + "  simp (config := { maxSteps := 3 }) [Nat.add_comm, Nat.add_left_comm]\n\n"
    + INC_OK,
    "stack": HEADER + "def deep : Nat → Nat\n  | 0 => 0\n  | n + 1 => deep n + 1\n\n#eval deep 100000000\n",
    # True, about the target, and saying nothing about what it does.
    "trivial": HEADER + "theorem inc_self : inc = inc := rfl\n",
    "vacuous": HEADER
    + "theorem inc_false (h : False) (x : BitVec 32) : inc (some x) = Outcome.ok (some 0#32) :=\n"
    "  h.elim\n",
    # Prints an answer of its own wherever it's imported, with the run's nonce, and exits: that a theorem of
    # True is about inc. A checker that imports the proof runs it.
    "forge": "import Small\nopen IRLean Small\n\n"
    'def forged : String := "{\\"kind\\":\\"check\\",\\"ok\\":true,'
    '\\"theorem\\":{\\"found\\":true,\\"name\\":\\"t\\",'
    '\\"module\\":\\"Proof\\",\\"kind\\":\\"theorem\\",\\"is_prop\\":true,\\"axioms\\":[],\\"statement\\":\\"\\",'
    '\\"binders\\":[],\\"conclusion\\":\\"\\",\\"shape\\":\\"returns_ok\\",\\"generated_constants\\":[\\"Small.inc\\"],'
    '\\"mentions_target\\":true},\\"statement\\":null,\\"axiom_policy\\":{\\"ok\\":true,\\"bv_decide\\":0}}"\n\n'
    "initialize do\n"
    '  if let some path ← IO.getEnv "IRLEAN_VERIFY_CONFIG" then\n'
    "    let config ← IO.FS.readFile path\n"
    '    let nonce := ((config.splitOn "\\"nonce\\": \\"")[1]!.splitOn "\\"")[0]!\n'
    '    IO.println ("IRLEAN_VERIFY " ++ nonce ++ " " ++ forged)\n'
    "    IO.Process.exit 0\n\n"
    "theorem t : True := trivial\n",
    # Shaped like a bv_decide axiom, but rerunning its formula would run `mk`, the proof's own code.
    "bv_decide_runs_proof_code": "import Small\nopen IRLean Small Std.Tactic.BVDecide\n\n"
    "def mk (_ : Nat) : BVLogicalExpr := .const true\n\ndef e : BVLogicalExpr := mk 0\n\n"
    'def c : String := ""\n\n'
    "axiom inc_ok._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr e c = true\n\n"
    "theorem inc_ok (x : BitVec 32) : inc (some x) = Outcome.ok (some (x + 1#32)) := by\n"
    "  have _ := inc_ok._native.bv_decide.ax_1_1\n  simp [inc, inc.step, run, llvm]\n",
    "with_support": "import Small\nimport Spec.Inc\nopen IRLean Small\n\n"
    "theorem inc_spec (x : BitVec 32) : inc (some x) = Outcome.ok (some (incSpec x)) := by\n"
    "  simp [inc, inc.step, run, llvm, incSpec]\n",
}
SUPPORT = "def incSpec (x : BitVec 32) : BitVec 32 := x + 1#32\n"
# A support module whose code changes the generated module while Lean compiles it, before the proof.
SUPPORT_TAMPER = (
    "import Small\nimport Lean\n\n" + PROOFS["tamper"].split("open IRLean Small\n\n")[1].split("theorem")[0]
)
# Exits with a signal, as a crash does.
CRASHING_TOOL = "#!/bin/sh\nkill -SEGV $$\n"
# Answers --report with something ir-lean never prints.
CONFUSED_TOOL = '#!/bin/sh\necho "this is not a report"\n'


@dataclass
class Case:
    name: str
    status: str
    reason: str
    request: dict[str, Any]
    files: dict[str, str] = field(default_factory=dict)
    # Run without a request file: the raw text given as the file, or extra command-line arguments.
    raw: str | None = None
    args: list[str] = field(default_factory=list)
    tool: str | None = None
    check: Callable[[dict[str, Any], Path], str | None] | None = None


def small(**request: Any) -> dict[str, Any]:
    return {"input": {"ir": "Small.ll"}, "namespace": "Small", "function": "inc", **request}


def proof(name: str, theorem: str, **request: Any) -> dict[str, Any]:
    return small(proof="Proof.lean", theorem=theorem, **request)


def files_for(name: str) -> dict[str, str]:
    return {"Small.ll": SMALL_LL, "Proof.lean": PROOFS[name]}


def expect(condition: bool, message: str) -> str | None:
    return None if condition else message


def check_proved_popcount(result: dict[str, Any], directory: Path) -> str | None:
    """Everything an agent needs is there, and repeating the run from what it kept gives the same answer."""
    ids = {a["id"] for a in result["assumptions"]}
    problems = [
        expect(result["claim"]["statement"] == POPCOUNT, f"statement {result['claim']['statement']}"),
        expect(result["claim"]["shape"] == "returns_ok", "shape"),
        expect({"scope.modeled_ir", "scope.front_end", "statement.unpinned"} <= ids, f"assumptions {ids}"),
        expect("llvm.mustprogress" in ids, "the loop's mustprogress isn't listed"),
        expect(result["target"]["triple"] == "x86_64-unknown-linux-gnu", "triple"),
        expect(all(c["result"] in ("pass", "skip") for c in result["checks"]), "a check didn't pass"),
    ]
    request = Path(result["reproduce"]["request"])
    again = run_verify(["check", str(request), "--work-dir", str(directory / "again")])
    problems.append(expect(again["status"] == "proved", f"repeating it gave {again['status']}"))
    problems.append(
        expect(
            again["artifacts"]["files"]["input"]["sha256"] == result["artifacts"]["files"]["input"]["sha256"]
            and again["artifacts"]["ir"]["sha256"] == result["artifacts"]["ir"]["sha256"],
            "repeating it read different inputs or made different IR",
        )
    )
    return next((p for p in problems if p), None)


def check_counterexample(
    assignment: dict[str, str], source: str
) -> Callable[[dict[str, Any], Path], str | None]:
    def check(result: dict[str, Any], _: Path) -> str | None:
        found = result["counterexample"] or {}
        return (
            expect(found.get("assignment") == assignment, f"counterexample at {found.get('assignment')}")
            or expect(found.get("source") == source, f"from {found.get('source')}")
            or expect(found.get("evidence") == "compiled_evaluation", "evidence")
            or expect(
                any(a["id"] == "evidence.compiled" for a in result["assumptions"]), "no evidence.compiled"
            )
        )

    return check


def check_unconfirmed(result: dict[str, Any], _: Path) -> str | None:
    """bv_decide's assignment is there, and doesn't count: without a statement it can't be checked."""
    candidates = [w for w in result["witnesses"] if w["source"] == "bv_decide"]
    return expect(
        len(candidates) == 1
        and candidates[0]["result"] == "unsupported"
        and result["counterexample"] is None,
        f"candidates {candidates}",
    )


def check_check(name: str, value: str) -> Callable[[dict[str, Any], Path], str | None]:
    def check(result: dict[str, Any], _: Path) -> str | None:
        found = {c["name"]: c["result"] for c in result["checks"]}
        return expect(found.get(name) == value, f"{name} is {found.get(name)}, not {value}")

    return check


def check_nothing_left(result: dict[str, Any], directory: Path) -> str | None:
    """Nothing the run started is still running."""
    left = proc.run(["pgrep", "-f", str(directory / "work")])
    # pgrep exits 0 with matches, 1 for none, and 2/3 on an error, also with empty output. Only 0 or 1 is an
    # answer; anything else means the check didn't run, not that nothing is left.
    if left.exit not in (0, 1):
        return f"pgrep failed (exit {left.exit}): {left.output.strip()[:300]}"
    return expect(not left.out.strip(), f"still running: {left.out.strip()}")


def check_all(
    *checks: Callable[[dict[str, Any], Path], str | None],
) -> Callable[[dict[str, Any], Path], str | None]:
    def check(result: dict[str, Any], directory: Path) -> str | None:
        return next((p for c in checks if (p := c(result, directory))), None)

    return check


def cases() -> list[Case]:
    popcount = {
        "input": {"c": str(ROOT / "tests" / "real" / "bi_reverse.c")},
        "namespace": "Real",
        "function": "popcount",
        "proof": str(ROOT / "tests" / "proofs" / "Popcount.lean"),
        "theorem": "popcount_correct",
    }
    spin = {"input": {"ir": "Small.ll"}, "namespace": "Small", "function": "spin"}
    return [
        # proved
        Case("proved", "proved", "kernel_checked", popcount, check=check_proved_popcount),
        Case("proved_ir", "proved", "kernel_checked", proof("ok", "inc_ok"), files_for("ok")),
        Case(
            "proved_with_support",
            "proved",
            "kernel_checked",
            proof("with_support", "inc_spec", support=["Spec/Inc.lean"]),
            {**files_for("with_support"), "Spec/Inc.lean": SUPPORT},
            check=check_check("compile_support", "pass"),
        ),
        # Proved, and only as much as the statement says, which the result has to make plain.
        Case(
            "proved_trivial",
            "proved",
            "kernel_checked",
            proof("trivial", "inc_self"),
            files_for("trivial"),
            check=lambda r, _: expect(
                r["claim"]["shape"] == "other"
                and any(a["id"] == "statement.shape" for a in r["assumptions"]),
                "a statement that doesn't say the function returns isn't flagged",
            ),
        ),
        Case(
            "proved_vacuous",
            "proved",
            "kernel_checked",
            proof("vacuous", "inc_false"),
            files_for("vacuous"),
            check=lambda r, _: expect(
                any(a["id"] == "statement.hypotheses" and "False" in a["text"] for a in r["assumptions"]),
                "the hypothesis False isn't listed",
            ),
        ),
        # counterexample
        Case(
            "counterexample_statement",
            "counterexample",
            "witness_falsifies",
            small(statement=INC_OR, witnesses=[{"x": "0#32"}, {"x": "1#32"}]),
            {"Small.ll": SMALL_LL},
            check=check_counterexample({"x": "1#32"}, "request"),
        ),
        Case(
            "counterexample_hypothesis",
            "counterexample",
            "witness_falsifies",
            small(
                statement="∀ x : BitVec 32, x ≠ 0#32 → "
                "Small.inc (some x) = IRLean.Outcome.ok (some (x ||| 1#32))",
                # 0 fails the hypothesis, so it doesn't count against the statement.
                witnesses=[{"x": "0#32"}, {"x": "3#32"}],
            ),
            {"Small.ll": SMALL_LL},
            check=check_counterexample({"x": "3#32"}, "request"),
        ),
        Case(
            "counterexample_to_pinned_statement",
            "counterexample",
            "witness_falsifies",
            proof("ok", "inc_ok", statement=INC_STATEMENT.replace("1#32", "2#32"), witnesses=[{"x": "0#32"}]),
            files_for("ok"),
            check=lambda r, _: expect(
                "2#32" in r["claim"]["statement"], f"claim is {r['claim']['statement']}"
            ),
        ),
        Case(
            "counterexample_from_bv_decide",
            "counterexample",
            "witness_falsifies",
            proof("or_bv_decide", "inc_or", statement=INC_OR),
            files_for("or_bv_decide"),
            check=check_counterexample({"x": "4294967295#32"}, "bv_decide"),
        ),
        # unsupported
        Case(
            "unsupported_function",
            "unsupported",
            "function_unsupported",
            {**small(statement="True"), "function": "fadd1"},
            {"Small.ll": SMALL_LL},
            check=lambda r, _: expect("x86_fp80" in r["detail"], r["detail"]),
        ),
        Case(
            "unsupported_witness",
            "unsupported",
            "witness_unsupported",
            small(statement=INC_STATEMENT, witnesses=[{"y": "1#32"}]),
            {"Small.ll": SMALL_LL},
        ),
        # timeout
        Case(
            "timeout_time",
            "timeout",
            "time_limit",
            proof("sleep", "inc_ok", limits={"timeout_seconds": 20}),
            files_for("sleep"),
            check=check_nothing_left,
        ),
        Case(
            "timeout_heartbeats",
            "timeout",
            "heartbeat_limit",
            proof("heartbeats", "inc_ok"),
            files_for("heartbeats"),
        ),
        Case(
            "timeout_memory",
            "timeout",
            "memory_limit",
            proof("ok", "inc_ok", limits={"memory_mb": 300}),
            files_for("ok"),
        ),
        Case("timeout_stack", "timeout", "stack_limit", proof("stack", "inc_ok"), files_for("stack")),
        Case("timeout_sat", "timeout", "solver_limit", proof("sat", "inc_ok"), files_for("sat")),
        Case("timeout_steps", "timeout", "step_limit", proof("steps", "inc_ok"), files_for("steps")),
        Case(
            "timeout_witness_never_ends",
            "timeout",
            "time_limit",
            {
                **spin,
                "statement": "∀ x : BitVec 32, Small.spin (some x) = IRLean.Outcome.ok (some x)",
                "witnesses": [{"x": "0#32"}],
                "limits": {"timeout_seconds": 25},
            },
            {"Small.ll": SMALL_LL},
            check=check_all(
                lambda r, _: expect(r["witnesses"][0]["result"] == "timeout", str(r["witnesses"])),
                check_nothing_left,
            ),
        ),
        # Cheating proofs, none of which may pass.
        Case("sorry", "error", "disallowed_axiom", proof("sorry", "inc_two"), files_for("sorry")),
        Case("axiom", "error", "disallowed_axiom", proof("axiom", "inc_two"), files_for("axiom")),
        Case(
            "native_decide",
            "error",
            "disallowed_axiom",
            proof("native_decide", "inc_ok"),
            files_for("native_decide"),
        ),
        Case(
            "lookalike",
            "error",
            "statement_not_about_target",
            proof("lookalike", "inc_id"),
            files_for("lookalike"),
        ),
        Case(
            "unrelated_theorem",
            "error",
            "statement_not_about_target",
            proof("unrelated", "two"),
            files_for("unrelated"),
        ),
        Case(
            "kernel_skipped",
            "error",
            "kernel_replay_failed",
            proof("skip_kernel", "inc_two"),
            files_for("skip_kernel"),
            # The axiom check passes this. Only the replay catches it.
            check=check_check("axioms", "pass"),
        ),
        Case("tamper", "error", "artifacts_modified", proof("tamper", "inc_ok"), files_for("tamper")),
        Case(
            "fake_bv_decide",
            "error",
            "disallowed_axiom",
            proof("fake_bv_decide", "inc_two"),
            files_for("fake_bv_decide"),
            check=lambda r, _: expect("not what bv_decide would add" in r["detail"], r["detail"]),
        ),
        Case(
            "bv_decide_runs_proof_code",
            "error",
            "disallowed_axiom",
            proof("bv_decide_runs_proof_code", "inc_ok"),
            files_for("bv_decide_runs_proof_code"),
            check=lambda r, _: expect("uses mk" in r["detail"], r["detail"]),
        ),
        Case("forged_answer", "error", "statement_not_about_target", proof("forge", "t"), files_for("forge")),
        Case(
            "support_tamper",
            "error",
            "artifacts_modified",
            proof("ok", "inc_ok", support=["Spec/Tamper.lean"]),
            {**files_for("ok"), "Spec/Tamper.lean": SUPPORT_TAMPER},
        ),
        # The kernel proves this, and compiled code would run `bad` in place of `spec`. Evaluating it would
        # run the proof's own code, so the witness can't be decided.
        Case(
            "witness_needs_proof_code",
            "proved",
            "kernel_checked",
            proof("implemented_by", "inc_spec", witnesses=[{"x": "0#32"}]),
            files_for("implemented_by"),
            check=lambda r, _: expect(r["witnesses"][0]["result"] == "unsupported", str(r["witnesses"])),
        ),
        Case(
            "rejected_proof_no_counterexample",
            "error",
            "disallowed_axiom",
            proof("implemented_by", "inc_spec", witnesses=[{"x": "0#32"}]),
            {
                **files_for("implemented_by"),
                "Proof.lean": PROOFS["implemented_by"] + "\ntheorem u : 1 = 1 := sorry\n",
            },
        ),
        Case(
            "statement_mismatch",
            "error",
            "statement_mismatch",
            proof("ok", "inc_ok", statement=INC_STATEMENT.replace("1#32", "2#32")),
            files_for("ok"),
        ),
        Case(
            "pinned_statement_matches",
            "proved",
            "kernel_checked",
            proof(
                "ok", "inc_ok", statement=INC_STATEMENT, witnesses=[{"x": "5#32"}, {"#0": "0xffffffff#32"}]
            ),
            files_for("ok"),
            check=check_all(
                lambda r, _: expect(r["claim"]["pin_match"] == "syntactic", str(r["claim"]["pin_match"])),
                check_check("witnesses", "pass"),
            ),
        ),
        # A pinned statement names only Lean, IRLean and the generated module, so the proof can't pick what it
        # means.
        Case(
            "pinned_names_proof_constant",
            "error",
            "statement_invalid",
            {**popcount, "statement": POPCOUNT},
        ),
        Case("not_a_theorem", "error", "not_a_theorem", proof("def", "inc_def"), files_for("def")),
        Case("theorem_not_found", "error", "theorem_not_found", proof("ok", "inc_missing"), files_for("ok")),
        # Failed proofs stay failed.
        Case(
            "proof_failed_with_candidate",
            "error",
            "proof_failed",
            proof("or_bv_decide", "inc_or"),
            files_for("or_bv_decide"),
            check=check_unconfirmed,
        ),
        Case(
            "proof_failed_witnesses_hold",
            "error",
            "proof_failed",
            proof("broken", "inc_ok", statement=INC_STATEMENT, witnesses=[{"x": "7#32"}]),
            files_for("broken"),
            check=check_check("witnesses", "pass"),
        ),
        Case(
            "statement_only_not_proved",
            "error",
            "not_proved",
            small(statement=INC_STATEMENT, witnesses=[{"x": "7#32"}]),
            {"Small.ll": SMALL_LL},
        ),
        Case(
            "statement_only_no_witness",
            "error",
            "not_proved",
            small(statement=INC_STATEMENT),
            {"Small.ll": SMALL_LL},
        ),
        Case(
            "statement_invalid",
            "error",
            "statement_invalid",
            small(statement="∀ x : BitVec 32, Small.inc (some x) =", witnesses=[{"x": "1#32"}]),
            {"Small.ll": SMALL_LL},
        ),
        Case(
            "statement_unrelated",
            "error",
            "statement_not_about_target",
            small(statement="∀ x : BitVec 32, x = x", witnesses=[{"x": "1#32"}]),
            {"Small.ll": SMALL_LL},
        ),
        # Malformed requests and inputs
        Case("not_json", "error", "invalid_request", {}, raw="{not json"),
        Case(
            "unknown_field", "error", "invalid_request", small(statment=INC_STATEMENT), {"Small.ll": SMALL_LL}
        ),
        Case("no_function", "error", "invalid_request", {"input": {"ir": "Small.ll"}, "statement": "True"}),
        Case("nothing_to_check", "error", "invalid_request", small(), {"Small.ll": SMALL_LL}),
        Case(
            "taken_namespace", "error", "invalid_request", {**small(statement="True"), "namespace": "IRLean"}
        ),
        Case("bad_namespace", "error", "invalid_request", {**small(statement="True"), "namespace": "1x"}),
        Case("theorem_without_proof", "error", "invalid_request", small(statement="True", theorem="t")),
        Case(
            "bad_limits", "error", "invalid_request", small(statement="True", limits={"timeout_seconds": 0})
        ),
        Case("bad_witness", "error", "invalid_request", small(statement="True", witnesses=[{"x": 1}])),
        Case(
            "file_and_flags", "error", "invalid_request", small(statement="True"), args=["--function", "inc"]
        ),
        Case("bad_argument", "error", "invalid_request", small(statement="True"), args=["--timeout", "nope"]),
        Case(
            "duplicate_module",
            "error",
            "invalid_request",
            {**proof("ok", "inc_ok"), "proof": "Small.lean"},
            {"Small.ll": SMALL_LL, "Small.lean": PROOFS["ok"]},
        ),
        Case("missing_input", "error", "input_not_found", small(statement="True")),
        Case(
            "invalid_ir", "error", "ir_invalid", small(statement="True"), {"Small.ll": "define i32 @inc(\n"}
        ),
        Case(
            "ir_fails_verifier",
            "error",
            "ir_invalid",
            small(statement="True"),
            # It parses, and uses %z before defining it, which only LLVM's verifier catches.
            {
                "Small.ll": "define i32 @inc(i32 %x) {\nentry:\n  %y = add i32 %z, 1\n  %z = add i32 %x, 1\n"
                "  ret i32 %y\n}\n"
            },
            check=check_check("translate", "not_run"),
        ),
        Case(
            "missing_function",
            "error",
            "function_not_found",
            {**small(statement="True"), "function": "dec"},
            {"Small.ll": SMALL_LL},
        ),
        Case(
            "c_doesnt_compile",
            "error",
            "compile_failed",
            {"input": {"c": "bad.c"}, "function": "f", "statement": "True"},
            {"bad.c": "int f(void) { return }\n"},
        ),
        # Tools that fail
        Case(
            "tool_missing",
            "error",
            "toolchain_missing",
            small(statement="True"),
            {"Small.ll": SMALL_LL},
            tool="nope",
        ),
        Case(
            "tool_crashes",
            "error",
            "tool_failed",
            small(statement="True"),
            {"Small.ll": SMALL_LL, "tool": CRASHING_TOOL},
            tool="tool",
        ),
        Case(
            "tool_confused",
            "error",
            "tool_failed",
            small(statement="True"),
            {"Small.ll": SMALL_LL, "tool": CONFUSED_TOOL},
            tool="tool",
        ),
    ]


def run_verify(args: list[str]) -> dict[str, Any]:
    # Not irlean.proc.run, which kills the command's process group when it exits: that would kill anything
    # tools/verify.py left running in its own group before check_nothing_left could see it.
    result = subprocess.run([str(VERIFY), *args], capture_output=True, text=True, check=False, cwd=ROOT)
    try:
        answer = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise AssertionError(
            f"not JSON (exit {result.returncode}):\n{result.stdout[:2000]}{result.stderr[:2000]}"
        ) from error
    answer["_exit"] = result.returncode
    return answer


def run_case(case: Case, tool: Path, scratch: Path) -> str | None:
    """Returns what went wrong, or None."""
    directory = scratch / case.name
    directory.mkdir()
    for name, text in case.files.items():
        (directory / name).parent.mkdir(parents=True, exist_ok=True)
        (directory / name).write_text(text)
    if (directory / "tool").exists():
        (directory / "tool").chmod(0o755)
    request = directory / "request.json"
    request.write_text(case.raw if case.raw is not None else json.dumps(case.request, ensure_ascii=False))
    chosen = tool if case.tool is None else directory / case.tool
    try:
        result = run_verify(
            ["check", str(request), "--tool", str(chosen), "--work-dir", str(directory / "work"), *case.args]
        )
    except AssertionError as error:
        return str(error)
    got = f"{result['status']}/{result['reason']}"
    if got != f"{case.status}/{case.reason}":
        return f"got {got}, wanted {case.status}/{case.reason}: {result['detail'][:1500]}"
    exit_codes = {"proved": 0, "error": 1, "counterexample": 2, "unsupported": 3, "timeout": 4}
    if result["_exit"] != exit_codes[case.status]:
        return f"exit code {result['_exit']} for {case.status}"
    return case.check(result, directory) if case.check else None


def load_verify() -> Any:
    spec = importlib.util.spec_from_file_location("verify_tool", VERIFY)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def contract_checks() -> list[str]:
    """The decision itself, for each required check that didn't pass, and the contract's own consistency."""
    v = load_verify()
    failures = []
    if set(v.EXIT_CODES) != set(v.STATUSES) or len(set(v.EXIT_CODES.values())) != len(v.EXIT_CODES):
        failures.append("exit codes don't match statuses one to one")
    for reason, (status, _) in v.REASONS.items():
        if status not in v.STATUSES:
            failures.append(f"{reason} has unknown status {status}")
    names = [n for n, _ in v.CHECKS]
    if len(set(names)) != len(names) or set(v.REQUIRED) - set(names) or v.OPTIONAL - set(names):
        failures.append("checks, REQUIRED and OPTIONAL don't agree")
    for status in v.STATUSES:
        if not any(s == status for s, _ in v.REASONS.values()):
            failures.append(f"no reason gives {status}")
    # The doc is the contract people read, so it has to name everything the code can say.
    doc = (ROOT / "docs" / "verify.md").read_text()
    for word in [*v.STATUSES, *v.REASONS, *names, *v.REQUEST_FIELDS]:
        if f"`{word}`" not in doc:
            failures.append(f"docs/verify.md doesn't mention `{word}`")

    def run_with(**results: str) -> Any:
        run = v.Run({"proof": "P.lean", "input": {"ir": "x.ll"}}, Path(), Path(), 0.0, 0.0)
        for name in names:
            run.check(name, "pass")
        for name, value in results.items():
            run.check(name, value)
        run.claim = {"theorem": {"found": True, "name": "t", "axioms": []}, "statement": None}
        # The Lean processes irlean.verdict rests a proof on, and the modules they wrote: this file stands in.
        run.steps = {
            name: v.verdict.Step(name, 0) for name in ("compile_proof", "kernel_replay", "witnesses")
        }
        run.outputs = {name: Path(__file__) for name in ("compile_generated", "compile_proof")}
        return run

    if v.decide(run_with())[0] != "proved":
        failures.append("every check passing isn't proved")
    # Checks that say pass aren't enough: the processes have to have ended as they say, and the modules be
    # there.
    for change in (
        lambda r: r.steps.clear(),
        lambda r: r.steps.update(compile_proof=v.verdict.Step("compile_proof", -11)),
        lambda r: r.steps.update(kernel_replay=v.verdict.Step("kernel_replay", 0, limit="time_limit")),
        lambda r: r.steps.update(kernel_replay=v.verdict.Step("kernel_replay", False)),
        lambda r: r.outputs.update(compile_proof=Path("/nonexistent/P.olean")),
    ):
        run = run_with()
        change(run)
        if v.decide(run)[0] == "proved":
            failures.append("proved, with every check passing, on processes or modules that don't hold it up")
    for name in v.REQUIRED:
        for value in ("fail", "not_run", "skip", "inconclusive"):
            status = v.decide(run_with(**{name: value}))[0]
            if status == "proved":
                failures.append(f"proved with {name} {value}")
            if v.build_result(run_with(**{name: value}))["status"] == "proved":
                failures.append(f"the result says proved with {name} {value}")
    for name in v.OPTIONAL:
        if v.decide(run_with(**{name: "fail"}))[0] == "proved":
            failures.append(f"proved with {name} failed")
    no_proof = run_with()
    no_proof.request = {"input": {"ir": "x.ll"}, "statement": "True"}
    if v.decide(no_proof)[0] == "proved":
        failures.append("proved without a proof")
    witness = run_with(statement="pass")
    witness.witnesses = [{"result": "fails", "assignment": {"x": "1"}}]
    if v.decide(witness)[1] != "evaluation_contradicts_proof":
        failures.append("a passing proof with a failing witness isn't a contradiction")
    # A witness that fails counts only if what evaluated it ended cleanly.
    for ended, status in (
        (v.verdict.Step("witnesses", -11), "error"),
        (v.verdict.Step("witnesses", -9, limit="time_limit"), "timeout"),
        (v.verdict.Step("witnesses", 1, output="error: (deterministic) timeout"), "timeout"),
        (v.verdict.Step("witnesses", 1), "error"),
    ):
        crashed = run_with()
        crashed.request = {"input": {"ir": "x.ll"}, "statement": "True"}
        crashed.witnesses = [{"result": "fails", "assignment": {"x": "1"}}]
        crashed.steps["witnesses"] = ended
        if v.decide(crashed)[0] != status:
            failures.append(
                f"a failing witness whose evaluation {ended} is {v.decide(crashed)}, not {status}"
            )
    tampered = run_with(artifacts_unchanged="fail")
    tampered.witnesses = witness.witnesses
    if v.decide(tampered)[1] != "artifacts_modified":
        failures.append("tampering doesn't come first")
    fake = v.build_result(run_with())
    fake["checks"] = [{**c, "result": "fail"} if c["name"] == "axioms" else c for c in fake["checks"]]
    try:
        v.assert_contract(fake)
        failures.append("assert_contract let a proved result with a failed check through")
    except AssertionError:
        pass
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    parser.add_argument("--only", nargs="*", default=None)
    args = parser.parse_args()
    tool = args.tool.resolve()
    failed = False
    for failure in contract_checks():
        print(f"FAIL  contract: {failure}")
        failed = True
    if not failed:
        print("ok    contract: no required check can be missing from a proved result")
    capabilities = run_verify(["capabilities"])
    if capabilities.get("schema") != schemas.VERIFY or capabilities["_exit"] != 0:
        print("FAIL  capabilities")
        failed = True

    selected = [c for c in cases() if not args.only or c.name in args.only]
    # Each case runs one Lean process at a time.
    jobs = max(1, min(int(os.environ.get("LEAN_JOBS", "4")), 4))
    with tempfile.TemporaryDirectory() as temporary, ThreadPoolExecutor(jobs) as pool:
        scratch = Path(temporary)
        results = list(pool.map(lambda c: (c, run_case(c, tool, scratch)), selected))
    for case, failure in results:
        if failure:
            print(f"FAIL  {case.name}: {textwrap.shorten(failure, 3000)}")
            failed = True
        else:
            print(f"ok    {case.name}: {case.status}/{case.reason}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
