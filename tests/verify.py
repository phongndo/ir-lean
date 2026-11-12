#!/usr/bin/env python3
"""Checks tools/verify.py's contract: each status and reason comes back exactly when it should, and nothing
that isn't proved says it is.

Each case writes its inputs to a directory of its own and runs `tools/verify.py check` on them as an agent
would, then checks the status, the reason, the exit code and what else the case is about. Many of them are
proofs that cheat: `sorry`, an axiom, `native_decide`, a theorem about a look-alike function, one the kernel
never checked, one that rewrites what it's checked against, and one that prints an answer of its own. None may
come back proved, and one that fails to compile, with an error forging a counterexample, may not come back
refuted either. A first group
checks the decision in tools/verify.py directly, for every required check that could be missing. And for each
thing its grants require, a case plants a fault on the public path that takes the grant away, by a program it
runs, first on PATH, or its request or files: BREAKERS, docs/verdicts.md's invariant 3.

usage: tests/verify.py path/to/ir-lean [--only NAME ...]
"""

import argparse
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from unittest import mock

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


def lean_string(text: str) -> str:
    """A Lean string literal: JSON's escapes are Lean's."""
    return json.dumps(text, ensure_ascii=False)


# A witness that, elaborated where witnesses are evaluated, prints that witness 0 makes the statement false,
# with the run's nonce, and exits before the real answer.
FORGED_WITNESS = (
    "(by (run_tac (do "
    'let p := (← IO.getEnv "IRLEAN_VERIFY_CONFIG").getD ""; '
    "let j := (Lean.Json.parse (← IO.FS.readFile p)).toOption.getD Lean.Json.null; "
    'let n := (j.getObjValAs? String "nonce").toOption.getD ""; '
    'let h ← IO.FS.Handle.mk "/dev/stdout" IO.FS.Mode.append; '
    'h.putStrLn ("IRLEAN_VERIFY " ++ n ++ '
    + lean_string(' {"kind":"witness_start","count":1,"source":"statement"}')
    + '); h.putStrLn ("IRLEAN_VERIFY " ++ n ++ '
    + lean_string(' {"kind":"witness","index":0,"result":"fails","instance":"forged"}')
    + "); h.flush; (IO.Process.exit 0 : IO Unit))); exact 0#32)"
)

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
    # True of every `inc`: the left side only mentions it.
    "mentions_only": HEADER + "theorem inc_const (x : BitVec 32) :\n"
    "    (fun _ => Outcome.ok (some 0#32)) (inc (some x)) = Outcome.ok (some 0#32) := rfl\n",
    # Fails to compile with an error that reads like bv_decide's, whose value is code that forges an answer
    # where the counterexample would be checked.
    "forged_counterexample": "import Small\nimport Lean\nopen IRLean Small Lean Elab Command\n\n"
    "run_cmd logError " + lean_string("found a counterexample\n#0 = " + FORGED_WITNESS) + "\n\n" + INC_OK,
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
# The real program, in a shim.
REAL = '"{real}" "$@"'


def shim(match: str, then: str) -> str:
    """A program put first on PATH in place of one tools/verify.py runs: the real one, `{real}`, but when its
    arguments name `match`, `then` instead. It plants one fault on the public path."""
    return f'#!/bin/sh\ncase "$*" in\n  *{match}*) {then} ;;\n  *) exec {REAL} ;;\nesac\n'


def lean(match: str, then: str) -> dict[str, str]:
    """A `lean` that runs, and when its arguments name `match`, does `then` after."""
    return {"lean": shim(match, f"{REAL}; {then}")}


# A witness answer that fails, as tools/verify_check.lean prints one.
WITNESS_FAILS = '{{"kind":"witness","index":{index},"result":"fails","instance":"x"}}'
# An answer as tools/verify_check.lean prints one, but with a nonce that isn't the run's.
FORGED_ANSWER = """echo 'IRLEAN_VERIFY 00 {"kind":"witness","index":0,"result":"fails","instance":"x"}'"""


def own_answer(answer: str) -> str:
    """Shell that prints `answer` as tools/verify_check.lean does, with the run's own nonce, read from the
    configuration tools/verify.py gave it: an answer the nonce can't tell from a real one."""
    read = """n=$(sed -n 's/.*"nonce": "\\([0-9a-f]*\\)".*/\\1/p' "$IRLEAN_VERIFY_CONFIG")"""
    return f"{read}; printf 'IRLEAN_VERIFY %s %s\\n' \"$n\" '{answer}'"


def rewritten(match: str, sed: str) -> dict[str, str]:
    """A `lean` whose output, when its arguments name `match`, goes through `sed`: a checker answering
    outside its contract."""
    return {"lean": shim(match, f"{REAL} | sed '{sed}'")}


# leanchecker, which then deletes the proof's module.
OLEAN_GONE = shim("Small", f'{REAL} && rm "${{LEAN_PATH%%:*}}/Proof.olean"')


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
    # Programs put first on PATH, by name, each a script naming the real one `{real}`. One named ir-lean is
    # the tool.
    shims: dict[str, str] = field(default_factory=dict)


def planted(
    name: str,
    status: str,
    reason: str,
    shims: dict[str, str] | None = None,
    files: Any = None,
    **request: Any,
) -> Case:
    """proved_ir, with one fault planted: in a program it runs, by `shims`, its `files`, `tool` or request."""
    tool = request.pop("tool", None)
    files = files_for("ok") if files is None else files
    return Case(name, status, reason, proof("ok", "inc_ok", **request), files, tool=tool, shims=shims or {})


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
    ok = files_for("ok")
    refute = (small(statement=INC_OR, witnesses=[{"x": "1#32"}]), {"Small.ll": SMALL_LL})
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
        Case(
            "proved_mentions_only",
            "proved",
            "kernel_checked",
            proof("mentions_only", "inc_const"),
            files_for("mentions_only"),
            check=lambda r, _: expect(
                r["claim"]["shape"] == "other"
                and any(a["id"] == "statement.shape" for a in r["assumptions"]),
                f"shape {r['claim']['shape']}, for a conclusion that only mentions inc",
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
        # A witness that would run code while it elaborates is refused, and one that doesn't is still decided.
        Case(
            "counterexample_witness_runs_no_code",
            "counterexample",
            "witness_falsifies",
            small(
                statement="∀ x : IRLean.Val 32, Small.inc x = IRLean.Outcome.ok x",
                witnesses=[
                    {"x": "(by exact some 1#32)"},
                    {"x": "(show IRLean.Val 32 by exact some 1#32)"},
                    {"x": "(by_elab return Lean.toExpr (some 1#32 : Option (BitVec 32)))"},
                    {"x": "some 5#32"},
                ],
            ),
            {"Small.ll": SMALL_LL},
            check=check_all(
                check_counterexample({"x": "some 5#32"}, "request"),
                lambda r, _: expect(
                    all(
                        w["result"] == "unsupported" and "tactic block" in w.get("error", "")
                        for w in r["witnesses"][:3]
                    ),
                    str(r["witnesses"][:3]),
                ),
            ),
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
        # The proof's error reads like bv_decide's, and its value is code. Only literals are taken from one.
        Case(
            "proof_failed_forged_counterexample",
            "error",
            "proof_failed",
            proof("forged_counterexample", "inc_ok", statement=INC_STATEMENT, witnesses=[{"x": "5#32"}]),
            files_for("forged_counterexample"),
            check=check_all(
                check_check("witnesses", "pass"),
                lambda r, _: expect(
                    r["counterexample"] is None and all(w["source"] == "request" for w in r["witnesses"]),
                    f"took {r['witnesses']}",
                ),
            ),
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
            "statement_runs_tactic",
            "error",
            "statement_invalid",
            small(
                statement="∀ x : BitVec 32, "
                "Small.inc (some x) = IRLean.Outcome.ok (some (x + (by exact 1#32)))",
                witnesses=[{"x": "1#32"}],
            ),
            {"Small.ll": SMALL_LL},
            check=lambda r, _: expect("tactic block" in r["detail"], r["detail"]),
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
        # Faults planted in proved_ir, and in counterexample_statement, each taking the grant away: BREAKERS.
        planted("proof_bad_request", "error", "invalid_request", limits={"timeout_seconds": 0}),
        planted("proof_tool_missing", "error", "toolchain_missing", tool="nope"),
        planted("proof_input_missing", "error", "input_not_found", files={"Small.ll": SMALL_LL}),
        planted("proof_opt_fails", "error", "ir_invalid", {"opt": "#!/bin/sh\nexit 1\n"}),
        planted(
            "proof_tool_crashes", "error", "tool_failed", files={**ok, "tool": CRASHING_TOOL}, tool="tool"
        ),
        planted("proof_generate_fails", "error", "tool_failed", {"ir-lean": shim("--namespace", "exit 1")}),
        planted(
            "proof_generated_fails", "error", "generated_module_failed", lean("lean/Small.lean", "exit 1")
        ),
        planted("proof_lean_fails", "error", "proof_failed", lean("Proof.lean", "exit 1")),
        # The process that read the claim and applied the axiom policy answers, then doesn't end cleanly.
        planted("proof_check_fails", "error", "tool_failed", lean("check/Check.lean", "exit 1")),
        planted("proof_check_killed", "timeout", "memory_limit", lean("check/Check.lean", "kill -9 $$")),
        planted(
            "proof_check_silent", "error", "internal_error", {"lean": shim("check/Check.lean", "exit 0")}
        ),
        planted(
            "proof_leanchecker_fails", "error", "kernel_replay_failed", {"leanchecker": "#!/bin/sh\nexit 1\n"}
        ),
        # The proof's module, gone after leanchecker replayed it.
        planted("proof_olean_deleted", "error", "internal_error", {"leanchecker": OLEAN_GONE}),
        Case(
            "witness_eval_fails", "error", "tool_failed", *refute, shims=lean("check/Witness.lean", "exit 1")
        ),
        # A real answer that the witness fails, and one more without the run's nonce.
        Case(
            "witness_answer_without_nonce",
            "error",
            "tool_failed",
            *refute,
            shims=lean("check/Witness.lean", FORGED_ANSWER),
        ),
        # Review 1 of #123. A checker's answers are read only once they're its contract's: a witness that
        # holds, answered again as failing with the run's nonce, isn't a counterexample; nor is an answer for
        # a witness never asked.
        Case(
            "witness_answered_twice",
            "error",
            "internal_error",
            small(statement=INC_STATEMENT, witnesses=[{"x": "1#32"}]),
            {"Small.ll": SMALL_LL},
            shims=lean("check/Witness.lean", own_answer(WITNESS_FAILS.format(index=0))),
        ),
        Case(
            "witness_answer_not_asked",
            "error",
            "internal_error",
            small(statement=INC_STATEMENT, witnesses=[{"x": "1#32"}]),
            {"Small.ll": SMALL_LL},
            shims=lean("check/Witness.lean", own_answer(WITNESS_FAILS.format(index=7))),
        ),
        # The axiom policy's `ok: false` as the string "false", and a statement's `match` left out: neither
        # reads as a pass.
        Case(
            "policy_ok_not_a_bool",
            "error",
            "internal_error",
            proof("axiom", "inc_two"),
            files_for("axiom"),
            shims=rewritten("check/Check.lean", 's/"ok":false/"ok":"false"/'),
        ),
        Case(
            "statement_match_missing",
            "error",
            "internal_error",
            proof("ok", "inc_ok", statement=INC_OR),
            files_for("ok"),
            shims=rewritten("check/Check.lean", 's/"match":"mismatch",//'),
        ),
        # Killed, as a memory cap or the OOM killer does, is a limit wherever it happens, through
        # irlean.verdict.limit_of.
        planted(
            "proof_leanchecker_killed", "timeout", "memory_limit", {"leanchecker": "#!/bin/sh\nkill -9 $$\n"}
        ),
        planted("proof_lean_killed", "timeout", "memory_limit", lean("Proof.lean", "kill -9 $$")),
        planted("generated_lean_killed", "timeout", "memory_limit", lean("lean/Small.lean", "kill -9 $$")),
    ]


# docs/verdicts.md's invariant 3: for each thing tools/verify.py's grants require, by grant, kind and name,
# the cases above that plant a fault in it on the public path, each of which takes the grant away. Deleting a
# requirement from GRANTS and its line here together still fails tests/verdict_test.py's snapshot.
BREAKERS: dict[tuple[str, str, str], list[str]] = {
    ("verify.proved", "step", "lean"): ["proof_lean_fails"],
    ("verify.proved", "step", "axioms"): ["proof_check_fails", "proof_check_killed"],
    ("verify.proved", "step", "replay"): ["proof_leanchecker_fails"],
    ("verify.proved", "files", "files"): ["proof_olean_deleted"],
    ("verify.proved", "check", "request"): ["proof_bad_request"],
    ("verify.proved", "check", "toolchain"): ["proof_tool_missing"],
    ("verify.proved", "check", "inputs"): ["proof_input_missing"],
    ("verify.proved", "check", "ir_valid"): ["proof_opt_fails"],
    ("verify.proved", "check", "translate"): ["proof_tool_crashes"],
    ("verify.proved", "check", "generate"): ["proof_generate_fails"],
    ("verify.proved", "check", "compile_generated"): ["proof_generated_fails"],
    ("verify.proved", "check", "compile_proof"): ["proof_lean_fails", "proof_failed_witnesses_hold"],
    ("verify.proved", "check", "claim"): ["proof_check_silent"],
    ("verify.proved", "check", "theorem"): ["theorem_not_found", "not_a_theorem"],
    ("verify.proved", "check", "mentions_target"): ["unrelated_theorem", "lookalike"],
    ("verify.proved", "check", "axioms"): ["sorry", "axiom", "native_decide"],
    ("verify.proved", "check", "kernel_replay"): ["kernel_skipped", "proof_leanchecker_fails"],
    ("verify.proved", "check", "artifacts_unchanged"): ["tamper", "support_tamper"],
    ("verify.proved", "if_asked", "statement"): ["statement_mismatch", "pinned_names_proof_constant"],
    ("verify.counterexample", "step", "witnesses"): ["witness_eval_fails"],
    ("verify.counterexample", "check", "falsified"): ["statement_only_not_proved"],
    ("verify.counterexample", "check", "nonce"): ["witness_answer_without_nonce"],
}
# Those no fault on the public path reaches, and why.
UNREACHABLE = {
    (
        "verify.counterexample",
        "check",
        "literal",
    ): "candidates_from drops an assignment bv_decide printed with "
    "a value that isn't a literal, so a witness that fails is the request's own or all literals. "
    "proof_failed_forged_counterexample plants one, and no witness is taken from it",
}


def requirements(grants: Any, name: str) -> set[tuple[str, str, str]]:
    """What GRANTS[name] requires, by grant, kind and name."""
    grant = grants[name]
    return {
        *((name, "step", s) for s in grant.steps),
        *((name, "check", c) for c in grant.checks),
        *((name, "if_asked", c) for c in getattr(grant, "if_asked", ())),
        *([(name, "files", "files")] if grant.files else []),
    }


def run_verify(args: list[str], env: dict[str, str] | None = None) -> dict[str, Any]:
    # Not irlean.proc.run, which kills the command's process group when it exits: that would kill anything
    # tools/verify.py left running in its own group before check_nothing_left could see it.
    result = subprocess.run(
        [str(VERIFY), *args], capture_output=True, text=True, check=False, cwd=ROOT, env=env
    )
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
    env = None
    if case.shims:
        shims = directory / "bin"
        shims.mkdir()
        for program, script in case.shims.items():
            real = tool if program == "ir-lean" else shutil.which(program)
            (shims / program).write_text(script.replace("{real}", str(real)))
            (shims / program).chmod(0o755)
        env = {**os.environ, "PATH": f"{shims}{os.pathsep}{os.environ['PATH']}"}
        chosen = shims / "ir-lean" if "ir-lean" in case.shims else chosen
    try:
        result = run_verify(
            ["check", str(request), "--tool", str(chosen), "--work-dir", str(directory / "work"), *case.args],
            env,
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
            name: v.verdict.Step(name, 0)
            for name in ("compile_proof", "claim:check", "kernel_replay", "witnesses")
        }
        run.outputs = {name: Path(__file__) for name in ("compile_generated", "compile_proof")}
        run.forged = {"check": 0, "witness": 0}
        return run

    if v.decide(run_with())[0] != "proved":
        failures.append("every check passing isn't proved")
    # Checks that say pass aren't enough: the processes have to have ended as they say, and the modules be
    # there.
    for change in (
        lambda r: r.steps.clear(),
        lambda r: r.steps.update(compile_proof=v.verdict.Step("compile_proof", -11)),
        lambda r: r.steps.update(kernel_replay=v.verdict.Step("kernel_replay", 0, limit="time_limit")),
        lambda r: r.outputs.update(compile_proof=Path("/nonexistent/P.olean")),
    ):
        run = run_with()
        change(run)
        if v.decide(run)[0] == "proved":
            failures.append("proved, with every check passing, on processes or modules that don't hold it up")
    # A step whose exit isn't an integer can't even be built, so it can't hold a proof up.
    try:
        v.verdict.Step("kernel_replay", False)
        failures.append("a step whose exit is False was built")
    except TypeError:
        pass
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
    witness.witnesses = [{"source": "request", "result": "fails", "assignment": {"x": "1"}}]
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
        crashed.witnesses = witness.witnesses
        crashed.steps["witnesses"] = ended
        if v.decide(crashed)[0] != status:
            failures.append(
                f"a failing witness whose evaluation {ended} is {v.decide(crashed)}, not {status}"
            )
    # A pinned statement is required, when the request pins one, as the grant's `if_asked` says.
    pinned = run_with(statement="skip")
    pinned.request = {**pinned.request, "statement": "True"}
    if v.decide(pinned)[0] == "proved":
        failures.append("proved with a pinned statement that wasn't checked")
    # The process that applied the axiom policy has to end cleanly, as the others do.
    for ended, said in (
        (v.verdict.Step("claim:check", 1), ("error", "tool_failed")),
        (v.verdict.Step("claim:check", 137), ("timeout", "memory_limit")),
    ):
        run = run_with()
        run.steps["claim:check"] = ended
        if v.decide(run)[:2] != said:
            failures.append(f"with the axiom policy's process {ended}, {v.decide(run)[:2]}, not {said}")

    # A witness answer, with another in its process's output that lacks the run's nonce, or one from a proof
    # that isn't a literal, isn't a counterexample.
    def refutation() -> Any:
        run = run_with(compile_proof="skip")
        run.request = {"input": {"ir": "x.ll"}, "statement": "True"}
        del run.steps["compile_proof"]
        run.witnesses = [dict(w) for w in witness.witnesses]
        return run

    refuted = refutation()
    if v.decide(refuted)[:2] != ("counterexample", "witness_falsifies"):
        failures.append(f"a clean refutation is {v.decide(refuted)[:2]}")
    for change in (
        lambda r: r.forged.update(witness=1),
        lambda r: r.witnesses[0].update(source="bv_decide", assignment={"x": "(by exact 1)"}),
    ):
        run = refutation()
        change(run)
        if v.decide(run)[0] == "counterexample":
            failures.append(f"a counterexample with {run.forged}, {run.witnesses}")
    # IRLEAN_DENY_ALL takes either grant away.
    with mock.patch.dict(os.environ, {v.verdict.DENY_ALL: "1"}):
        for run in (run_with(), refuted):
            if v.decide(run)[:2] != ("error", "denied"):
                failures.append(f"under {v.verdict.DENY_ALL}, {v.decide(run)[:2]}")
    # Each requirement of tools/verify.py's grants has a fault planted on the public path, or says why not.
    wanted = requirements(v.verdict.GRANTS, "verify.proved") | requirements(
        v.verdict.GRANTS, "verify.counterexample"
    )
    planted = set(BREAKERS) | set(UNREACHABLE)
    if wanted != planted or set(BREAKERS) & set(UNREACHABLE):
        failures.append(
            f"no fault planted for {sorted(wanted - planted)}; not required: {sorted(planted - wanted)}"
        )
    named = {c.name: c for c in cases()}
    for (grant, _, _), breakers in BREAKERS.items():
        for name in breakers:
            if name not in named or named[name].status == v.verdict.GRANTS[grant].word:
                failures.append(f"{name} doesn't take {grant} away")
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
