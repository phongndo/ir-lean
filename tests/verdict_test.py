#!/usr/bin/env python3
"""Checks tools/irlean/verdict.py, the one place Python decides a verdict, without Lean, in a few seconds.
docs/verdicts.md is the design, and these are its invariants 3 to 6:

- What each grant requires is fixed: GRANTS is tests/verdict/grants.json, byte for byte, so a change to it is
  one a reviewer sees.
- Bounded, for each grant: every value of each kind of evidence with the rest clean, each requirement left
  out, every pair at one value of each failure category, and named interactions, such as Lean killed after
  the error a check expects, each giving the outcome docs/verdicts.md's table says.
- One lint: no function in tools/, tests/ or bench/ returns, assigns, or sets as a status or verdict a
  grant's word, or makes a Decision, but those on a list that can only shrink, each with why; and no shell
  test runs Lean and prints `ok` or exits 0 itself, but those on another.
- The old form, `decide` asked for a claim, is counted where it's called, and the count can only fall.

And the old form, until it goes:

- Exhaustively, over every combination of a set of ways each process can end, each file can be there or not,
  and each check can pass, fail or not run, that `decide` grants a claim only when everything it rests on is
  clean, calls it `unknown` only when a limit could explain it, and never grants a different claim.
- Adversarially, that breaking any one or two things in evidence it grants, in each way it can break, always
  takes the grant away; and that a value that only looks right, such as `False` for an exit, can't be made.
- That the three verdicts Python got wrong before can't come back: a crashed native check counting as catching
  a wrong rewrite, and a slice that didn't compile counting as a refutation, both in #57, and a cached result
  whose certificate is gone counting as certified, in #51.
- That each tool and test that decides one of these verdicts asks `decide`.

docs/trust.md#where-python-decides-a-verdict.

usage: tests/verdict_test.py
"""

import ast
import collections
import dataclasses
import importlib.util
import itertools
import json
import os
import re
import sys
import unittest
from pathlib import Path
from typing import Any, ClassVar
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc, schemas  # noqa: E402
from irlean.verdict import (  # noqa: E402
    CLAIMS,
    DENY_ALL,
    GRANTS,
    UNCHANGED,
    UPSTREAM,
    Cases,
    Decision,
    Evidence,
    Grant,
    Plan,
    Step,
    Verdict,
    decide,
    limit_of,
)

LIMIT_TEXT = "x.lean:3:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)"
ERROR_TEXT = "x.lean:3:2: error: type mismatch"

# Every way a process can end, by name: what it is, its category in docs/verdicts.md's outcome table, and the
# limit that stopped it, if one did. A Lean limit is read from the first error of a process that didn't exit
# 0.
STEPS: dict[str, tuple[Step | None, str, str | None]] = {
    "absent": (None, "absent", None),
    "clean": (Step("p", 0), "clean", None),
    "clean_with_limit_text": (Step("p", 0, output=LIMIT_TEXT), "clean", None),
    "never_ended": (Step("p", None), "absent", None),
    "failed": (Step("p", 1, output=ERROR_TEXT), "unclean", None),
    "failed_quietly": (Step("p", 1), "unclean", None),
    "failed_at_a_lean_limit": (Step("p", 1, output=LIMIT_TEXT), "limit", "heartbeat_limit"),
    "exit_2": (Step("p", 2), "unclean", None),
    "exit_3": (Step("p", 3, output="differs"), "unclean", None),
    "time_limit": (Step("p", -9, limit="time_limit"), "limit", "time_limit"),
    "cap": (Step("p", -9, limit="resource_limit"), "limit", "resource_limit"),
    "zero_but_stopped": (Step("p", 0, limit="time_limit"), "limit", "time_limit"),
    "sigkill": (Step("p", -9), "limit", "killed"),
    "sigkill_from_a_shell": (Step("p", 137), "limit", "killed"),
    "timeout_124": (Step("p", 124), "limit", "time_limit"),
    "segfault": (Step("p", -11), "crash", None),
    "segfault_from_a_shell": (Step("p", 139), "crash", None),
    "abort": (Step("p", -6), "crash", None),
}
FILES: dict[str, Any] = {
    "none": {},
    "there": {"a": True},
    "gone": {"a": True, "b": False},
}
CHECKS: dict[str, Any] = {
    "none": {},
    "passed": {"c": True},
    "failed": {"c": False},
    "not_run": {"c": None},
}
FLAGS: dict[str, Any] = {"absent": None, "true": True, "false": False}


def clean(step: Step | None) -> bool:
    return step is not None and STEPS[name_of(step)][1] == "clean"


def limited(step: Step | None) -> bool:
    return step is not None and STEPS[name_of(step)][1] == "limit"


def name_of(step: Step) -> str:
    # By identity, as two steps that end alike are equal.
    return next(n for n, (s, _, _) in STEPS.items() if s is step)


def same_code(a: Any, b: int) -> bool:
    return type(a) is int and a == b


def good_record(claim: Verdict) -> tuple[Step, dict[str, Any]]:
    schema, status, code = UPSTREAM[claim][0]
    return Step("upstream", code), {"schema": schema, "status": status, "exit_code": code}


class Exhaustive(unittest.TestCase):
    """Every combination of a set of ways each part of the evidence can be."""

    def check(self, claim: Verdict, e: Evidence, granted_when: bool, unknown_when: bool) -> Decision:
        d = decide(claim, e)
        self.assertIn(d.verdict, (claim, Verdict.UNKNOWN, Verdict.ERROR), (claim, e, d))
        self.assertEqual(d.granted, granted_when, (claim, e, d))
        self.assertEqual(d.verdict is Verdict.UNKNOWN, unknown_when, (claim, e, d))
        return d

    def test_a_module(self) -> None:
        """proved, certified and refuted on a compiled, replayed and audited module."""
        axioms_variants: list[Any] = [*(s for s, _, _ in STEPS.values()), *FLAGS.values()]
        count = 0
        for claim in (Verdict.PROVED, Verdict.CERTIFIED, Verdict.REFUTED):
            for lean, replay, axioms, files, checks in itertools.product(
                [s for s, _, _ in STEPS.values()],
                [s for s, _, _ in STEPS.values()],
                axioms_variants,
                FILES.values(),
                CHECKS.values(),
            ):
                e = Evidence(lean=lean, replay=replay, axioms=axioms, files=files, checks=checks)
                axioms_step = axioms if isinstance(axioms, Step) else None
                any_limit = limited(lean) or limited(replay) or limited(axioms_step)
                axioms_ok = clean(axioms_step) if axioms_step else axioms is True
                files_ok = all(v is True for v in files.values()) and bool(
                    claim is not Verdict.CERTIFIED or files
                )
                checks_ok = all(v is True for v in checks.values())
                granted = (
                    not any_limit and clean(lean) and clean(replay) and axioms_ok and files_ok and checks_ok
                )
                self.check(claim, e, granted, any_limit)
                count += 1
        self.assertGreater(count, 100000)

    def test_the_other_evidence(self) -> None:
        """certified from a stored verdict, and refuted by the kernel or compiled code, which counts only if
        the process that answered ended cleanly, with every file and check."""
        for claim in (Verdict.PROVED, Verdict.CERTIFIED, Verdict.REFUTED):
            for kernel, evaluated, cached, (lean, _, _), files, checks in itertools.product(
                FLAGS.values(),
                FLAGS.values(),
                (True, False),
                STEPS.values(),
                FILES.values(),
                CHECKS.values(),
            ):
                lean_clean, lean_limit = clean(lean), limited(lean)
                e = Evidence(
                    kernel=kernel, evaluated=evaluated, cached=cached, lean=lean, files=files, checks=checks
                )
                files_ok = all(v is True for v in files.values()) and bool(
                    claim is not Verdict.CERTIFIED or files
                )
                checks_ok = all(v is True for v in checks.values())
                by = {
                    Verdict.PROVED: False,
                    Verdict.CERTIFIED: cached is True,
                    Verdict.REFUTED: (kernel is True or evaluated is True) and lean_clean,
                }[claim]
                self.check(claim, e, not lean_limit and files_ok and checks_ok and by, lean_limit)

    def test_a_checkers_record(self) -> None:
        for claim in (Verdict.PROVED, Verdict.CERTIFIED, Verdict.REFUTED):
            for schema, status, code in [(s, st, c) for rows in UPSTREAM.values() for s, st, c in rows] + [
                (schemas.VERIFY, "error", 1),
                ("ir-lean.verify/2", "proved", 0),
            ]:
                for exit_code in (code, code + 1, False, True, None, str(code)):
                    for step, _, _ in STEPS.values():
                        if step is None:
                            continue
                        record = {"schema": schema, "status": status, "exit_code": exit_code}
                        e = Evidence(
                            upstream=(dataclasses.replace(step, name="upstream"), record), files={"a": True}
                        )
                        grants = (schema, status, code) in UPSTREAM[claim]
                        ended = same_code(step.exit, code) and step.limit is None
                        exact = same_code(exit_code, code)
                        self.check(claim, e, grants and ended and exact, limited(step))
            self.assertFalse(
                decide(claim, Evidence(upstream=(Step("u", 0), ["proved"]), files={"a": True})).granted
            )

    def test_caught(self) -> None:
        findings = [None, "", "   ", ERROR_TEXT, LIMIT_TEXT, "differs"]
        for step, found_exit, finding, checks in itertools.product(
            [s for s, _, _ in STEPS.values()], (1, 3, 0), findings, CHECKS.values()
        ):
            e = Evidence(step=step, found_exit=found_exit, finding=finding, checks=checks)
            any_limit = limited(step)
            ended = step is not None and same_code(step.exit, found_exit) and not step.limit
            checks_ok = all(v is True for v in checks.values())
            own = bool((finding or "").strip()) and finding != LIMIT_TEXT
            limit_found = ended and checks_ok and finding == LIMIT_TEXT
            self.check(
                Verdict.CAUGHT, e, not any_limit and ended and checks_ok and own, any_limit or limit_found
            )

    def test_only_the_four_are_claims(self) -> None:
        for claim in ("unknown", "error", "granted", "bound", "", None, 1, "PROVED", "verify.prove"):
            with self.assertRaises(ValueError, msg=claim):
                decide(claim, Evidence())  # ty: ignore[invalid-argument-type]
        for claim in CLAIMS:
            self.assertEqual(decide(str(claim), Evidence()).verdict, Verdict.ERROR)


# Evidence each claim is granted on, one for each way it can be.
GRANTED: list[tuple[Verdict, Evidence]] = [
    (claim, Evidence(lean=Step("lean", 0), replay=Step("leanchecker", 0), axioms=axioms, files=files))
    for claim in (Verdict.PROVED, Verdict.CERTIFIED, Verdict.REFUTED)
    for axioms in (True, Step("check_axioms", 0))
    for files in ({"cert.olean": True},)
] + [
    (Verdict.CERTIFIED, Evidence(cached=True, files={"Cert.lean": True}, checks={"artifacts": True})),
    (Verdict.REFUTED, Evidence(kernel=True, lean=Step("harness", 0))),
    (Verdict.REFUTED, Evidence(evaluated=True, lean=Step("claim:witness", 0))),
    *(
        (claim, Evidence(upstream=good_record(claim), files={"a": True}))
        for claim in UPSTREAM
        if UPSTREAM[claim]
    ),
    (Verdict.CAUGHT, Evidence(step=Step("lean", 1, output=ERROR_TEXT), finding="type mismatch")),
    (Verdict.CAUGHT, Evidence(step=Step("native_check", 3), found_exit=3, finding="lane 2 differs")),
    (Verdict.CAUGHT, Evidence(step=Step("alive-tv", 0), found_exit=0, finding="incorrect")),
]


def breakages(e: Evidence) -> list[tuple[str, Evidence]]:
    """Every way to break one thing in `e`, each named."""
    out: list[tuple[str, Evidence]] = []
    bad_steps = {n: s for n, (s, category, _) in STEPS.items() if category != "clean"}
    for field in ("lean", "replay", "axioms", "step"):
        current = getattr(e, field)
        if isinstance(current, Step):
            for n, s in bad_steps.items():
                # For caught, a check that exits with the code that says it found something isn't broken.
                expected = s is not None and same_code(s.exit, e.found_exit) and not limited(s)
                if field == "step" and expected:
                    continue
                replaced = None if s is None else dataclasses.replace(s, name=current.name)
                out.append((f"{field}={n}", dataclasses.replace(e, **{field: replaced})))
    for field in ("axioms", "kernel", "evaluated", "cached"):
        if getattr(e, field) is True:
            for v in (False, None)[: 1 if field == "cached" else 2]:
                out.append((f"{field}={v!r}", dataclasses.replace(e, **{field: v})))
    out.append(("a file False", dataclasses.replace(e, files={**e.files, "extra": False})))
    for v in (False, None):
        out.append((f"a check {v!r}", dataclasses.replace(e, checks={**e.checks, "extra": v})))
    if e.upstream is not None and isinstance(e.upstream[1], dict):
        step, record = e.upstream
        code = record.get("exit_code")
        for key, values in (
            ("schema", [schemas.MEASUREMENT, "ir-lean.verify/2", None]),
            ("status", ["error", "unknown", "refused", None, ""]),
            ("exit_code", [code + 1 if type(code) is int else 99, None, str(code), bool(code)]),
        ):
            for v in values:
                out.append(
                    (f"record {key}={v!r}", dataclasses.replace(e, upstream=(step, {**record, key: v})))
                )
        out.append(
            (
                "record without exit_code",
                dataclasses.replace(
                    e, upstream=(step, {k: v for k, v in record.items() if k != "exit_code"})
                ),
            )
        )
        for n, s in bad_steps.items():
            if s is not None and not (same_code(s.exit, code) and s.limit is None):
                out.append(
                    (
                        f"upstream step {n}",
                        dataclasses.replace(e, upstream=(dataclasses.replace(s, name="u"), record)),
                    )
                )
    if e.step is not None:
        for finding in (None, "", "  \n", LIMIT_TEXT, "SAT solver timed out"):
            out.append((f"finding={finding!r}", dataclasses.replace(e, finding=finding)))
        out.append(("found_exit other", dataclasses.replace(e, found_exit=e.found_exit + 7)))
    return out


class Adversarial(unittest.TestCase):
    def test_each_grant_holds(self) -> None:
        for claim, e in GRANTED:
            d = decide(claim, e)
            self.assertEqual(d.verdict, claim, (claim, e, d))
            self.assertTrue(d.granted)
            self.assertTrue(d.reason)

    def test_breaking_one_thing_takes_the_grant_away(self) -> None:
        count = 0
        for claim, e in GRANTED:
            for name, broken in breakages(e):
                d = decide(claim, broken)
                self.assertFalse(d.granted, f"{claim} still granted with {name}: {d}")
                count += 1
        self.assertGreater(count, 450)

    def test_breaking_two_things_takes_the_grant_away(self) -> None:
        count = 0
        for claim, e in GRANTED:
            for n1, b1 in breakages(e):
                for n2, b2 in breakages(b1):
                    if n2 != n1:
                        d = decide(claim, b2)
                        self.assertFalse(d.granted, f"{claim} still granted with {n1} and {n2}: {d}")
                        count += 1
        self.assertGreater(count, 5000)

    def test_a_limit_is_unknown_and_the_rest_is_error(self) -> None:
        e = Evidence(lean=Step("lean", 0), replay=Step("leanchecker", -9, limit="time_limit"), axioms=True)
        self.assertEqual(decide(Verdict.PROVED, e).verdict, Verdict.UNKNOWN)
        e = Evidence(lean=Step("lean", 1, output=LIMIT_TEXT), replay=Step("leanchecker", 0), axioms=True)
        self.assertEqual(decide(Verdict.PROVED, e).verdict, Verdict.UNKNOWN)
        e = Evidence(lean=Step("lean", -11), replay=Step("leanchecker", 0), axioms=True)
        self.assertEqual(decide(Verdict.PROVED, e).verdict, Verdict.ERROR)
        # A limit anywhere wins over a missing file, as more time might change what's there.
        e = Evidence(lean=Step("lean", -9), replay=Step("leanchecker", 0), axioms=True, files={"a": False})
        self.assertEqual(decide(Verdict.PROVED, e).verdict, Verdict.UNKNOWN)


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class PastBugs(unittest.TestCase):
    """What went wrong before, at the core and where it happened."""

    def test_a_crashed_native_check_catches_nothing(self) -> None:
        # #57: tests/llama.py counted a native check that crashed as catching a wrong rewrite.
        for exit_code in (-11, -6, -9, 137, 1, 2):
            e = Evidence(step=Step("native_check", exit_code), found_exit=3, finding="Segmentation fault")
            self.assertFalse(decide(Verdict.CAUGHT, e).granted, exit_code)
        llama = load("llama_under_test", ROOT / "tests" / "llama.py")
        for code, out, want in (
            (-11, "Segmentation fault", None),
            (1, "error: couldn't build", None),
            (3, "", None),
            (0, "all pairs agree", False),
            (3, "pair 4 differs at lane 2", True),
        ):
            done = proc.Ran([], code, out.encode(), b"", 0.0)
            with mock.patch.object(llama, "run", return_value=done):
                self.assertEqual(llama.native(Path("/s"), Path("/w"))[0], want, (code, out))

    def test_a_slice_that_failed_to_compile_refutes_nothing(self) -> None:
        # #57: a refutation whose slice didn't compile counted.
        for lean in (
            Step("lean", 1, output=ERROR_TEXT),
            Step("lean", -11),
            Step("lean", 1, output=LIMIT_TEXT),
        ):
            e = Evidence(lean=lean, replay=Step("leanchecker", 0), axioms=True, files={"R.olean": True})
            self.assertFalse(decide(Verdict.REFUTED, e).granted, lean)
        e = Evidence(
            lean=Step("lean", 0), replay=Step("leanchecker", 0), axioms=True, files={"R.olean": False}
        )
        self.assertFalse(decide(Verdict.REFUTED, e).granted)
        text = (ROOT / "tests" / "llama.py").read_text()
        differs = text[text.index("    def differs(") : text.index("    def one(")]
        self.assertIn("core.Verdict.REFUTED", differs)
        self.assertIn("r.exit == 0", differs)

    def test_an_answer_from_a_process_that_then_failed_refutes_nothing(self) -> None:
        # Found in review: a kernel answer or a failing witness from a process that then crashed, timed out or
        # failed, or one with no process at all, counted.
        for kernel, evaluated in ((True, None), (None, True)):
            for lean in (None, Step("lean", -11), Step("lean", 1), Step("lean", -9, limit="time_limit")):
                e = Evidence(lean=lean, kernel=kernel, evaluated=evaluated)
                self.assertFalse(decide(Verdict.REFUTED, e).granted, (kernel, evaluated, lean))

    def test_a_cached_result_whose_certificate_is_gone_is_not_certified(self) -> None:
        # #51: the scorer counted cached results whose certificates were gone.
        for files in ({}, {"Cert.lean": False}, {"Cert.lean": True, "manifest.json": False}):
            e = Evidence(cached=True, files=files)
            self.assertFalse(decide(Verdict.CERTIFIED, e).granted, files)
        record = {"schema": schemas.BINDING_VERDICT, "status": "bound", "exit_code": 0}
        e = Evidence(upstream=(Step("binding", 0), record), files={"bundle/Cert.lean": False})
        self.assertFalse(decide(Verdict.CERTIFIED, e).granted)
        e = Evidence(upstream=(Step("binding", 0), record))
        self.assertFalse(decide(Verdict.CERTIFIED, e).granted)


class Routed(unittest.TestCase):
    """Each tool and test that decides one of these verdicts asks the core."""

    SITES: ClassVar[dict[str, list[str]]] = {
        "tools/verify.py": ["Verdict.PROVED", "Verdict.REFUTED"],
        "tools/binding.py": ["Verdict.CERTIFIED"],
        "tools/prooftest/prooftest.py": ["Verdict.REFUTED"],
        "tools/store/store.py": ["Verdict.PROVED"],
        "tools/rules/proved.py": ["Verdict.PROVED"],
        "tools/rules/certify.py": ["Verdict.CERTIFIED"],
        "tests/llvm.py": ["Verdict.PROVED", "Verdict.CAUGHT"],
        "tests/llama.py": ["Verdict.PROVED", "Verdict.REFUTED", "Verdict.CAUGHT"],
        "tests/superopt.py": ["Verdict.CAUGHT"],
        "tests/passes.py": ["Verdict.CERTIFIED"],
        "tests/verify_negative.py": ["Verdict.CERTIFIED"],
        "tests/cpp_correspondence.py": ["Verdict.PROVED", "Verdict.CAUGHT"],
        "bench/instcombine/stage1.py": ["Verdict.PROVED", "Verdict.CERTIFIED", "Verdict.REFUTED"],
    }

    def test_each_site_asks_the_core(self) -> None:
        for path, claims in self.SITES.items():
            text = (ROOT / path).read_text()
            self.assertRegex(text, r"from irlean import [^\n]*verdict", path)
            for claim in claims:
                self.assertIn(claim, text, path)

    def test_verify_grants_proved_only_through_the_core(self) -> None:
        verify = load("verify_under_test", ROOT / "tools" / "verify.py")
        run = verify.Run({"proof": "P.lean", "witnesses": []}, Path("/w"), Path("/t"), 0, 0)
        for name in verify.REQUIRED:
            run.check(name, "pass")
        for name in verify.OPTIONAL:
            run.check(name, "skip")
        run.claim = {"theorem": {"found": True, "name": "T"}, "statement": None}
        # Every check says pass, but no process was recorded, so nothing rests on the kernel.
        self.assertEqual(verify.decide(run)[:2], ("error", "internal_error"))
        olean = Path(__file__)
        run.outputs = {"compile_generated": olean, "compile_proof": olean}
        run.steps = {"compile_proof": Step("compile_proof", 0), "kernel_replay": Step("kernel_replay", -11)}
        self.assertEqual(verify.decide(run)[:2], ("error", "internal_error"))
        run.steps["kernel_replay"] = Step("kernel_replay", 0)
        self.assertEqual(verify.decide(run)[:2], ("proved", "kernel_checked"))
        run.outputs["compile_proof"] = Path("/nonexistent/P.olean")
        self.assertEqual(verify.decide(run)[:2], ("error", "internal_error"))


# Grants by name: docs/verdicts.md's invariants 3 and 4.

GRANTS_JSON = ROOT / "tests" / "verdict" / "grants.json"
# A check left out of the evidence, rather than given a value.
LEFT_OUT = object()
CHECK_VALUES: dict[str, Any] = {
    "true": True,
    "false": False,
    "not_run": None,
    "left_out": LEFT_OUT,
}
FILE_VALUES: dict[str, dict[str, Any]] = {
    "there": {"out.olean": True},
    "one_gone": {"out.olean": True, "other.olean": False},
    "left_out": {},
}
VALUES = {"step": list(STEPS), "check": list(CHECK_VALUES), "files": list(FILE_VALUES)}
CLEAN = {"step": "clean", "check": "true", "files": "there"}
# One value of each failure category, by kind.
REPRESENTATIVE = {
    "step": {"limit": "time_limit", "crash": "segfault", "absent": "absent", "unclean": "failed"},
    "check": {"absent": "left_out", "unclean": "false"},
    "files": {"absent": "left_out", "unclean": "one_gone"},
}
Values = dict[tuple[str, str], str]


def grants_json() -> str:
    """GRANTS, as tests/verdict/grants.json has it."""
    return json.dumps({n: dataclasses.asdict(g) for n, g in GRANTS.items()}, indent=2, sort_keys=True) + "\n"


def requirements(grant: Grant) -> list[tuple[str, str]]:
    """Each thing `grant` requires, by kind and name, in the order `decide` reads them."""
    return [
        *(("step", r) for r in grant.steps),
        *(("check", c) for c in grant.checks),
        *([("files", "files")] if grant.files else []),
    ]


def clean_values(name: str) -> Values:
    return {r: CLEAN[r[0]] for r in requirements(GRANTS[name])}


def evidence(values: Values) -> Evidence:
    """Evidence with each requirement as `values` says."""
    own: dict[str, Any] = {}
    steps: dict[str, Step] = {}
    checks: dict[str, Any] = {}
    files: dict[str, Any] = {}
    for (kind, name), value in values.items():
        if kind == "step":
            step = STEPS[value][0]
            step = None if step is None else dataclasses.replace(step, name=name)
            if name in ("lean", "replay", "axioms", "step"):
                own[name] = step
            elif step is not None:
                steps[name] = step
        elif kind == "check" and CHECK_VALUES[value] is not LEFT_OUT:
            checks[name] = CHECK_VALUES[value]
        elif kind == "files":
            files = FILE_VALUES[value]
    return Evidence(**own, steps=steps, checks=checks, files=files)


def category(kind: str, value: str) -> tuple[str, str | None]:
    """The outcome table's category of a value, and the limit that stopped it, if one did."""
    if kind == "step":
        return STEPS[value][1], STEPS[value][2]
    clean_or_absent = {"true": "clean", "there": "clean", "not_run": "absent", "left_out": "absent"}
    return clean_or_absent.get(value, "unclean"), None


def expected(values: Values) -> tuple[Verdict, str]:
    """What docs/verdicts.md's outcome table says of `values`, a grant's requirements in its order: the first
    limit, then a crash, then something absent, then the first that isn't clean, the check that files didn't
    change before the rest."""
    found = [(kind, name, *category(kind, value)) for (kind, name), value in values.items()]
    for _, _, cat, limit in found:
        if cat == "limit":
            return Verdict.UNKNOWN, str(limit)
    for want, reason in (("crash", "tool_failed"), ("absent", "internal_error")):
        if any(cat == want for _, _, cat, _ in found):
            return Verdict.ERROR, reason
    unclean = [(kind, name) for kind, name, cat, _ in found if cat == "unclean"]
    if ("check", UNCHANGED) in unclean:
        return Verdict.ERROR, "artifacts_modified"
    if unclean:
        kind, name = unclean[0]
        return Verdict.ERROR, "missing_file" if kind == "files" else name
    return Verdict.GRANTED, "clean"


class Fixed(unittest.TestCase):
    """docs/verdicts.md's invariant 3: what each grant requires is fixed in GRANTS, and a change to it changes
    tests/verdict/grants.json, so it's one a reviewer sees."""

    def test_grants_are_the_snapshot(self) -> None:
        self.assertEqual(
            GRANTS_JSON.read_text(),
            grants_json(),
            "GRANTS changed: what a grant requires goes in tests/verdict/grants.json too, from grants_json()",
        )

    def test_each_grant_is_whole(self) -> None:
        for name, grant in GRANTS.items():
            self.assertIn(grant.schema, schemas.ALL, name)
            self.assertIs(type(grant.exit), int, name)
            for what in (grant.steps, grant.checks, grant.excludes):
                self.assertEqual(len(set(what)), len(what), name)
            for other in grant.excludes:
                # Each excludes the other, so the same evidence is asked for both.
                self.assertIn(name, GRANTS[other].excludes, (name, other))


class Bounded(unittest.TestCase):
    """docs/verdicts.md's invariant 4: for each grant, the outcome table's answer to every value of each kind
    with the rest clean, each requirement left out, and every pair at one value of each failure category."""

    def check(self, name: str, values: Values) -> None:
        d = decide(name, evidence(values))
        want = expected(values)
        self.assertEqual((d.verdict, d.reason), want, (name, values, d))
        self.assertEqual(d.granted, want[0] is Verdict.GRANTED)
        self.assertEqual(d.grant, name if d.granted else "")

    def test_each_value_with_the_rest_clean(self) -> None:
        count = 0
        for name in GRANTS:
            clean = clean_values(name)
            self.check(name, clean)
            for r in clean:
                for value in VALUES[r[0]]:
                    self.check(name, {**clean, r: value})
                    count += 1
        self.assertGreater(count, 100)

    def test_each_requirement_left_out(self) -> None:
        for name in GRANTS:
            clean = clean_values(name)
            for r in clean:
                out = {**clean, r: "absent" if r[0] == "step" else "left_out"}
                d = decide(name, evidence(out))
                self.assertEqual((d.verdict, d.reason), (Verdict.ERROR, "internal_error"), (name, r))

    def test_every_pair(self) -> None:
        count = 0
        for name in GRANTS:
            clean = clean_values(name)
            for a, b in itertools.combinations(clean, 2):
                for va, vb in itertools.product(REPRESENTATIVE[a[0]].values(), REPRESENTATIVE[b[0]].values()):
                    self.check(name, {**clean, a: va, b: vb})
                    count += 1
        self.assertGreater(count, 800)

    def test_a_check_no_grant_lists_is_an_internal_error(self) -> None:
        for name in GRANTS:
            e = evidence(clean_values(name))
            typo = dataclasses.replace(e, checks={**e.checks, "artifact_unchanged": True})
            self.assertEqual(decide(name, typo).reason, "internal_error", name)

    def test_an_axiom_audit_needs_its_process(self) -> None:
        e = evidence(clean_values("verify.proved"))
        for answer in (True, False):
            d = decide("verify.proved", dataclasses.replace(e, axioms=answer))
            self.assertEqual((d.verdict, d.reason), (Verdict.ERROR, "internal_error"))


def proved(**change: Any) -> Evidence:
    """Evidence `verify.proved` is granted on, with `change`."""
    return dataclasses.replace(evidence(clean_values("verify.proved")), **change)


REFUTED_BY: dict[str, Any] = {"witnesses": Step("witnesses", 0)}
REFUTATION: dict[str, Any] = {"falsified": True, "nonce": True, "literal": True}


class Interactions(unittest.TestCase):
    """docs/verdicts.md's invariant 4's named interactions."""

    def test_a_limit_and_an_ordinary_error_in_either_order(self) -> None:
        limit_first = Step("lean", 1, output=f"{LIMIT_TEXT}\n{ERROR_TEXT}")
        error_first = Step("lean", 1, output=f"{ERROR_TEXT}\n{LIMIT_TEXT}")
        self.assertEqual(limit_of(limit_first), "heartbeat_limit")
        self.assertIsNone(limit_of(error_first))
        d = decide("verify.proved", proved(lean=limit_first))
        self.assertEqual((d.verdict, d.reason), (Verdict.UNKNOWN, "heartbeat_limit"))
        d = decide("verify.proved", proved(lean=error_first))
        self.assertEqual((d.verdict, d.reason), (Verdict.ERROR, "lean"))
        # The old form reads its limits the same way.
        old = Evidence(lean=error_first, replay=Step("leanchecker", 0), axioms=True)
        self.assertEqual(decide(Verdict.PROVED, old).verdict, Verdict.ERROR)
        old = dataclasses.replace(old, lean=limit_first)
        self.assertEqual(decide(Verdict.PROVED, old).verdict, Verdict.UNKNOWN)

    def test_lean_stopped_after_the_error_a_check_expects(self) -> None:
        ends = [Step("lean", code, output=ERROR_TEXT) for code in (137, -9, 124)]
        ends += [
            Step("lean", 1, output=f"{ERROR_TEXT}\n{said}")
            for said in (
                "INTERNAL PANIC: out of memory",
                "libc++abi: terminating due to uncaught exception of type lean::memory_exception",
                "Stack overflow detected. Aborting.",
            )
        ]
        for end in ends:
            caught = decide(Verdict.CAUGHT, Evidence(step=end, finding="type mismatch"))
            self.assertEqual(caught.verdict, Verdict.UNKNOWN, end)
            self.assertEqual(decide("verify.proved", proved(lean=end)).verdict, Verdict.UNKNOWN, end)
        self.assertTrue(
            decide(
                Verdict.CAUGHT, Evidence(step=Step("lean", 1, output=ERROR_TEXT), finding="mismatch")
            ).granted
        )

    def test_a_proof_beside_a_refutation(self) -> None:
        e = proved(steps=REFUTED_BY, checks={**proved().checks, **REFUTATION})
        for name in ("verify.proved", "verify.counterexample"):
            d = decide(name, e)
            self.assertEqual((d.verdict, d.reason), (Verdict.ERROR, "contradiction"), name)
        self.assertTrue(decide("verify.proved", proved()).granted)
        self.assertTrue(
            decide("verify.counterexample", Evidence(steps=REFUTED_BY, checks=REFUTATION)).granted
        )
        # A refutation that isn't one takes nothing from the proof.
        for change in ({"falsified": False}, {"nonce": False}, {"literal": None}):
            e = proved(steps=REFUTED_BY, checks={**proved().checks, **REFUTATION, **change})
            self.assertTrue(decide("verify.proved", e).granted, change)
            self.assertFalse(decide("verify.counterexample", e).granted, change)


# A grant over many cases, which no tool asks for until tools/prooftest/prooftest.py moves onto its grants, in
# PR 6: the harness's exits, with a model stop of its own.
TIER = Grant(
    "passed",
    0,
    schemas.PROOFTEST,
    steps=("harness",),
    cases=Cases(holds=(1,), discards=(0, 3), stops=(4,), at_least="min_satisfied"),
)
# Each way a case can end, its category, and the limit that stopped it.
CASE: dict[str, tuple[Step, str, str | None]] = {
    "holds": (Step("", 1), "holds", None),
    "discarded": (Step("", 0), "discard", None),
    "discarded_later": (Step("", 3), "discard", None),
    "stopped_the_model": (Step("", 4), "stop", None),
    "failed": (Step("", 2), "fail", None),
    "time_limit": (Step("", -9, limit="time_limit"), "limit", "time_limit"),
    "killed": (Step("", 137), "limit", "killed"),
    "crashed": (Step("", -11), "crash", None),
    "never_ended": (Step("", None), "absent", None),
}
PLANNED = ("a", "b", "c")


def observed(kinds: tuple[str, ...], how: str) -> list[tuple[str, str]]:
    """Each case observed, by its identity and kind, as `how` says: as planned, one left out, the first
    observed twice, as a retry is, or one not planned."""
    out = list(zip(PLANNED, kinds, strict=True))
    return {
        "as_planned": out,
        "one_left_out": out[:-1],
        "first_twice": [*out, out[0]],
        "one_not_planned": [*out, ("z", "holds")],
    }[how]


def run_over(harness: str, cases: list[tuple[str, str]], at_least: int, whole: bool) -> Evidence:
    return Evidence(
        steps={"harness": dataclasses.replace(s, name="harness")} if (s := STEPS[harness][0]) else {},
        plan=Plan(PLANNED, at_least, whole),
        cases=tuple(dataclasses.replace(CASE[kind][0], name=case) for case, kind in cases),
    )


def expected_of_cases(
    harness: str, cases: list[tuple[str, str]], how: str, at_least: int, whole: bool
) -> tuple[Verdict, str]:
    _, h, h_limit = STEPS[harness]
    kinds = [CASE[kind][1] for _, kind in cases]
    if h == "limit":
        return Verdict.UNKNOWN, str(h_limit)
    for _, kind in cases:
        if CASE[kind][1] == "limit":
            return Verdict.UNKNOWN, str(CASE[kind][2])
    if h == "crash" or "crash" in kinds:
        return Verdict.ERROR, "tool_failed"
    if h == "absent" or "absent" in kinds:
        return Verdict.ERROR, "internal_error"
    if how != "as_planned":
        return Verdict.ERROR, "incomplete"
    if h == "unclean":
        return Verdict.ERROR, "harness"
    if "fail" in kinds:
        return Verdict.ERROR, "case_failed"
    if "stop" in kinds:
        return Verdict.UNKNOWN, "model_stopped"
    if not whole and kinds.count("holds") < at_least:
        return Verdict.UNKNOWN, "too_few_satisfying"
    if not kinds.count("holds"):
        return Verdict.ERROR, "vacuous"
    return Verdict.GRANTED, "exhaustive" if whole else "sampled"


@mock.patch.dict(GRANTS, {"t.passed": TIER})
class ManyCases(unittest.TestCase):
    """A grant over many cases: every three cases, planned, left out, observed twice or not planned, at two
    minimums, sampled and the whole domain, under a harness that ended cleanly, failed or stopped at a
    limit."""

    def test_every_three_cases(self) -> None:
        count = 0
        for harness, kinds, how, at_least, whole in itertools.product(
            ("clean", "failed", "time_limit"),
            itertools.product(CASE, repeat=3),
            ("as_planned", "one_left_out", "first_twice", "one_not_planned"),
            (1, 3),
            (False, True),
        ):
            cases = observed(kinds, how)
            d = decide("t.passed", run_over(harness, cases, at_least, whole))
            want = expected_of_cases(harness, cases, how, at_least, whole)
            self.assertEqual((d.verdict, d.reason), want, (harness, cases, at_least, whole, d))
            count += 1
        self.assertGreater(count, 30000)

    def test_named(self) -> None:
        def reason(harness: str, *kinds: str, at_least: int = 1, whole: bool = False) -> tuple[Verdict, str]:
            cases = list(zip(["a", "b", "c", "a"], kinds, strict=False))
            d = decide("t.passed", run_over(harness, cases, at_least, whole))
            return d.verdict, d.reason

        # A clean retry after a failure, or after a limit.
        self.assertEqual(reason("clean", "failed", "holds", "holds", "holds"), (Verdict.ERROR, "incomplete"))
        self.assertEqual(reason("clean", "killed", "holds", "holds", "holds"), (Verdict.UNKNOWN, "killed"))
        # A model stop beside a failing input: the failure decides.
        self.assertEqual(
            reason("clean", "stopped_the_model", "failed", "holds"), (Verdict.ERROR, "case_failed")
        )
        # A run its own budget stopped: the cases it didn't reach are unknown, not incomplete.
        self.assertEqual(reason("time_limit", "holds"), (Verdict.UNKNOWN, "time_limit"))
        self.assertEqual(reason("clean", "holds", "holds", "holds", at_least=3), (Verdict.GRANTED, "sampled"))

    def test_the_plan(self) -> None:
        holds = (Step("a", 1),)
        harness = {"harness": Step("harness", 0)}
        for plan, want in (
            (None, (Verdict.ERROR, "internal_error")),
            (Plan((), 1), (Verdict.UNKNOWN, "nothing_planned")),
            (Plan(("a",), 0), (Verdict.ERROR, "internal_error")),
            (Plan(("a", "a"), 1), (Verdict.ERROR, "incomplete")),
            (Plan(("a",), 1), (Verdict.GRANTED, "sampled")),
        ):
            d = decide("t.passed", Evidence(steps=harness, plan=plan, cases=holds))
            self.assertEqual((d.verdict, d.reason), want, plan)


# Something made right, and values of each of its fields that only look right, each of which has to raise
# where it's made: in Python, True is an int, "false" is truthy, and a str is a sequence of its letters.
MALFORMED: dict[str, tuple[Any, dict[str, list[Any]]]] = {
    "Step": (Step("p", 0), {"name": [None], "exit": [False, "0", 256], "limit": ["", 1], "output": [b""]}),
    "Plan": (Plan(("a",)), {"cases": ["abc", ["a"]], "at_least": [True, "1", -1], "whole": ["false", 1]}),
    "Cases": (Cases((1,)), {"holds": [[1], (True,)], "discards": [(0.0,)], "stops": ["4"], "at_least": [""]}),
    "Grant": (
        Grant("w", 0, "s"),
        {"word": [""], "exit": [False], "schema": [None], "steps": [["lean"]], "checks": [("c", 1)]}
        | {"files": [1], "excludes": ["x.y"], "cases": [{}]},
    ),
    "Evidence": (
        Evidence(),
        {"lean": [True], "replay": ["ok"], "axioms": [1], "kernel": [1], "evaluated": ["yes"]}
        | {"cached": [None], "upstream": [(True, {}), [Step("u", 0), {}]], "step": [0], "found_exit": [True]}
        | {"finding": [1], "files": [{"a": 1}, {"a": None}], "checks": [{"c": "yes"}, {1: True}]}
        | {"steps": [{"s": None}], "plan": [("a",)], "cases": [[Step("a", 1)]]},
    ),
    "Decision": (
        decide("verify.proved", Evidence()),
        {"verdict": ["proved"], "reason": [1], "detail": [1], "grant": [1]},
    ),
}


class Malformed(unittest.TestCase):
    """Review 1's S1: evidence that isn't what its fields say can't be made, so `decide` never reads a field,
    by truthiness, comparison or arithmetic, that only looks right."""

    def test_each_field_of_each_kind(self) -> None:
        for kind, (made, values) in MALFORMED.items():
            self.assertEqual(set(values), {f.name for f in dataclasses.fields(made)}, kind)
            for name, bad in values.items():
                for value in bad:
                    with self.assertRaises(TypeError, msg=(kind, name, value)):
                        dataclasses.replace(made, **{name: value})

    def test_s1(self) -> None:
        # Three planned, one that holds and two discarded, at a minimum of three: `whole` decides.
        cases = observed(("holds", "discarded", "discarded"), "as_planned")
        with mock.patch.dict(GRANTS, {"t.passed": TIER}):
            for whole, want in ((False, "too_few_satisfying"), (True, "exhaustive")):
                self.assertEqual(decide("t.passed", run_over("clean", cases, 3, whole)).reason, want)
        with self.assertRaises(TypeError):
            run_over("clean", cases, 3, "false")  # ty: ignore[invalid-argument-type]

    def test_a_mapping_changed_after_is_not_read(self) -> None:
        checks: dict[str, Any] = {"c": True}
        e = Evidence(checks=checks)
        checks["c"] = "yes"
        self.assertIs(e.checks["c"], True)


class OneLimitReader(unittest.TestCase):
    """`limit_of` alone says which limit stopped a process, for both forms of `decide`."""

    SAID: ClassVar[list[tuple[Step, str | None]]] = [
        (Step("p", 0, limit="time_limit"), "time_limit"),
        (Step("p", -9), "killed"),
        (Step("p", 137), "killed"),
        (Step("p", 124), "time_limit"),
        (Step("p", 1, output="INTERNAL PANIC: out of memory"), "memory_limit"),
        (
            Step(
                "p",
                -6,
                output="libc++abi: terminating due to uncaught exception of type lean::memory_exception",
            ),
            "memory_limit",
        ),
        (Step("p", 134, output="Stack overflow detected. Aborting."), "stack_limit"),
        (
            Step("p", 1, output="P.lean:1:1: error: resource exhausted (error code: 12, not enough memory)"),
            "memory_limit",
        ),
        (Step("p", 1, output="error: cannot allocate memory"), "memory_limit"),
        (Step("p", 1, output="uncaught exception: (kernel) deep recursion detected"), "stack_limit"),
        (
            Step(
                "p", 1, output="X.lean:2:0: error: tactic failed\n  maximum recursion depth has been reached"
            ),
            "recursion_limit",
        ),
        (Step("p", -11, output=LIMIT_TEXT), "heartbeat_limit"),
        (Step("p", 1, output=f"X.lean:1:0: warning: maximum number of heartbeats\n{ERROR_TEXT}"), None),
        (Step("p", 1, output="solver: SAT solver timed out"), None),
        (Step("p", 0, output=LIMIT_TEXT), None),
        (Step("p", 1, output=ERROR_TEXT), None),
        (Step("p", 2), None),
        (Step("p", -11), None),
        (Step("p", None), None),
    ]

    def test_limit_of(self) -> None:
        for step, want in self.SAID:
            self.assertEqual(limit_of(step), want, step)

    def test_verdict_reads_no_limit_any_other_way(self) -> None:
        text = (ROOT / "tools" / "irlean" / "verdict.py").read_text()
        self.assertNotIn("is_limit", text)
        self.assertNotIn("LIMIT.", text)


class DenyAll(unittest.TestCase):
    """IRLEAN_DENY_ALL takes every grant away, and nothing else."""

    def test_it_takes_every_grant_away(self) -> None:
        granted: list[tuple[Any, Evidence]] = [*GRANTED, *((n, evidence(clean_values(n))) for n in GRANTS)]
        for claim, e in granted:
            self.assertTrue(decide(claim, e).granted, claim)
            for value in ("1", "yes", "true"):
                with mock.patch.dict(os.environ, {DENY_ALL: value}):
                    d = decide(claim, e)
                    self.assertEqual((d.verdict, d.reason), (Verdict.ERROR, "denied"), (claim, value))
            for value in ("", "0"):
                with mock.patch.dict(os.environ, {DENY_ALL: value}):
                    self.assertTrue(decide(claim, e).granted, (claim, value))

    def test_it_takes_nothing_else(self) -> None:
        for claim, e in GRANTED:
            for name, broken in breakages(e):
                plain = decide(claim, broken)
                with mock.patch.dict(os.environ, {DENY_ALL: "1"}):
                    self.assertEqual(decide(claim, broken), plain, name)


# One lint: docs/verdicts.md's invariant 5.

# Words a grant is reported as that GRANTS doesn't have yet, each with the pull request of docs/verdicts.md's
# migration that adds its grant. It can only shrink: a word GRANTS has can't be here too.
PENDING = {
    "bound": "PR 9, tools/binding.py",
    "passed_tier1": "PR 6, tools/prooftest/prooftest.py",
    "exact": "PR 7, tools/store/store.py",
    "instance": "PR 7, tools/store/store.py",
    "admitted": "PR 7, tools/store/store.py",
    "candidate": "PR 7, tools/store/store.py",
    "counted": "PR 10, the peephole scorer",
    "faster": "#117, cut again on PR 1",
    "slower": "#117, cut again on PR 1",
    "win": "#117, cut again on PR 1",
}
# tools/verify_claims.py's verdicts, which it decides itself, on purpose: BIND-03 shares no code with the
# scorer it checks.
VERIFY_CLAIMS = ("replayed", "verified")
GRANTING = {m.name for m in (*CLAIMS, Verdict.GRANTED)}


def words() -> set[str]:
    """Every word a grant is reported as."""
    return {g.word for g in GRANTS.values()} | {str(c) for c in CLAIMS} | set(PENDING) | set(VERIFY_CLAIMS)


def given(node: ast.AST, said: set[str], returned: bool = False) -> set[str]:
    """The grant words and granting Verdicts `node` gives as a value: itself, or through a conditional, or
    `and` and `or`, and if it's `returned`, through a tuple, as a status and its reason are. A tuple of words
    assigned is a list of the ones a tool knows, which isn't a grant."""
    if isinstance(node, ast.Constant):
        return {node.value} & said if isinstance(node.value, str) else set()
    if isinstance(node, ast.Attribute) and node.attr in GRANTING:
        base = node.value
        if (
            isinstance(base, ast.Name | ast.Attribute)
            and (getattr(base, "id", None) or getattr(base, "attr", None)) == "Verdict"
        ):
            return {f"Verdict.{node.attr}"}
    if isinstance(node, ast.Tuple) and returned:
        return set().union(*(given(e, said, returned) for e in node.elts))
    if isinstance(node, ast.IfExp):
        return given(node.body, said, returned) | given(node.orelse, said, returned)
    if isinstance(node, ast.BoolOp):
        return set().union(*(given(v, said, returned) for v in node.values))
    return set()


def grants_in(source: str, path: str = "") -> dict[str, set[str]]:
    """Each function, class or module in `source` that returns, assigns, or sets as a `status` or `verdict`
    a grant's word or a granting Verdict, or that makes a Decision outside tools/irlean/verdict.py, by its
    dotted name, and what it gives. A word passed by position counts where `source` defines what it's passed
    to, and names that parameter `status` or `verdict`."""
    said = words()
    found: dict[str, set[str]] = collections.defaultdict(set)
    tree = ast.parse(source)
    # The parameters of each function and class `source` defines, by name.
    params: dict[str, list[str]] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef):
            params.setdefault(node.name, [a.arg for a in [*node.args.posonlyargs, *node.args.args]])
        elif isinstance(node, ast.ClassDef):
            for init in node.body:
                if isinstance(init, ast.FunctionDef) and init.name == "__init__":
                    params[node.name] = [a.arg for a in [*init.args.posonlyargs, *init.args.args]][1:]

    def visit(node: ast.AST, where: str) -> None:
        for child in ast.iter_child_nodes(node):
            values: list[Any] = []
            given_as = ast.Return | ast.Yield | ast.Assign | ast.AnnAssign | ast.AugAssign | ast.NamedExpr
            as_status = isinstance(child, ast.keyword) and child.arg in ("status", "verdict")
            if isinstance(child, given_as) or as_status:
                values.append(getattr(child, "value", None))
            elif isinstance(child, ast.Dict):
                values += [
                    v
                    for k, v in zip(child.keys, child.values, strict=True)
                    if isinstance(k, ast.Constant) and k.value in ("status", "verdict")
                ]
            elif isinstance(child, ast.Call):
                callee = getattr(child.func, "id", None) or getattr(child.func, "attr", None)
                if callee == "Decision" and path != "tools/irlean/verdict.py":
                    found[where].add("Decision")
                names = params.get(callee, []) if isinstance(child.func, ast.Name) else []
                values += [a for a, n in zip(child.args, names, strict=False) if n in ("status", "verdict")]
            returned = isinstance(child, ast.Return | ast.Yield)
            for value in values:
                if value is not None:
                    found[where] |= given(value, said, returned)
            inner = where
            if isinstance(child, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef):
                inner = child.name if where == "<module>" else f"{where}.{child.name}"
            visit(child, inner)

    visit(tree, "<module>")
    return {where: words for where, words in found.items() if words}


def tracked(*patterns: str) -> list[str]:
    """The files git has, or would add, matching `patterns`."""
    listed = ["git", "ls-files", "--cached", "--others", "--exclude-standard", *patterns]
    return sorted(f for f in proc.run(listed, cwd=ROOT).out.split() if (ROOT / f).is_file())


# Each place on main that gives a grant's word, or makes a Decision, outside tools/irlean/verdict.py, and why.
# It can only shrink: each tool's pull request in docs/verdicts.md's migration takes its own off, and at the
# end of stage A only tools/verify_claims.py and the fixtures that write one tool's record to feed another are
# left.
EXCEPTIONS: dict[str, str] = {
    "tools/verify.py::decide": "tools/verify.py's statuses, until it's on its grants: PR 3",
    "tools/prooftest/prooftest.py::decide": "tools/prooftest/prooftest.py's statuses: PR 6",
    "tools/store/store.py::lookup": "A lookup's `exact` and `instance`: PR 7",
    "tools/store/store.py::verdict": "A lemma's `admitted` and `candidate`: PR 7",
    "tools/rules/certify.py::conclude": "A certificate's `certified`: PR 8",
    "tools/binding.py::_verify": "A cached `bound`: PR 9",
    "tools/binding.py::replay": "A replayed `bound`: PR 9",
    "bench/instcombine/stage1.py::lean_verdict": "Joins tools/verify.py's and binding.py's records: PR 9",
    "bench/instcombine/stage1.py::classify": "A pair's `candidate`, one to prove, isn't the store's: PR 9",
    "tests/verify_negative.py::Outcome.line": "Prints a case's `certified`, from tools/verify.py's: PR 9",
    "tests/passes.py::Scorer.instances": "Records an instance Lean accepts as a `candidate`, not bound: PR 9",
    "tests/passes.py::Scorer.store": "Caches a `bound` instance as a `candidate`, never as bound: PR 9",
    "tests/binding.py::cache_cases": "What it expects tools/binding.py to say, passed as `status`: PR 9",
    "tests/peephole.py::counts": "The peephole scorer's `counted`: PR 10",
    "tools/irlean/verdict.py::Verdict": "The old form's claims, which only decide returns: PR 10",
    "tools/verify_claims.py::complete": "BIND-03's own guard, sharing no code, the one place of `replayed`",
    "tools/verify_claims.py::verified": "BIND-03's own guard, sharing no code, the one place of `verified`",
    "tests/gepcheck.py::classify": "Its `exact` is Alive2 agreeing both ways on a pointer, not the store's",
    "tests/irlean_test.py::Schemas.test_reading_checks_the_schema": "A fixture: tools/verify.py's record",
    "tests/passes_test.py::static": "Fixtures: tools/binding.py's records and the scorer's cache",
    "tests/passes_test.py::live": "A fixture: tools/binding.py's record, which the scorer reads",
    "tests/prooftest_test.py::static_checks": "A fixture: a record of tools/prooftest/prooftest.py's",
    "tests/verify_claims_test.py::static_cases": "A fixture: a claim saying `admitted`, its own status",
    "tests/verdict_test.py::PastBugs.test_a_cached_result_whose_certificate_is_gone_is_not_certified": (
        "A fixture: tools/binding.py's record, which decide reads"
    ),
    "tests/verdict_test.py::expected": "What the outcome table says decide answers",
    "tests/verdict_test.py::expected_of_cases": "What the outcome table says decide answers",
}

# Shell tests that run Lean, and print `ok` or exit 0 themselves rather than through tools/irlean/check.py,
# and the pull request that moves their decisions onto it. It can only shrink, to nothing after PR 5.
SHELL: dict[str, str] = {
    "tests/cut.sh": "PR 4",
    **{
        f"tests/{name}.sh": "PR 5"
        for name in (
            "proofs",
            "calls",
            "contracts",
            "float",
            "freeze",
            "refine",
            "generic_rewrites",
            "undef_freeze",
            "memory_refine",
            "exec_memory",
            "llama-bitspread",
            "llvm_heap",
            "emitter",
        )
    },
}
# A Lean process the script starts itself, and a line it grants with itself.
LEAN_RUN = re.compile(
    r"(?:^|[\s;|&(`]|\$\()(?:command\s+|exec\s+|lake\s+env\s+)?(?:lean|leanchecker)(?=\s|$|\))"
)
GRANTS_ITSELF = re.compile(r"""(?:echo|printf)\s+["']?ok\b|\bexit\s+0\b""")


def runs_lean_and_grants(text: str) -> bool:
    lines = [line for line in text.splitlines() if not line.lstrip().startswith("#")]
    runs = any(LEAN_RUN.search(line) and "check.py" not in line for line in lines)
    return runs and any(GRANTS_ITSELF.search(line) for line in lines)


# Where a grant word is given, as a status, in each way the lint has to see.
GIVES = (
    "def f():\n    return '{w}'\n",
    "def f():\n    return '{w}', 'why', 'detail'\n",
    "def f(x):\n    return '{w}' if x else 'error'\n",
    "def f(x):\n    return x and '{w}'\n",
    "def f():\n    status = '{w}'\n",
    "def f(r):\n    r['status'] = '{w}'\n",
    "def f():\n    return {{'status': '{w}', 'reason': 'r'}}\n",
    "def f(g):\n    g(verdict='{w}')\n",
    "def f(g):\n    g(status='{w}')\n",
    "def g(status, reason):\n    pass\n\n\ndef f():\n    return g('{w}', 'why')\n",
    "class C:\n    def f(self):\n        yield '{w}'\n",
)
# And where one isn't.
READS = (
    "def f(r):\n    return r['status'] == '{w}'\n",
    "def f():\n    return {{'{w}': 'what it means'}}\n",
    "def f():\n    '''{w}'''\n",
    "def f(g):\n    g('{w}')\n",
    "KNOWN = ('{w}', 'error')\n",
)


class OneLint(unittest.TestCase):
    """docs/verdicts.md's invariant 5. It replaces a lint that matched six words, by a pattern, in files not
    on its list, so a word such as `passed_tier1` or `exact`, or any word at all in a file on the list,
    passed."""

    def test_a_grant_word_is_found_anywhere(self) -> None:
        for word in sorted(words()):
            for form in GIVES:
                self.assertEqual(
                    grants_in(form.format(w=word)), {"f" if "class" not in form else "C.f": {word}}
                )
            for form in READS:
                self.assertEqual(grants_in(form.format(w=word)), {}, form)
        made = "def f(core):\n    return core.Decision(core.Verdict.PROVED, 'x')\n"
        self.assertEqual(grants_in(made), {"f": {"Decision"}})
        self.assertEqual(grants_in(made, "tools/irlean/verdict.py"), {})
        self.assertEqual(grants_in("def f(v):\n    return v.Verdict.CAUGHT\n"), {"f": {"Verdict.CAUGHT"}})
        self.assertEqual(grants_in("X = Verdict.GRANTED\n"), {"<module>": {"Verdict.GRANTED"}})

    def test_a_new_grant_word_is_found(self) -> None:
        with mock.patch.dict(GRANTS, {"x.adopted": Grant("adopted", 0, schemas.VERIFY)}):
            self.assertEqual(grants_in("def f():\n    return 'adopted'\n"), {"f": {"adopted"}})
        self.assertEqual(grants_in("def f():\n    return 'adopted'\n"), {})

    def test_no_word_is_both_pending_and_in_grants(self) -> None:
        self.assertEqual(set(PENDING) & {g.word for g in GRANTS.values()}, set())

    def test_nothing_gives_a_grant_but_what_the_list_says(self) -> None:
        found = {
            f"{path}::{where}": said
            for path in tracked("tools/*.py", "tests/*.py", "bench/*.py")
            for where, said in grants_in((ROOT / path).read_text(), path).items()
        }
        unlisted = {k: sorted(v) for k, v in found.items() if k not in EXCEPTIONS}
        self.assertEqual(
            unlisted, {}, "these give a grant outside irlean.verdict: ask decide, through an adapter"
        )
        stale = sorted(set(EXCEPTIONS) - set(found))
        self.assertEqual(stale, [], "these don't give a grant any more: take them off EXCEPTIONS")

    def test_no_shell_test_grants_a_lean_process_itself(self) -> None:
        found = {
            p for p in tracked("tests/*.sh", "bench/*.sh") if runs_lean_and_grants((ROOT / p).read_text())
        }
        self.assertEqual(sorted(found - set(SHELL)), [], "these run Lean, and grant themselves")
        self.assertEqual(sorted(set(SHELL) - found), [], "these don't any more: take them off SHELL")
        self.assertTrue(runs_lean_and_grants("lean x.lean\nprintf 'ok    x\\n'\n"))
        self.assertTrue(runs_lean_and_grants("out=$(command lean -M 4000 x.lean 2>&1)\nexit 0\n"))
        self.assertFalse(runs_lean_and_grants("tools/irlean/check.py module X\n# lean x.lean\necho ok\n"))


# Calls of `decide` in the old form, asked for a claim rather than a grant's name, by file. It can only fall:
# each tool's pull request in docs/verdicts.md's migration takes its own off, and the last, PR 10, takes the
# old form away.
LEGACY: dict[str, int] = {
    "tools/verify.py": 2,
    "tools/prooftest/prooftest.py": 1,
    "tools/rules/proved.py": 1,
    "tools/rules/certify.py": 1,
    "tools/store/store.py": 1,
    "tools/binding.py": 1,
    "bench/instcombine/stage1.py": 2,
    "tests/passes.py": 1,
    "tests/llvm.py": 2,
    "tests/llama.py": 3,
    "tests/superopt.py": 2,
    "tests/cpp_correspondence.py": 2,
    "tests/verify_negative.py": 1,
    "tests/peephole.py": 1,
    "tests/rules_test.py": 2,
}


def legacy_calls(source: str) -> int:
    """How many times `source` calls irlean.verdict's `decide` with anything but a grant's name."""
    tree = ast.parse(source)
    modules, functions = set(), set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module in ("irlean", "irlean.verdict"):
            for alias in node.names:
                if (node.module, alias.name) == ("irlean", "verdict"):
                    modules.add(alias.asname or alias.name)
                elif (node.module, alias.name) == ("irlean.verdict", "decide"):
                    functions.add(alias.asname or alias.name)
    count = 0
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not node.args:
            continue
        f = node.func
        ours = isinstance(f, ast.Name) and f.id in functions
        ours |= (
            isinstance(f, ast.Attribute) and f.attr == "decide" and getattr(f.value, "id", None) in modules
        )
        first = node.args[0]
        count += ours and not (isinstance(first, ast.Constant) and first.value in GRANTS)
    return count


class LegacyCalls(unittest.TestCase):
    """docs/verdicts.md's invariant 6."""

    def test_the_old_form_only_falls(self) -> None:
        found = {
            path: n
            for path in tracked("tools/*.py", "tests/*.py", "bench/*.py")
            if path != "tests/verdict_test.py" and (n := legacy_calls((ROOT / path).read_text()))
        }
        self.assertEqual(found, LEGACY, "LEGACY counts the old form's calls, and can only fall")

    def test_what_counts(self) -> None:
        self.assertEqual(legacy_calls("from irlean import verdict as v\nv.decide(v.Verdict.PROVED, e)\n"), 1)
        self.assertEqual(legacy_calls("from irlean.verdict import decide\ndecide(claim, e)\n"), 1)
        self.assertEqual(legacy_calls("from irlean import verdict\nverdict.decide('verify.proved', e)\n"), 0)
        self.assertEqual(legacy_calls("import x as v\nv.decide(run)\ndecide(run)\n"), 0)


if __name__ == "__main__":
    # Set where this runs, it would take every grant away the tests expect.
    os.environ.pop(DENY_ALL, None)
    unittest.main()
