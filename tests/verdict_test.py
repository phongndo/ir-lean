#!/usr/bin/env python3
"""Checks tools/irlean/verdict.py, the one place Python decides a verdict, without Lean, in a few seconds.

- Exhaustively, over every combination of a set of ways each process can end, each file can be there or not,
  and each check can pass, fail or not run, that `decide` grants a claim only when everything it rests on is
  clean, calls it `unknown` only when a limit could explain it, and never grants a different claim.
- Adversarially, that breaking any one or two things in evidence it grants, in each way it can break, always
  takes the grant away, including values that only look right, such as `False` for exit code 0.
- That the three verdicts Python got wrong before can't come back: a crashed native check counting as catching
  a wrong rewrite, and a slice that didn't compile counting as a refutation, both in #57, and a cached result
  whose certificate is gone counting as certified, in #51.
- That each tool and test that decides one of these verdicts asks `decide`, and doesn't grant it otherwise.

docs/trust.md#where-python-decides-a-verdict.

usage: tests/verdict_test.py
"""

import dataclasses
import importlib.util
import itertools
import re
import sys
import unittest
from pathlib import Path
from typing import Any, ClassVar
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc, schemas  # noqa: E402
from irlean.verdict import CLAIMS, UPSTREAM, Decision, Evidence, Step, Verdict, decide  # noqa: E402

LIMIT_TEXT = "x.lean:3:2: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)"
ERROR_TEXT = "x.lean:3:2: error: type mismatch"

# Every way a process can end, by name: what it is, whether it's clean (exit 0, nothing stopped it), and
# whether a limit stopped it, when its output is read as Lean's.
STEPS: dict[str, tuple[Step | None, bool, bool]] = {
    "absent": (None, False, False),
    "clean": (Step("p", 0), True, False),
    "clean_with_limit_text": (Step("p", 0, output=LIMIT_TEXT), True, False),
    "never_ended": (Step("p", None), False, False),
    "failed": (Step("p", 1, output=ERROR_TEXT), False, False),
    "failed_quietly": (Step("p", 1), False, False),
    "failed_at_a_lean_limit": (Step("p", 1, output=LIMIT_TEXT), False, True),
    "exit_2": (Step("p", 2), False, False),
    "exit_3": (Step("p", 3, output="differs"), False, False),
    "time_limit": (Step("p", -9, limit="time_limit"), False, True),
    "cap": (Step("p", -9, limit="resource_limit"), False, True),
    "zero_but_stopped": (Step("p", 0, limit="time_limit"), False, True),
    "sigkill": (Step("p", -9), False, True),
    "sigkill_from_a_shell": (Step("p", 137), False, True),
    "segfault": (Step("p", -11), False, False),
    "abort": (Step("p", -6), False, False),
    "exit_false": (Step("p", False), False, False),
    "exit_text": (Step("p", "0"), False, False),  # ty: ignore[invalid-argument-type]
}
FILES: dict[str, Any] = {
    "none": {},
    "there": {"a": True},
    "gone": {"a": True, "b": False},
    "truthy": {"a": 1},
    "unknown": {"a": None},
}
CHECKS: dict[str, Any] = {
    "none": {},
    "passed": {"c": True},
    "failed": {"c": False},
    "not_run": {"c": None},
    "truthy": {"c": "yes"},
}
FLAGS: dict[str, Any] = {"absent": None, "true": True, "false": False, "truthy": 1}


def clean(step: Step | None) -> bool:
    return step is not None and STEPS[name_of(step)][1]


def limited(step: Step | None, read_output: bool = True) -> bool:
    if step is None:
        return False
    stopped = STEPS[name_of(step)][2]
    # A Lean limit is only read from the output of a Lean process the verdict rests on.
    if name_of(step) == "failed_at_a_lean_limit" and not read_output:
        return False
    return stopped


def name_of(step: Step) -> str:
    # By identity: a step that exits `False` equals one that exits 0, as False == 0.
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
            for kernel, evaluated, cached, (
                _,
                (lean, lean_clean, lean_limit),
            ), files, checks in itertools.product(
                FLAGS.values(), FLAGS.values(), FLAGS.values(), STEPS.items(), FILES.values(), CHECKS.values()
            ):
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
                        self.check(claim, e, grants and ended and exact, limited(step, read_output=False))
            self.assertFalse(
                decide(claim, Evidence(upstream=(Step("u", 0), ["proved"]), files={"a": True})).granted
            )

    def test_caught(self) -> None:
        findings = [None, "", "   ", ERROR_TEXT, LIMIT_TEXT, "differs"]
        for step, found_exit, finding, checks in itertools.product(
            [s for s, _, _ in STEPS.values()], (1, 3, 0), findings, CHECKS.values()
        ):
            e = Evidence(step=step, found_exit=found_exit, finding=finding, checks=checks)
            any_limit = limited(step, read_output=False)
            ended = step is not None and same_code(step.exit, found_exit) and not step.limit
            checks_ok = all(v is True for v in checks.values())
            own = bool((finding or "").strip()) and finding != LIMIT_TEXT
            limit_found = ended and checks_ok and finding == LIMIT_TEXT
            self.check(
                Verdict.CAUGHT, e, not any_limit and ended and checks_ok and own, any_limit or limit_found
            )

    def test_only_the_four_are_claims(self) -> None:
        for claim in ("unknown", "error", "bound", "", None, 1, "PROVED"):
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
    bad_steps = {n: s for n, (s, ok, _) in STEPS.items() if not ok}
    for field in ("lean", "replay", "axioms", "step"):
        current = getattr(e, field)
        if isinstance(current, Step):
            for n, s in bad_steps.items():
                if field == "step" and s is not None and same_code(s.exit, e.found_exit) and not s.limit:
                    continue
                replaced = None if s is None else dataclasses.replace(s, name=current.name)
                out.append((f"{field}={n}", dataclasses.replace(e, **{field: replaced})))
    if e.axioms is True:
        for v in (False, None, 1, "yes"):
            out.append((f"axioms={v!r}", dataclasses.replace(e, axioms=v)))
    for field in ("kernel", "evaluated", "cached"):
        if getattr(e, field) is True:
            for v in (False, None, 1, "yes"):
                out.append((f"{field}={v!r}", dataclasses.replace(e, **{field: v})))
    for v in (False, None, 0, 1, "yes"):
        out.append((f"a file {v!r}", dataclasses.replace(e, files={**e.files, "extra": v})))
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
        self.assertGreater(count, 500)

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

    def test_no_other_site_grants_these_verdicts(self) -> None:
        # A file that returns one of these verdicts, or sets a status to one, has to be one of SITES. Today
        # that's tools/verify.py, tools/binding.py and tools/prooftest/prooftest.py.
        word = r"""["'](proved|bound|certified|refuted|caught|counterexample)["']"""
        said = re.compile(rf"""return\s*\(?\s*{word}|["']status["']\s*:\s*{word}|status\s*=\s*{word}""")
        files = proc.run(
            [
                "git",
                "ls-files",
                "--cached",
                "--others",
                "--exclude-standard",
                "tools/*.py",
                "tests/*.py",
                "bench/*.py",
            ],
            cwd=ROOT,
        ).out.split()
        found = sorted(
            f
            for f in files
            if (ROOT / f).exists() and not f.endswith("_test.py") and said.search((ROOT / f).read_text())
        )
        self.assertEqual([f for f in found if f not in self.SITES], [])
        self.assertGreaterEqual(len(found), 3)


if __name__ == "__main__":
    unittest.main()
