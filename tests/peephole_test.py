#!/usr/bin/env python3
"""Checks tests/peephole.py, docs/rewrite-proofs.md, and that its checks can fail.

- static, in Python only: instructions as `opt -S` prints them become the operand trees `Term` holds, with one
  identity for one value; each case's function is what it should be; each way a case can come out of the
  comparison is classified as it should be; a rewrite counts only when every rule holds, and each rule broken
  alone, or a process stopped at a limit, keeps it from counting; a comparison recorded for other sources, or
  with a mismatch, doesn't count; a registry of the wrong shape is refused; and the generated operands are
  well formed.
- live, with Lean, opt and the library built: every opcode's generated cases are IR `opt` accepts; a model
  that drops `simplifyAddInst`'s `nuw` guard, and one that drops its sign-mask rule's flag guard, each fail
  `compare` at that site and no other; and a site proved with `sorry` makes `score --check` fail.

usage: tests/peephole_test.py --tier static|live
"""

import argparse
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, ClassVar
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import peephole  # noqa: E402

from irlean import lean as leanlib  # noqa: E402
from irlean import proc  # noqa: E402
from irlean import verdict as core  # noqa: E402

ADD = peephole.PEEPHOLE / "Peephole" / "IS" / "Add.lean"


def inst(text: str) -> tuple:
    """An instruction `Term` holds, parsed."""
    parsed = peephole.parse_instruction(text)
    assert parsed is not None, text
    return parsed


class Parse(unittest.TestCase):
    def test_instructions(self) -> None:
        p = peephole.parse_instruction
        self.assertEqual(
            p("add nuw nsw i8 %x, -1, !dbg !7"),
            ("bin", 8, {"op": "add", "nuw": True, "nsw": True}, [(8, "%x"), (8, "-1")]),
        )
        self.assertEqual(
            p("icmp samesign ult i32 %a, 7"),
            ("icmp", 1, {"p": "ult", "samesign": True}, [(32, "%a"), (32, "7")]),
        )
        self.assertEqual(
            p("select i1 %c, i8 %a, i8 poison"), ("select", 8, {}, [(1, "%c"), (8, "%a"), (8, "poison")])
        )
        self.assertEqual(p("zext nneg i8 %x to i32"), ("zext", 32, {"nneg": True}, [(8, "%x")]))
        self.assertEqual(p("trunc nuw i32 %x to i8"), ("trunc", 8, {"nuw": True}, [(32, "%x")]))
        self.assertEqual(
            p("call range(i8 0, 9) i8 @llvm.ctlz.i8(i8 %x, i1 true) #2"),
            ("un", 8, {"f": "ctlz", "flag": True}, [(8, "%x")]),
        )
        self.assertEqual(
            p("tail call i8 @llvm.uadd.sat.i8(i8 %a, i8 %b)"),
            ("bi", 8, {"f": "uadd.sat"}, [(8, "%a"), (8, "%b")]),
        )
        self.assertEqual(
            p("call i8 @llvm.fshr.i8(i8 %a, i8 %b, i8 3)"),
            ("fsh", 8, {"left": False}, [(8, "%a"), (8, "%b"), (8, "3")]),
        )
        # Vectors, pointers, an intrinsic Term doesn't have, and a flag that isn't a constant aren't held.
        for text in (
            "add <2 x i8> %x, %y",
            "getelementptr i8, ptr %p, i64 1",
            "call i8 @llvm.ctlz.i8(i8 %x, i1 %f)",
            "call i8 @f(i8 %x)",
            "call i32 @llvm.ctpop.v2i32(<2 x i32> %x)",
        ):
            self.assertIsNone(p(text), text)

    def test_trees_keep_identity_and_stop(self) -> None:
        defs = {
            "%n": "xor i8 %x, -1",
            "%s": "sub i8 %y, %n",
            "%r": "add i8 %n, %s",
            "%l": "load i8, ptr %p",
            "%q": "add i8 %l, %l",
        }
        b = peephole.Builder(defs)
        t = b.node("%r", inst(defs["%r"]), 0, frozenset())
        # The `xor` is one value, in both places, so a match by address sees it as one.
        self.assertEqual(t["a"]["id"], t["b"]["b"]["id"])
        self.assertEqual(t["a"]["k"], "bin")
        self.assertEqual(t["b"]["a"], {"k": "var", "w": 8, "id": b.ids["%y"]})
        # An instruction Term can't hold is an argument.
        q = peephole.Builder(defs).node("%q", inst(defs["%q"]), 0, frozenset())
        self.assertEqual(q["a"]["k"], "var")
        self.assertEqual(q["a"], q["b"])
        # Below the depth limit an instruction is an argument too.
        deep = peephole.Builder(defs).node("%r", inst(defs["%r"]), peephole.MAX_DEPTH - 1, frozenset())
        self.assertEqual(deep["a"]["k"], "var")

    def test_one_case_per_shape(self) -> None:
        def tree(defs: dict[str, str], root: str) -> dict:
            return peephole.Builder(defs).node(root, inst(defs[root]), 0, frozenset())

        one = tree({"%a": "sub i8 %x, %y", "%r": "add i8 %a, %y"}, "%r")
        two = tree({"%b": "sub i8 %p, %q", "%t": "add i8 %b, %q"}, "%t")
        other = tree({"%b": "sub i8 %p, %q", "%t": "add i8 %b, %p"}, "%t")
        key = lambda t: json.dumps(peephole.canonical(t), sort_keys=True)  # noqa: E731
        self.assertEqual(key(one), key(two))
        self.assertNotEqual(key(one), key(other))


def bin_(op: str, a: dict, b: dict, i: int, **f: bool) -> dict:
    return {"k": "bin", "w": a["w"], "id": i, "op": op, **f, "a": a, "b": b}


V0, V1 = {"k": "var", "w": 8, "id": 0}, {"k": "var", "w": 8, "id": 1}


class Emit(unittest.TestCase):
    def test_function(self) -> None:
        sub = bin_("sub", V1, V0, 5, nsw=True)
        text, names = peephole.Emitter().function(3, bin_("add", V0, sub, 9, nuw=True))
        self.assertEqual(
            text.splitlines(),
            [
                "define i8 @c3(i8 %v0, i8 %v1) {",
                "  %n5 = sub nsw i8 %v1, %v0",
                "  call void (...) @use(i8 %v0, i8 %n5)",
                "  %r = add nuw i8 %v0, %n5",
                "  ret i8 %r",
                "}",
            ],
        )
        self.assertEqual(names, {0: "%v0", 1: "%v1", 5: "%n5", 9: "%r"})

    def test_intrinsics_are_declared(self) -> None:
        em = peephole.Emitter()
        em.function(0, {"k": "un", "w": 8, "id": 4, "f": "abs", "flag": True, "a": V0})
        self.assertIn("declare i8 @llvm.abs.i8(i8, i1)", em.module([]))

    def test_expected_text(self) -> None:
        names = {0: "%v0", 5: "%n5"}
        e = peephole.expected_text
        self.assertEqual(e({"k": "old", "w": 8, "t": {"node": 5}}, names), "%n5")
        self.assertEqual(e({"k": "old", "w": 8, "t": {"const": "255"}}, names), "-1")
        self.assertEqual(e({"k": "const", "w": 1, "c": "1"}, names), "true")
        self.assertEqual(e({"k": "old", "w": 8, "t": "undef"}, names), "undef")
        self.assertEqual(e({"k": "poison", "w": 8}, names), "poison")
        self.assertIsNone(e({"k": "bin", "w": 8, "op": "add"}, names))


BEFORE = [
    "  %n5 = sub i8 %v1, %v0",
    "  call void (...) @use(i8 %v0, i8 %n5)",
    "  %r = add i8 %v0, %n5",
    "  ret i8 %r",
]


def after(ret: str, changed: bool = False) -> list[str]:
    """The function after opt, the root folded to `ret`, or kept if `ret` is `%r`."""
    lines = [*BEFORE[:2], *(BEFORE[2:3] if ret == "%r" else []), f"  ret i8 {ret}"]
    return [lines[0].replace("%v1", "0"), *lines[1:]] if changed else lines


class Classify(unittest.TestCase):
    def outcome(self, answer: dict, opt_after: list[str], files: list[str] | None = None) -> peephole.Tally:
        t = peephole.Tally()
        case = peephole.Case("c", "F", "instsimplify", "add", {}, files or [])
        peephole.classify(case, answer, BEFORE, opt_after, {0: "%v0", 1: "%v1", 5: "%n5", 9: "%r"}, t)
        return t

    def test_each_outcome(self) -> None:
        fires = {"result": {"value": {"k": "old", "w": 8, "t": {"node": 1}}}, "site": "IS.f.L1"}
        t = self.outcome(fires, after("%v1"), ["a.ll"])
        self.assertEqual((t.matched, t.mismatched, t.sites["IS.f.L1"]["files"]), (1, 0, {"a.ll"}))
        # The model fires where opt doesn't, or answers otherwise: a mismatch.
        self.assertEqual(self.outcome(fires, after("%r")).mismatched, 1)
        self.assertEqual(self.outcome(fires, after("%v0")).mismatched, 1)
        # Neither folds.
        self.assertEqual(self.outcome({"result": {"null": True}}, after("%r")).agreed_no_fold, 1)
        # opt folds, the model doesn't: an analysis that answered yes explains it, or nothing does.
        explained = {"result": {"null": True}, "analysis": {"oracle": "x", "site": "IS.f.L2"}}
        t = self.outcome(explained, after("0"))
        self.assertEqual((t.analysis, t.sites["IS.f.L2"]["analysis"], t.mismatched), (1, 1, 0))
        t = self.outcome({"result": {"null": True}}, after("0"))
        self.assertEqual((t.unexplained, t.mismatched), (1, 0))
        # Delegated: nothing compared, whatever opt does.
        t = self.outcome({"result": {"delegated": "simplifyXorInst"}}, after("0"))
        self.assertEqual((t.delegated, t.compared, t.delegated_to["simplifyXorInst"]), (1, 0, 1))
        # An operand changed first: left out, even where the answers differ.
        t = self.outcome(fires, after("%r", changed=True))
        self.assertEqual((t.operand_changed, t.compared, t.mismatched), (1, 0, 0))


def step(name: str, exit_: int = 0, limit: str | None = None, output: str = "") -> core.Step:
    return core.Step(name, exit_, limit, output)


class Counts(unittest.TestCase):
    """A rewrite counts only when every rule holds."""

    SOUND: ClassVar[str] = "Peephole.IS.f.sound"
    FOUND: ClassVar[dict[str, Any]] = {
        "name": "Peephole.IS.f.L1",
        "kind": "theorem",
        "module": "M",
        "axioms": ["propext", "Quot.sound"],
    }
    SND: ClassVar[dict[str, Any]] = {
        "kind": "theorem",
        "axioms": ["propext"],
        "sites": ["Peephole.IS.f.L1"],
        "found": True,
    }
    RAN: ClassVar[dict[str, Any]] = {
        "check_axioms": step("check_axioms"),
        "leanchecker": step("leanchecker"),
        "bv_decide": 0,
    }

    def decide(self, **change: Any) -> core.Decision:
        a: dict[str, Any] = {
            "found": self.FOUND,
            "snd": self.SND,
            "built": step("lake"),
            "ran": self.RAN,
            "why_not": "",
        } | change
        return peephole.counts(
            "IS.f.L1", a["found"], self.SOUND, a["snd"], a["built"], a["ran"], a["why_not"]
        )

    def test_every_rule(self) -> None:
        self.assertTrue(self.decide().granted)
        broken = {
            "no theorem": {"found": None},
            "sorry": {"found": {**self.FOUND, "axioms": ["sorryAx"]}},
            "bv_decide's native code": {"found": {**self.FOUND, "axioms": ["Lean.ofReduceBool"]}},
            "the fold's theorem doesn't use it": {"snd": {**self.SND, "sites": []}},
            "the fold's theorem isn't there": {"snd": {}},
            "the fold's theorem rests on sorry": {"snd": {**self.SND, "axioms": ["sorryAx"]}},
            "its module rests on bv_decide": {"ran": {**self.RAN, "bv_decide": 1}},
            "the comparison isn't current": {"why_not": "compared other sources"},
            "the audit failed": {"ran": {**self.RAN, "check_axioms": step("check_axioms", 1)}},
            "leanchecker failed": {"ran": {**self.RAN, "leanchecker": step("leanchecker", 1)}},
            "leanchecker didn't run": {"ran": {k: v for k, v in self.RAN.items() if k != "leanchecker"}},
            "lake has more to build": {"built": step("lake", 1)},
        }
        for what, change in broken.items():
            with self.subTest(what):
                self.assertFalse(self.decide(**change).granted)
        limited = self.decide(ran={**self.RAN, "leanchecker": step("leanchecker", -9, "time_limit")})
        self.assertEqual(limited.verdict, core.Verdict.UNKNOWN)


class Records(unittest.TestCase):
    def test_only_a_current_clean_comparison_counts(self) -> None:
        reg = peephole.registries("is-add")[0]
        with tempfile.TemporaryDirectory() as d, mock.patch.object(peephole, "COMPARED", Path(d)):
            self.assertIn("no comparison", peephole.recorded(reg)[1])
            path = Path(d) / "is-add.json"
            base = {"schema": peephole.schemas.PEEPHOLE_COMPARISON, "family": "is-add"}
            path.write_text(json.dumps({**base, "sources": "0" * 64, "status": "ok"}))
            self.assertIn("other sources", peephole.recorded(reg)[1])
            path.write_text(json.dumps({**base, "sources": peephole.model_hash(reg), "status": "mismatch"}))
            self.assertIn("mismatch", peephole.recorded(reg)[1])
            path.write_text(json.dumps({**base, "sources": peephole.model_hash(reg), "status": "ok"}))
            self.assertEqual(peephole.recorded(reg)[1], "")

    def test_the_hash_covers_the_model_and_what_it_imports(self) -> None:
        reg = peephole.registries("is-add")[0]
        sources = {p.name for p in peephole.model_sources(reg.modules)}
        self.assertTrue({"Add.lean", "Term.lean", "Match.lean", "Fold.lean", "Oracle.lean"} <= sources)


class Registries(unittest.TestCase):
    def test_shapes(self) -> None:
        path = peephole.FOLDS / "is-add.json"
        good = json.loads(path.read_text())
        self.assertEqual(peephole.registry_problems(path, good), [])
        bad = {
            "family": {**good, "family": "other"},
            "pass": {**good, "pass": "gvn"},
            "opcode": {**good, "entries": [{**good["entries"][0], "opcodes": ["fadd"]}]},
            "entry": {**good, "entries": [{**good["entries"][0], "fold": "simplifyAddInst"}]},
            "fold": {**good, "folds": {"F": {"sites": []}}},
        }
        for what, data in bad.items():
            with self.subTest(what):
                self.assertNotEqual(peephole.registry_problems(path, data), [])
        self.assertEqual(peephole.opcode_name("llvm.uadd_sat"), "uadd.sat")


def widths_hold(t: dict) -> bool:
    """Each operand has the width its instruction needs."""
    k, w = t["k"], t["w"]
    if k in ("const", "poison", "undef", "var"):
        return w >= 1
    kids = [t[key] for key in peephole.OPERANDS[k]]
    if k == "icmp":
        need = [kids[0]["w"]] * 2
        ok = w == 1
    elif k == "select":
        need, ok = [1, w, w], True
    elif k in peephole.CASTS:
        need = [kids[0]["w"]]
        ok = kids[0]["w"] < w if k != "trunc" else kids[0]["w"] > w
    else:
        need, ok = [w] * len(kids), True
    return ok and [c["w"] for c in kids] == need and all(widths_hold(c) for c in kids)


class Generated(unittest.TestCase):
    def test_every_opcode(self) -> None:
        for op in peephole.OPCODES:
            with self.subTest(op):
                terms = peephole.generated_terms(op)
                self.assertTrue(0 < len(terms) <= peephole.GENERATED_CAP)
                self.assertTrue(all(widths_hold(t) for t in terms))
                self.assertTrue(all(peephole.opcode_of(t["k"], t) == op for t in terms))
        self.assertTrue(all(t["w"] % 16 == 0 for t in peephole.generated_terms("bswap")))


# ------------------------------------------------------------------------------------------------------------
# Live: with Lean, opt and the library built


def harness(*args: str, overlay: Path | None = None) -> proc.Ran:
    env = {**os.environ, **({"PEEPHOLE_OVERLAY": str(overlay)} if overlay else {})}
    return proc.run(
        [sys.executable, str(ROOT / "tests" / "peephole.py"), *args], cwd=ROOT, env=env, timeout=1800
    )


def overlay_with(text: str, work: Path) -> Path:
    """The library, with `Peephole.IS.Add` compiled from `text`, in a directory of its own to put in front of
    lake's. Lean looks for a library's modules where it first finds its root, so the rest comes too."""
    shutil.copytree(leanlib.LIBRARY / "Peephole", work / "Peephole")
    src = work / "Peephole" / "IS" / "Add.lean"
    src.write_text(text)
    r = proc.run(
        leanlib.argv(peephole.LEAN_MB, "-R", work, "-o", src.with_suffix(".olean"), src),
        cwd=ROOT,
        env=leanlib.env(),
        timeout=600,
    )
    if r.exit != 0:
        raise AssertionError(f"the changed module doesn't compile:\n{r.output[-3000:]}")
    return work


def model_only(change: str, to: str) -> str:
    """Add.lean's model, without its theorems, with one line changed: a model the theorems would refuse,
    which only the comparison with opt sees as a model."""
    text = ADD.read_text()
    assert text.count(change) == 1, change
    model = text.split("/-! ### The rewrites, one theorem each -/")[0]
    return model.replace(change, to) + "end Peephole.IS\n"


class Live(unittest.TestCase):
    def test_generated_cases_are_ir_opt_accepts(self) -> None:
        em = peephole.Emitter()
        texts: list[str] = []
        for op in peephole.OPCODES:
            terms = peephole.generated_terms(op)
            for t in terms[:: max(1, len(terms) // 40)]:
                texts.append(em.function(len(texts), t)[0])
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "cases.ll"
            path.write_text(em.module(texts))
            r = proc.run(["opt", "-passes=verify", "-disable-output", str(path)], timeout=300)
        self.assertEqual(r.exit, 0, r.err[-2000:])

    def mutant(self, change: str, to: str, site: str) -> None:
        with tempfile.TemporaryDirectory() as d:
            r = harness(
                "compare", "--family", "is-add", overlay=overlay_with(model_only(change, to), Path(d))
            )
        said = r.output
        self.assertEqual(r.exit, 1, said[-3000:])
        lines = [x for x in said.splitlines() if "MISMATCH" in x]
        self.assertTrue(lines, said[-3000:])
        self.assertTrue(all(f", {site}: " in x for x in lines), "\n".join(lines[:10]))

    def test_dropping_the_nuw_guard_mismatches(self) -> None:
        self.mutant(
            "if isNUW && allOnes op1 then .fire", "if allOnes op1 then .fire", "IS.simplifyAddInst.L637"
        )

    def test_dropping_the_sign_mask_flag_guard_mismatches(self) -> None:
        self.mutant(
            "if (isNSW || isNUW) && signMask op1 then", "if signMask op1 then", "IS.simplifyAddInst.L633"
        )

    def test_a_site_proved_by_sorry_doesnt_count(self) -> None:
        proof = "  rw [addSrc_eval, cst_eq h, Generic.add_zero]\n  exact refines_ok (Refine.refl_val _)"
        text = ADD.read_text()
        self.assertEqual(text.count(proof), 1)
        with tempfile.TemporaryDirectory() as d:
            r = harness(
                "score",
                "--check",
                "--out",
                str(Path(d) / "s.json"),
                overlay=overlay_with(text.replace(proof, "  sorry"), Path(d) / "o"),
            )
        said = r.output
        self.assertEqual(r.exit, 1, said[-3000:])
        self.assertRegex(
            said, r"FAIL  is-add: IS\.simplifyAddInst\.L609 is listed as proved, and doesn't count"
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--tier", choices=["static", "live"], required=True)
    args = parser.parse_args()
    cases = (
        [Parse, Emit, Classify, Counts, Records, Registries, Generated] if args.tier == "static" else [Live]
    )
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(c) for c in cases)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)


if __name__ == "__main__":
    main()
