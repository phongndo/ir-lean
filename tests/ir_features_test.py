#!/usr/bin/env python3
"""Tests of tests/ir_features.py's rules, without LLVM: an item no rule classifies, or two rules do, fails; a
rule can't model or assume by prefix; a rule naming what the pin doesn't have fails; and the file in the repo
is well formed, with a class for every item and a lane only on refused ones.

usage: tests/ir_features_test.py
"""

from __future__ import annotations

import json
import unittest
from pathlib import Path
from unittest import mock

import ir_features as f

ROOT = Path(__file__).resolve().parent.parent


def items(*names: tuple[str, str]) -> list[f.Item]:
    return [f.Item(kind, name) for kind, name in names]


class Rules(unittest.TestCase):
    def classify(self, rules: list[f.Rule], found: list[f.Item]) -> tuple[list, list[str]]:
        with mock.patch.dict(f.RULES, {"intrinsic": rules}, clear=False):
            return f.classify(found)

    def test_every_item_classified(self) -> None:
        rows, problems = self.classify(
            [f.R("integer", "llvm.abs"), f.R("x86", "", "llvm.x86.")],
            items(("intrinsic", "llvm.abs"), ("intrinsic", "llvm.x86.foo")),
        )
        self.assertEqual(problems, [])
        self.assertEqual([r["class"] for r in rows], ["modeled", "refused"])
        self.assertEqual(rows[1]["lane"], "long tail")
        self.assertNotIn("lane", rows[0])

    def test_unclassified_fails(self) -> None:
        _, problems = self.classify(
            [f.R("integer", "llvm.abs")], items(("intrinsic", "llvm.abs"), ("intrinsic", "llvm.new"))
        )
        self.assertIn("unclassified: intrinsic llvm.new", problems)

    def test_two_exact_rules_fail(self) -> None:
        _, problems = self.classify(
            [f.R("integer", "llvm.abs"), f.R("integer gap", "llvm.abs")], items(("intrinsic", "llvm.abs"))
        )
        self.assertTrue(any(p.startswith("two rules match intrinsic llvm.abs") for p in problems), problems)

    def test_two_prefixes_fail(self) -> None:
        _, problems = self.classify(
            [f.R("x86", "", "llvm.x86."), f.R("other target", "", "llvm.x86.avx")],
            items(("intrinsic", "llvm.x86.avx.foo")),
        )
        self.assertTrue(any(p.startswith("two rules match") for p in problems), problems)

    def test_exact_rule_wins_over_prefix(self) -> None:
        rows, problems = self.classify(
            [f.R("x86 dot product", "llvm.x86.sse2.pmadd.wd"), f.R("x86", "", "llvm.x86.")],
            items(("intrinsic", "llvm.x86.sse2.pmadd.wd")),
        )
        self.assertEqual(problems, [])
        self.assertEqual(rows[0]["class"], "modeled")

    def test_modeled_by_prefix_fails(self) -> None:
        # A prefix would model whatever a later LLVM adds under it, unreviewed.
        _, problems = self.classify([f.R("integer", "", "llvm.")], items(("intrinsic", "llvm.abs")))
        self.assertTrue(any("matches by prefix" in p for p in problems), problems)

    def test_assumed_by_prefix_fails(self) -> None:
        _, problems = self.classify([f.R("hint", "", "llvm.")], items(("intrinsic", "llvm.abs")))
        self.assertTrue(any("matches by prefix" in p for p in problems), problems)

    def test_rule_naming_what_the_pin_lacks_fails(self) -> None:
        _, problems = self.classify([f.R("integer", "llvm.abs llvm.gone")], items(("intrinsic", "llvm.abs")))
        self.assertTrue(any("'llvm.gone'" in p for p in problems), problems)

    def test_unknown_reason_fails(self) -> None:
        _, problems = self.classify([f.R("no such reason", "llvm.abs")], items(("intrinsic", "llvm.abs")))
        self.assertTrue(any("no reason" in p for p in problems), problems)

    def test_positions(self) -> None:
        rules = [
            f.R("value promise", "noundef", at="parameter"),
            f.R("external", "noundef", at="call parameter"),
        ]
        found = [
            f.Item("attribute", "noundef", "parameter"),
            f.Item("attribute", "noundef", "call parameter"),
        ]
        with mock.patch.dict(f.RULES, {"attribute": rules}, clear=False):
            rows, problems = f.classify(found)
        self.assertEqual(problems, [])
        self.assertEqual(
            [(r["at"], r["class"]) for r in rows], [("parameter", "modeled"), ("call parameter", "refused")]
        )


class Partial(unittest.TestCase):
    def test_each_partial_refusal_names_a_refused_item(self) -> None:
        rules = {(k, n) for k, rs in f.RULES.items() for r in rs for n in r.names}
        for _, (kind, _, name) in f.PARTIAL:
            reason = next(r.reason for r in f.RULES[kind] if name in r.names)
            self.assertIn((kind, name), rules)
            self.assertEqual(f.REASONS[reason].cls, "refused", name)


class File(unittest.TestCase):
    def setUp(self) -> None:
        self.doc = json.loads(f.FILE.read_text())

    def test_schema_and_render(self) -> None:
        self.assertEqual(self.doc["schema"], f.SCHEMA)
        self.assertEqual(f.FILE.read_text(), f.render(self.doc))

    def test_every_item_has_a_class(self) -> None:
        for row in self.doc["items"]:
            self.assertIn(row["class"], f.CLASSES, row)
            reason = self.doc["reasons"][row["reason"]]
            self.assertEqual(reason["class"], row["class"], row)
            self.assertEqual(row.get("lane"), reason.get("lane"), row)
            if row.get("lane"):
                self.assertEqual(row["class"], "refused", row)
                self.assertIn(row["lane"], f.LANES)

    def test_totals(self) -> None:
        rows = self.doc["items"]
        totals = self.doc["totals"]
        self.assertEqual(totals["items"], len(rows))
        for c in f.CLASSES:
            self.assertEqual(totals[c], sum(r["class"] == c for r in rows))

    def test_every_kind_present(self) -> None:
        self.assertEqual({r["kind"] for r in self.doc["items"]}, set(f.KINDS))

    def test_written_probes_name_items(self) -> None:
        keys = {(r["kind"], r["name"]) for r in self.doc["items"]}
        for key in f.written_probes():
            self.assertIn(key, keys)


if __name__ == "__main__":
    unittest.main()
