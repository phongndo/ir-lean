#!/usr/bin/env python3
"""Checks campaign/o1 without LLVM or Lean: that the committed pin, pipeline, families, evidence and ledger
agree, that pipelines and traces are read right, that only a `bound` verdict linked to the captured IR counts,
that nothing makes O1 complete, and that measurements are in the right units and stop at their limits.

usage: campaign/o1/test_o1.py
"""

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import measure
import o1

TRACE = """Running pass: SimplifyCFGPass on f (4 instructions)
*** IR Dump At Start ***
; ModuleID = '<stdin>'
define i32 @f(i32 noundef %x) {
  %a = add i32 %x, 0
  ret i32 %a
}
*** IR Dump After SimplifyCFGPass on f omitted because no change ***
Running pass: InstCombinePass on f (2 instructions)
Running analysis: DominatorTreeAnalysis on f
*** IR Dump After InstCombinePass on f ***
; ModuleID = '<stdin>'
define i32 @f(i32 noundef %x) {
  ret i32 %x
}
Running pass: LoopSimplifyPass on f (1 instruction)
*** IR Dump After LoopSimplifyPass on f omitted because no change ***
Running pass: PrintModulePass on [module]
"""


def leaf(pos: str, name: str, cls: str, unit: str = "function") -> dict:
    return {"pos": pos, "name": name, "spec": name, "class": cls, "unit": unit, "family": "f", "replay": []}


class Units(unittest.TestCase):
    def test_maxrss_is_bytes_on_macos_and_kib_on_linux(self) -> None:
        with mock.patch.object(measure.sys, "platform", "darwin"):
            self.assertEqual(measure.maxrss_mib(300 << 20), 300)
        with mock.patch.object(measure.sys, "platform", "linux"):
            self.assertEqual(measure.maxrss_mib(300 << 10), 300)

    def test_a_cap_stops_the_whole_tree(self) -> None:
        argv = [sys.executable, "-c", "import time; x = bytearray(400 << 20); time.sleep(30)"]
        r = measure.run(argv, label="cap", timeout=60, cap_mb=100, interval=0.05)
        self.assertEqual(r["outcome"], "resource_limit")
        self.assertLess(r["wall_s"], 30)

    def test_a_timeout_is_not_a_success(self) -> None:
        r = measure.run(
            [sys.executable, "-c", "import time; time.sleep(30)"], label="t", timeout=1, cap_mb=None
        )
        self.assertEqual(r["outcome"], "time_limit")

    def test_a_child_peak_is_counted(self) -> None:
        child = "import subprocess, sys; subprocess.run([sys.executable, '-c', 'x = bytearray(200 << 20)'])"
        r = measure.run([sys.executable, "-c", child], label="child", timeout=60, cap_mb=None)
        self.assertEqual(r["outcome"], "ok")
        self.assertGreater(r["peak_process_mb"], 190)


class Pipeline(unittest.TestCase):
    def setUp(self) -> None:
        self.pin = next(iter(o1.read_json(o1.PIN)["hosts"].values()))
        self.text = self.pin["pipeline"]["text"]

    def test_parse_reads_back_the_printed_text(self) -> None:
        def show(e: dict) -> str:
            inner = f"({','.join(show(c) for c in e['children'])})" if e["children"] is not None else ""
            return o1.spec_of(e) + inner

        elements = [o1.parse_element(e) for e in o1.split_top(self.text)]
        self.assertEqual(",".join(show(e) for e in elements), self.text)

    def test_units_and_replay(self) -> None:
        leaves = {x["pos"]: x for x in o1.read_json(o1.PIPELINE)["leaves"]}
        lis = next(x for x in leaves.values() if x["name"] == "loop-instsimplify")
        self.assertEqual(lis["unit"], "loop")
        self.assertEqual(lis["replay"][0], "function(loop-mssa(loop-instsimplify))")
        self.assertEqual(o1.unit_of(["cgscc", "devirt<4>"]), "cgscc")
        self.assertEqual(o1.replay_specs("globalopt", []), ["globalopt"])

    def test_every_pass_has_exactly_one_family(self) -> None:
        families = o1.read_json(o1.FAMILIES)
        fam = o1.family_of(families)
        for x in o1.read_json(o1.PIPELINE)["leaves"]:
            self.assertIn(x["name"], fam)
        twice = copy.deepcopy(families)
        twice["families"]["cfg"]["passes"].append("instcombine")
        with self.assertRaises(ValueError):
            o1.family_of(twice)

    def test_unbalanced_pipelines_are_refused(self) -> None:
        for bad in ("function(instcombine", "instcombine>"):
            with self.assertRaises(ValueError):
                [o1.parse_element(e) for e in o1.split_top(bad)]


class Trace(unittest.TestCase):
    def test_steps_carry_the_ir_before_and_after(self) -> None:
        leaves = [leaf("1", "simplifycfg", "SimplifyCFGPass"), leaf("2", "instcombine", "InstCombinePass")]
        found = o1.attribute(o1.parse_trace(TRACE), leaves, {"LoopSimplifyPass": "loop-simplify"})
        self.assertEqual(len(found["steps"]), 1)
        step = found["steps"][0]
        self.assertEqual((step["pos"], step["name"]), ("2", "instcombine"))
        self.assertIn("add i32", step["before"])
        self.assertNotIn("add i32", step["after"])
        self.assertEqual(found["final"], step["after"])
        self.assertEqual(found["invocation"], ["PrintModulePass"])
        self.assertEqual([r["name"] for r in found["runs"] if r["implicit"]], ["loop-simplify"])
        self.assertEqual(found["analyses"], {"DominatorTreeAnalysis": 1})

    def test_comment_only_differences(self) -> None:
        a = "b:                ; preds = %x, %y\n  ret i32 0\n"
        b = "b:                ; preds = %y, %x\n  ret i32 0\n"
        self.assertEqual(o1.without_comments(a), o1.without_comments(b))
        self.assertNotEqual(o1.without_comments(a), o1.without_comments(a.replace("0", "1")))


class Ledger(unittest.TestCase):
    """Synthetic evidence, in a directory of its own."""

    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.patch = mock.patch.object(o1, "EVIDENCE", Path(self.dir.name))
        self.patch.start()
        self.pipeline = o1.read_json(o1.PIPELINE)
        self.families = o1.read_json(o1.FAMILIES)
        steps = [
            {"k": k, "pos": "11.2", "name": "instcombine", "family": "peephole-int", "blockers": []}
            | {"before_sha256": f"b{k}", "after_sha256": f"a{k}"}
            for k in (1, 2, 3, 4, 5)
        ]
        self.capture = {"case": "c", "steps": steps, "input_sha256": "in", "o1_sha256": "out"}

    def tearDown(self) -> None:
        self.patch.stop()
        self.dir.cleanup()

    def bundle(self, label: str, src: str, tgt: str) -> None:
        d = Path(self.dir.name) / "c" / "bundles" / label
        d.mkdir(parents=True)
        art = {"input": {"sha256": src}, "tgt_ir": {"sha256": tgt}}
        (d / "manifest.json").write_text(json.dumps({"artifacts": art}))

    def test_only_linked_bound_verdicts_count(self) -> None:
        self.bundle("s01", "b1", "a1")
        self.bundle("s02", "b2", "not-a2")
        verdicts = [
            {"label": "s01", "step": 1, "status": "bound", "reason": "replayed"},
            {"label": "s02", "step": 2, "status": "bound", "reason": "replayed"},
            {"label": "s03", "step": 3, "status": "unknown", "reason": "time_limit"},
            {"label": "s04", "step": 4, "status": "unsupported", "reason": "trusted_promise"},
            {"label": "s05", "step": 5, "status": "proved", "reason": "made_up"},
        ]
        ledger = o1.derive_ledger(self.pipeline, self.families, [self.capture], {"c": verdicts})
        counts = ledger["corpus"]["verdicts"]
        self.assertEqual(counts["bound"], 1)
        self.assertEqual(counts["bound_unlinked"], 1)
        self.assertEqual(counts["unknown"], 1)
        self.assertEqual(counts["unsupported"], 1)
        self.assertEqual(counts["error"], 1)
        self.assertEqual(ledger["passes"]["instcombine"]["steps_bound"], 1)
        self.assertTrue(ledger["cases"]["c"]["chain_to_output"].startswith("broken at step 2"))
        self.assertIs(ledger["complete"], False)
        self.assertEqual(ledger["discharged"], dict.fromkeys(ledger["discharged"], 0))
        self.assertEqual(ledger["lemmas"]["checked"], 0)

    def test_a_whole_run_bound_to_other_ir_is_not_evidence(self) -> None:
        self.bundle("o1", "in", "something-else")
        verdicts = [{"label": "o1", "step": None, "status": "bound", "reason": "replayed"}]
        ledger = o1.derive_ledger(self.pipeline, self.families, [self.capture], {"c": verdicts})
        self.assertEqual(ledger["corpus"]["whole_run_verdicts"], {"bound_unlinked": 1})

    def test_every_step_bound_is_still_not_complete(self) -> None:
        verdicts = []
        for k in range(1, 6):
            self.bundle(f"s{k:02d}", f"b{k}", f"a{k}")
            verdicts.append({"label": f"s{k:02d}", "step": k, "status": "bound", "reason": "replayed"})
        ledger = o1.derive_ledger(self.pipeline, self.families, [self.capture], {"c": verdicts})
        self.assertTrue(ledger["cases"]["c"]["chain_to_output"].startswith("every step bound"))
        self.assertIs(ledger["complete"], False)
        self.assertEqual(ledger["passes"]["instcombine"]["all-input"], "open")


class Committed(unittest.TestCase):
    def test_the_committed_files_agree(self) -> None:
        self.assertEqual(o1.check_consistency(), [])

    def test_every_report_names_the_level(self) -> None:
        for path in (o1.PIN, o1.PIPELINE, o1.LEDGER, *sorted(o1.EVIDENCE.glob("*/capture.json"))):
            data = o1.read_json(path)
            self.assertEqual((data["level"], data["spec"]), ("O1", "default<O1>"), path)


if __name__ == "__main__":
    unittest.main()
