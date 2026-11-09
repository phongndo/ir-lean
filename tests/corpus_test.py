#!/usr/bin/env python3
"""Checks tools/corpus/capture.py without LLVM or Lean: that pipelines and traces are read right, and that a
corpus refuses a toolchain other than its own. With the pinned opt on PATH, as in `nix develop`, it also
captures one seed. tests/irlean_test.py checks tools/measure.py and the library it runs on. docs/corpus.md.

usage: tests/corpus_test.py
"""

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, pins, proc  # noqa: E402


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


capture = load("capture", ROOT / "tools" / "corpus" / "capture.py")
PIPELINE = json.loads(capture.INVENTORY.read_text())["pipelines"]["opt"][capture.SPEC]["pipeline"]

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


def leaf(pos: str, name: str, cls: str) -> dict:
    return {"pos": pos, "name": name, "spec": name, "class": cls, "unit": "function", "replay": []}


def pin(**changes: Any) -> dict:
    p = {
        "opt": {"path": "/opt", "sha256": "a" * 64, "version": []},
        "llvm": {"tag": "llvmorg-1.0", "repo_tag": "llvmorg-1.0", "repo_commit": "c"},
        "spec": "default<O1>",
        "mtriple": "x86_64-unknown-linux-gnu",
        "pipeline": {"text": "instcombine", "sha256": "b" * 64, "inventory_match": True},
    }
    for key, value in changes.items():
        part, _, field = key.partition("__")
        if field:
            p[part] = p[part] | {field: value}
        else:
            p[part] = value
    return p


class Pipeline(unittest.TestCase):
    def test_parse_reads_back_the_printed_text(self) -> None:
        def show(e: dict) -> str:
            inner = f"({','.join(show(c) for c in e['children'])})" if e["children"] is not None else ""
            return capture.spec_of(e) + inner

        elements = [capture.parse_element(e) for e in capture.split_top(PIPELINE)]
        self.assertEqual(",".join(show(e) for e in elements), PIPELINE)

    def test_every_pass_has_a_class_to_match_the_trace_with(self) -> None:
        leaves, names = capture.pipeline_passes(PIPELINE)
        self.assertEqual([x["name"] for x in leaves if x["class"] is None], [])
        self.assertEqual(names["ModuleInlinerWrapperPass"], "inliner-wrapper")
        self.assertEqual(names["LCSSAPass"], "lcssa")

    def test_units_and_replay(self) -> None:
        leaves, _ = capture.pipeline_passes(PIPELINE)
        lis = next(x for x in leaves if x["name"] == "loop-instsimplify")
        self.assertEqual(lis["unit"], "loop")
        self.assertEqual(lis["replay"][0], "function(loop-mssa(loop-instsimplify))")
        self.assertEqual(capture.unit_of(["cgscc", "devirt<4>"]), "cgscc")
        self.assertEqual(capture.replay_specs("globalopt", []), ["globalopt"])

    def test_unbalanced_pipelines_are_refused(self) -> None:
        for bad in ("function(instcombine", "instcombine>"):
            with self.assertRaises(ValueError):
                [capture.parse_element(e) for e in capture.split_top(bad)]

    def test_every_pipeline_in_the_inventory_is_read(self) -> None:
        # Such as default<O0> and lto<O1>, whose coro-cond wraps passes of its own.
        pipelines = json.loads(capture.INVENTORY.read_text())["pipelines"]["opt"]
        texts = [p["pipeline"] for p in pipelines.values() if "pipeline" in p]
        self.assertGreater(len(texts), 10)
        for text in texts:
            capture.flatten([capture.parse_element(e) for e in capture.split_top(text)])


class Trace(unittest.TestCase):
    def test_steps_carry_the_ir_before_and_after(self) -> None:
        leaves = [leaf("1", "simplifycfg", "SimplifyCFGPass"), leaf("2", "instcombine", "InstCombinePass")]
        found = capture.attribute(capture.parse_trace(TRACE), leaves, {"LoopSimplifyPass": "loop-simplify"})
        self.assertEqual(len(found["steps"]), 1)
        step = found["steps"][0]
        self.assertEqual((step["pos"], step["name"], step["implicit"]), ("2", "instcombine", False))
        self.assertIn("add i32", step["before"])
        self.assertNotIn("add i32", step["after"])
        self.assertEqual(found["start"], step["before"])
        self.assertEqual(found["final"], step["after"])

    def test_comment_only_differences(self) -> None:
        a = "b:                ; preds = %x, %y\n  ret i32 0\n"
        b = "b:                ; preds = %y, %x\n  ret i32 0\n"
        self.assertEqual(capture.without_comments(a), capture.without_comments(b))
        self.assertNotEqual(capture.without_comments(a), capture.without_comments(a.replace("0", "1")))

    def test_a_wrapper_is_not_a_step(self) -> None:
        trace = "\n".join(
            [
                "*** IR Dump At Start ***",
                "declare void @g()",
                "Running pass: CoroConditionalWrapper on [module]",
                "Running pass: GlobalDCEPass on [module]",
                "*** IR Dump After GlobalDCEPass on [module] ***",
                "; empty",
                "*** IR Dump After CoroConditionalWrapper on [module] ***",
                "; empty",
            ]
        )
        found = capture.attribute(capture.parse_trace(trace), [leaf("1", "globaldce", "GlobalDCEPass")], {})
        self.assertEqual([s["name"] for s in found["steps"]], ["globaldce"])


class Pin(unittest.TestCase):
    def test_the_repo_pin_holds(self) -> None:
        self.assertEqual(capture.pin_problems(pin(), None), [])
        self.assertEqual(capture.pin_problems(pin(), pin()), [])
        self.assertEqual(capture.pin_problems(pin(pipeline__inventory_match=None), None), [])

    def test_another_toolchain_is_refused(self) -> None:
        for changed, words in (
            (pin(llvm__tag="llvmorg-2.0"), "not the repo's pin"),
            (pin(pipeline__inventory_match=False), "isn't the inventory's"),
        ):
            self.assertRegex(" ".join(capture.pin_problems(changed, None)), words)

    def test_a_corpus_keeps_its_toolchain(self) -> None:
        for recorded in (
            pin(opt__sha256="c" * 64),
            pin(pipeline__sha256="d" * 64),
            pin(spec="default<O2>"),
            pin(mtriple="aarch64-unknown-linux-gnu"),
        ):
            problems = capture.pin_problems(pin(), recorded)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("the corpus there was made with", problems[0])


def unpinned() -> str | None:
    """Why the live tests can't run, or None when the repo's opt is on PATH."""
    tag = pins.llvm()["tag"]
    try:
        r = proc.run(["opt", "--version"])
    except FileNotFoundError:
        return "no opt on PATH"
    return None if f"LLVM version {tag.removeprefix('llvmorg-')}\n" in r.out else f"opt isn't {tag}"


UNPINNED = unpinned()


@unittest.skipIf(UNPINNED, UNPINNED or "")
class Live(unittest.TestCase):
    """One seed through the pinned opt, which takes well under a second."""

    def capture(self, out: Path, *extra: str) -> proc.Ran:
        argv = [sys.executable, str(ROOT / "tools" / "corpus" / "capture.py"), "capture", "--out", str(out)]
        return proc.run([*argv, *extra])

    def test_a_seed_is_captured_and_its_steps_replay_alone(self) -> None:
        seed = capture.SEEDS / "sub_add_cancel.ll"
        with tempfile.TemporaryDirectory() as d:
            out = Path(d)
            r = self.capture(out, str(seed))
            self.assertEqual(r.exit, 0, r.err)
            record = json.loads((out / "sub_add_cancel" / "capture.json").read_text())
            self.assertEqual(record["status"], "captured")
            self.assertEqual(record["input_sha256"], hashing.sha256(seed.read_bytes()))
            self.assertIn("instcombine", [s["name"] for s in record["steps"]])
            for s in record["steps"]:
                self.assertTrue(s["reproduced"], s)
                for side in ("before", "after"):
                    data = (out / "sub_add_cancel" / s[side]).read_bytes()
                    self.assertEqual(hashing.sha256(data), s[f"{side}_sha256"])
            # Each step follows the last, from the input as opt prints it to the output.
            for prev, s in zip(record["steps"], record["steps"][1:], strict=False):
                self.assertEqual(prev["after_sha256"], s["before_sha256"])
            self.assertEqual(record["steps"][-1]["after_sha256"], record["output_sha256"])

            # A corpus made by another opt isn't added to.
            pinned = json.loads((out / "pin.json").read_text())
            pinned["opt"]["sha256"] = "0" * 64
            (out / "pin.json").write_text(json.dumps(pinned))
            r = self.capture(out, str(seed))
            self.assertEqual(r.exit, 1)
            self.assertIn("the corpus there was made with opt", r.err)

    def test_an_input_for_another_target_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            ll = Path(d) / "arm.ll"
            ll.write_text('target triple = "aarch64-unknown-linux-gnu"\ndefine i32 @f() {\n  ret i32 0\n}\n')
            r = self.capture(Path(d) / "out", str(ll))
            self.assertEqual(r.exit, 1)
            record = json.loads((Path(d) / "out" / "arm" / "capture.json").read_text())
            self.assertEqual(record["status"], "refused")


if __name__ == "__main__":
    unittest.main()
