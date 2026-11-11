#!/usr/bin/env python3
"""Checks tools/x86_rank.py without the network, a compiler or Lean: that calls are counted and declarations
aren't, that a call's own types say whether it's an integer one, that an intrinsic's family is its
instruction, and that the committed ranking, tests/x86_rank/ranking.json, is of this pin, names only the pin's
intrinsics, and is what docs/x86-intrinsics.md holds, with a changed ranking, pin or document each refused.

usage: tests/x86_rank_test.py
"""

import copy
import importlib.util
import sys
import unittest
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


rank = load("x86_rank", ROOT / "tools" / "x86_rank.py")

IR = """
declare <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8>, <16 x i8>)
declare <4 x float> @llvm.x86.sse.max.ps(<4 x float>, <4 x float>)

define <16 x i8> @f(<16 x i8> %a, <16 x i8> %b, <4 x float> %x) {
  %r = tail call <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8> %a, <16 x i8> %b)
  %s = call <16 x i8> @llvm.x86.ssse3.pshuf.b.128(<16 x i8> %r, <16 x i8> %b)
  %m = call <4 x float> @llvm.x86.sse.max.ps(<4 x float> %x, <4 x float> %x)
  ret <16 x i8> %s
}

define <8 x i32> @g(<8 x i32> %a, ptr %p, <8 x i1> %k) {
  %r = call <8 x i32> @llvm.x86.avx512.mask.compress.v8i32(<8 x i32> %a, <8 x i32> %a, <8 x i1> %k)
  %l = call <8 x i32> @llvm.masked.load.v8i32.p0(ptr %p, i32 1, <8 x i1> %k, <8 x i32> %r)
  ret <8 x i32> %l
}
"""


class Counting(unittest.TestCase):
    def test_calls_count_and_declarations_dont(self) -> None:
        self.assertEqual(
            rank.count_calls(IR),
            {
                ("llvm.x86.ssse3.pshuf.b.128", "integer"): {"f": 2},
                ("llvm.x86.sse.max.ps", "float"): {"f": 1},
                ("llvm.x86.avx512.mask.compress.v8i32", "integer"): {"g": 1},
                ("llvm.masked.load.v8i32.p0", "other"): {"g": 1},
            },
        )

    def test_a_family_is_the_instruction(self) -> None:
        for name, family in {
            "llvm.x86.sse2.packsswb.128": "PACKSSWB",
            "llvm.x86.avx2.packsswb": "PACKSSWB",
            "llvm.x86.avx512.packsswb.512": "PACKSSWB",
            "llvm.x86.ssse3.pmadd.ub.sw.128": "PMADDUBSW",
            "llvm.x86.avx512.pmaddubs.w.512": "PMADDUBSW",
            "llvm.x86.avx2.permd": "VPERMD",
            "llvm.x86.avx512.permvar.si.512": "VPERMD",
            "llvm.x86.pclmulqdq.256": "PCLMULQDQ",
            "llvm.x86.aesni.aesenc": "AESENC",
            # On MMX's registers, so apart from the form on XMM ones.
            "llvm.x86.ssse3.pshuf.b": "MMX PSHUFB",
            "llvm.x86.mmx.padd.b": "MMX PADDB",
        }.items():
            self.assertEqual(rank.family(name), family, name)

    def test_an_overloaded_name_is_its_intrinsic(self) -> None:
        known = {"llvm.x86.avx512.mask.compress": "refused", "llvm.masked.load": "refused"}
        self.assertEqual(
            rank.base("llvm.x86.avx512.mask.compress.v8i32", known), "llvm.x86.avx512.mask.compress"
        )
        self.assertEqual(rank.base("llvm.masked.load.v8i32.p0", known), "llvm.masked.load")
        self.assertIsNone(rank.base("llvm.x86.made.up", known))


class Committed(unittest.TestCase):
    def setUp(self) -> None:
        self.record, self.doc = rank.load()
        self.text = rank.DOC.read_text()

    def test_the_ranking_is_what_the_document_holds(self) -> None:
        self.assertEqual(rank.problems(self.record, self.doc, self.text), [])

    def test_every_project_compiled_every_file(self) -> None:
        for p in self.record["projects"]:
            self.assertEqual(p["not_compiled"], [], p["name"])
            self.assertGreater(p["files"], 0, p["name"])

    def test_a_modeled_form_changes_the_table(self) -> None:
        # The model gaining or losing an intrinsic has to show in the document.
        doc = copy.deepcopy(self.doc)
        item = next(i for i in doc["items"] if i["name"] == "llvm.x86.avx2.pmadd.wd")
        self.assertEqual(item["class"], "modeled")
        item["class"] = "refused"
        self.assertIn("table", " ".join(rank.problems(self.record, doc, self.text)))

    def test_a_changed_count_is_refused(self) -> None:
        record = copy.deepcopy(self.record)
        calls = next(p for p in record["projects"] if p["name"] == "libaom")["calls"]
        calls["llvm.x86.sse2.pmadd.wd|integer"]["calls"] += 1
        self.assertIn("table", " ".join(rank.problems(record, self.doc, self.text)))

    def test_another_pin_is_refused(self) -> None:
        record = copy.deepcopy(self.record)
        record["pin"] = {"tag": "llvmorg-0.0.0", "commit": "0" * 40}
        self.assertIn("llvmorg-0.0.0", " ".join(rank.problems(record, self.doc, self.text)))

    def test_an_intrinsic_the_pin_lacks_is_refused(self) -> None:
        record = copy.deepcopy(self.record)
        record["integer"].append("llvm.x86.made.up")
        record["projects"][0]["calls"]["llvm.x86.also.made.up|integer"] = {"calls": 1, "functions": 1}
        wrong = " ".join(rank.problems(record, self.doc, self.text))
        self.assertIn("llvm.x86.made.up isn't", wrong)
        self.assertIn("llvm.x86.also.made.up|integer", wrong)

    def test_a_document_without_the_table_is_refused(self) -> None:
        self.assertIn("markers", " ".join(rank.problems(self.record, self.doc, "# x86 intrinsics\n")))


if __name__ == "__main__":
    unittest.main()
