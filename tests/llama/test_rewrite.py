#!/usr/bin/env python3
"""Acceptance-boundary and reproduction checks for the retained q5 IR rewrite.

The default tests build a three-site synthetic module from the committed proof
fixture. Optional --actual-source and --reference-target paths also check a
complete externally compiled module and its previously selected native input.
All CLI output is written to temporary directories and removed on completion.
"""

import argparse
import copy
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path

import rewrite as matcher

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1] / "tools"))
from irlean import hashing, proc  # noqa: E402

FIXTURE = HERE.parent / "real/llama_q5_bitspread.ll"
ACTUAL_SOURCE: Path | None = None
REFERENCE_TARGET: Path | None = None


def synthetic_module():
    fixture = FIXTURE.read_text()
    header, rest = fixture.split("define <32 x i8> @src(i32 %x) {\nentry:\n", 1)
    source_body, _ = rest.split("  ret <32 x i8> %out\n}", 1)
    lines = [
        header.rstrip(),
        "",
        f"define <32 x i8> @{matcher.DEFAULT_FUNCTION}(i32 %a, i32 %b, i32 %c) {{",
        "entry:",
    ]
    for index, operand in enumerate(["%a", "%b", "%c"]):
        lines.extend(
            re.sub(
                matcher.SSA,
                lambda match, operand=operand, index=index: (
                    operand if match[0] == "%x" else f"{match[0]}.{index}"
                ),
                source_body,
            ).splitlines()
        )
    lines.extend(["  ret <32 x i8> %out.2", "}"])
    return "\n".join(lines) + "\n"


class BitspreadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = synthetic_module()
        cls.source = cls.text.encode()
        cls.target, cls.helper, cls.witness = matcher.prepare(cls.source, {matcher.DEFAULT_FUNCTION}, 3)
        cls.site = cls.witness["sites"][0]

    def prepare_text(self, text, functions=None, count=3):
        return matcher.prepare(text.encode(), functions or {matcher.DEFAULT_FUNCTION}, count)

    def mutate_instruction(self, index, old, new):
        line = self.site["original"][index]
        self.assertIn(old, line)
        self.assertEqual(self.text.count(line), 1)
        return self.text.replace(line, line.replace(old, new, 1), 1)

    def test_extracted_helper_equals_committed_proof_fixture(self):
        self.assertEqual(self.helper.encode(), FIXTURE.read_bytes())
        self.assertEqual(self.witness["actual_sites"], 3)
        self.assertEqual(self.witness["selected_functions"], [matcher.DEFAULT_FUNCTION])

    def test_actual_ir_reproduction(self):
        if ACTUAL_SOURCE is None:
            self.skipTest("no optional --actual-source supplied")
        target, helper, _ = matcher.prepare(ACTUAL_SOURCE.read_bytes(), {matcher.DEFAULT_FUNCTION}, 3)
        self.assertEqual(helper.encode(), FIXTURE.read_bytes())
        if REFERENCE_TARGET is not None:
            self.assertEqual(target.encode(), REFERENCE_TARGET.read_bytes())

    def test_every_unrelated_line_is_preserved(self):
        patches = {site["original"][-1]: site["replacement"] for site in self.witness["sites"]}
        dropped = {line for site in self.witness["sites"] for line in site["dropped_uselistorders"]}
        expected = []
        for line in self.text.splitlines():
            if line in patches:
                expected.extend(patches[line])
            elif line not in dropped:
                expected.append(line)
        self.assertEqual(self.target, "\n".join(expected) + "\n")
        for site in self.witness["sites"]:
            for producer in site["original"][:-1]:
                self.assertIn(producer, self.target)

    def test_unrelated_users_of_input_and_old_mask_survive(self):
        inserted = "  %irlean.test.other = xor i32 %a, 17"
        old_mask_user = "  %irlean.test.mask = xor <32 x i1> %mask.0, splat (i1 true)"
        first = self.site["original"][0]
        compare = self.site["original"][4]
        text = self.text.replace(first, first + "\n" + inserted, 1)
        text = text.replace(compare, compare + "\n" + old_mask_user, 1)
        target, helper, _ = self.prepare_text(text)
        self.assertIn(inserted, target)
        self.assertIn(old_mask_user, target)
        self.assertIn(compare, target)
        self.assertEqual(helper, self.helper)

    def test_wrong_shuffle_lane_is_rejected(self):
        text = self.mutate_instruction(2, "<i32 0, i32 0,", "<i32 1, i32 0,")
        with self.assertRaisesRegex(ValueError, "expected exactly 3 rewrite sites, found 2"):
            self.prepare_text(text)

    def test_wrong_complement_mask_is_rejected(self):
        text = self.mutate_instruction(3, "<i8 -2,", "<i8 -3,")
        with self.assertRaisesRegex(ValueError, "expected exactly 3 rewrite sites, found 2"):
            self.prepare_text(text)

    def test_poison_changing_opcode_flags_are_rejected(self):
        for index, old, new in [(3, " = or ", " = or disjoint "), (4, " = icmp eq ", " = icmp samesign eq ")]:
            with self.subTest(flag=new):
                text = self.mutate_instruction(index, old, new)
                with self.assertRaisesRegex(ValueError, "expected exactly 3 rewrite sites, found 2"):
                    self.prepare_text(text)

    def test_wrong_input_width_is_rejected(self):
        text = self.mutate_instruction(0, ", i32 %a,", ", i16 %a,")
        with self.assertRaisesRegex(ValueError, "expected exactly 3 rewrite sites, found 2"):
            self.prepare_text(text)

    def test_implicit_and_big_endian_layouts_are_rejected(self):
        layout, _ = matcher.module_layout(self.text)
        old = f'target datalayout = "{layout}"'
        for replacement in [
            "",
            'target datalayout = ""',
            f'target datalayout = "E{layout[1:]}"',
            f'target datalayout = "{layout}-E"',
            old + "\n" + old,
        ]:
            with (
                self.subTest(layout=replacement),
                self.assertRaisesRegex(ValueError, "explicit little-endian"),
            ):
                self.prepare_text(self.text.replace(old, replacement, 1))

    def test_unmodeled_instruction_metadata_is_rejected(self):
        line = self.site["original"][3]
        text = self.text.replace(line, line + ", !annotation !999999", 1)
        with self.assertRaisesRegex(ValueError, "expected exactly 3 rewrite sites, found 2"):
            self.prepare_text(text)

    def test_fresh_name_collision_is_rejected(self):
        first = self.site["original"][0]
        text = self.text.replace(first, first + "\n  %irlean.bitspread.0.mask = add i32 0, 0", 1)
        with self.assertRaisesRegex(ValueError, "fresh SSA prefix already appears"):
            self.prepare_text(text)

    def test_unselected_function_is_untouched(self):
        begin = self.text.index("define <32 x i8> @" + matcher.DEFAULT_FUNCTION + "(")
        end = self.text.index("\n}", begin) + 2
        clone = self.text[begin:end].replace("@" + matcher.DEFAULT_FUNCTION + "(", "@untouched_clone(", 1)
        target, helper, witness = self.prepare_text(self.text + "\n" + clone + "\n")
        self.assertTrue(target.endswith(clone + "\n"))
        self.assertEqual(helper, self.helper)
        self.assertEqual(witness["actual_sites"], 3)

    def test_exact_count_and_function_set_are_required(self):
        with self.assertRaisesRegex(ValueError, "expected exactly 4"):
            self.prepare_text(self.text, count=4)
        with self.assertRaisesRegex(ValueError, "differs from selected functions"):
            self.prepare_text(self.text, {matcher.DEFAULT_FUNCTION, "unused_selected_function"})

    def test_different_extracted_dags_cannot_share_a_helper(self):
        sites = copy.deepcopy(self.witness["sites"])
        sites[1]["normalized_source"][3] = sites[1]["normalized_source"][3].replace("<i8 -2,", "<i8 -3,", 1)
        with self.assertRaisesRegex(ValueError, "do not normalize"):
            matcher.helper_ir(*matcher.module_layout(self.text), sites)

    def test_cli_override_hashes_and_no_writes_on_rejection(self):
        with tempfile.TemporaryDirectory(prefix="irlean-bitspread-test-") as tmp:
            directory = Path(tmp)
            source = directory / "input.ll"
            target = directory / "output.ll"
            helper = directory / "helpers/q5_bitspread.ll"
            witness_path = directory / "witness.json"
            source.write_text(
                self.text.replace("@" + matcher.DEFAULT_FUNCTION + "(", "@selected_alternative(", 1)
            )
            command = [
                sys.executable,
                str(HERE / "rewrite.py"),
                str(source),
                str(target),
                "--function",
                "selected_alternative",
                "--expect-sites",
                "3",
                "--helpers-dir",
                str(helper.parent),
                "--witness",
                str(witness_path),
            ]
            result = proc.run(command)
            self.assertEqual(result.exit, 0, result.err)
            witness = json.loads(witness_path.read_text())
            self.assertEqual(witness["selected_functions"], ["selected_alternative"])
            for field, path in [
                ("source_sha256", source),
                ("target_sha256", target),
                ("helper_sha256", helper),
            ]:
                self.assertEqual(witness[field], hashing.sha256_file(path))
            self.assertEqual(witness["helper_ir"].encode(), helper.read_bytes())
            witness_hash = witness.pop("witness_sha256")
            self.assertEqual(witness_hash, hashing.sha256(matcher.canonical_json(witness)))
            originals = [path.read_bytes() for path in [target, helper, witness_path]]
            command[command.index("--expect-sites") + 1] = "4"
            failed = proc.run(command)
            self.assertNotEqual(failed.exit, 0)
            self.assertIn("expected exactly 4 rewrite sites, found 3", failed.err)
            self.assertEqual(originals, [path.read_bytes() for path in [target, helper, witness_path]])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--actual-source", type=Path)
    parser.add_argument("--reference-target", type=Path)
    options, remaining = parser.parse_known_args()
    if options.reference_target and not options.actual_source:
        parser.error("--reference-target requires --actual-source")
    ACTUAL_SOURCE, REFERENCE_TARGET = options.actual_source, options.reference_target
    unittest.main(argv=[sys.argv[0], *remaining])
