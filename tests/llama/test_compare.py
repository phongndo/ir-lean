#!/usr/bin/env python3
"""Portable mutation checks for the exact-logit comparator; no model or native build is needed."""

import hashlib
import json
import re
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import compare as comparator


class CaptureComparisonTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="irlean-capture-test-")
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        self.left, self.right = directory / "left", directory / "right"
        self.metadata = {
            "format": "llama-completion-exact-v1",
            "endianness": "little",
            "n_vocab": 3,
            "prompt_tokens": 2,
            "sampled_tokens": 2,
            "logit_rows": 2,
            "logits_bytes": 24,
        }
        self.payloads = {
            # Include both signed zeros and a quiet NaN: equality is of bytes, not float values.
            "logits.f32": struct.pack("<6I", 0, 0x80000000, 0x3F800000, 0x7FC00000, 0x40000000, 0xC0000000),
            "tokens.i32": struct.pack("<2i", 2, 1),
            "positions.i32": struct.pack("<2i", 2, 3),
            "prompt.i32": struct.pack("<2i", 1, 2),
        }
        self.write_capture(self.left)
        self.write_capture(self.right)

    def write_capture(self, prefix):
        comparator.capture_path(prefix, "json").write_text(json.dumps(self.metadata) + "\n")
        for suffix, content in self.payloads.items():
            comparator.capture_path(prefix, suffix).write_bytes(content)

    def write_metadata(self, prefix, metadata):
        comparator.capture_path(prefix, "json").write_text(json.dumps(metadata) + "\n")

    def flip_bit(self, suffix, offset=0):
        path = comparator.capture_path(self.right, suffix)
        data = bytearray(path.read_bytes())
        data[offset] ^= 1
        path.write_bytes(data)

    def test_identical_complete_captures(self):
        result = comparator.compare(self.left, self.right)
        self.assertTrue(result["bitwise_equal"])
        self.assertEqual(result["metadata"], self.metadata)
        self.assertEqual(
            result["sha256"],
            {suffix: hashlib.sha256(content).hexdigest() for suffix, content in self.payloads.items()},
        )

    def test_one_bit_fp32_change_is_rejected(self):
        # Flip the low mantissa bit of 1.0; a numerical-tolerance comparison could overlook this.
        self.flip_bit("logits.f32", 8)
        with self.assertRaisesRegex(ValueError, r"logits\.f32 mismatch at byte 8"):
            comparator.compare(self.left, self.right)

    def test_token_position_and_prompt_changes_are_rejected(self):
        for suffix in ("tokens.i32", "positions.i32", "prompt.i32"):
            with self.subTest(suffix=suffix):
                self.write_capture(self.right)
                self.flip_bit(suffix)
                with self.assertRaisesRegex(ValueError, re.escape(suffix) + " mismatch at byte 0"):
                    comparator.compare(self.left, self.right)

    def test_truncation_and_appended_data_are_rejected(self):
        for suffix, original in self.payloads.items():
            for content in (original[:-1], original + b"\x00"):
                with self.subTest(suffix=suffix, length=len(content)):
                    self.write_capture(self.right)
                    comparator.capture_path(self.right, suffix).write_bytes(content)
                    with self.assertRaisesRegex(ValueError, r"expected \d+ bytes, found \d+"):
                        comparator.compare(self.left, self.right)

    def test_invalid_metadata_is_rejected_even_when_both_captures_match(self):
        mutations = [("format", "unknown"), ("endianness", "big")]
        for key in ("n_vocab", "prompt_tokens", "sampled_tokens", "logit_rows", "logits_bytes"):
            mutations.extend((key, value) for value in (0, -1, True, 2.0, "2"))
        for key, value in mutations:
            with self.subTest(key=key, value=value):
                metadata = self.metadata | {key: value}
                self.write_metadata(self.left, metadata)
                self.write_metadata(self.right, metadata)
                with self.assertRaises(ValueError):
                    comparator.compare(self.left, self.right)

    def test_inconsistent_shape_metadata_is_rejected(self):
        for update, message in (
            ({"sampled_tokens": 1}, "each sampled token must have a logits row"),
            ({"logits_bytes": 20}, "logits byte count disagrees with its shape"),
            ({"n_vocab": 4, "logits_bytes": 32}, "expected 32 bytes, found 24"),
        ):
            with self.subTest(update=update):
                self.write_metadata(self.right, self.metadata | update)
                with self.assertRaisesRegex(ValueError, message):
                    comparator.compare(self.left, self.right)

    def test_missing_metadata_and_missing_payload_are_rejected(self):
        metadata = self.metadata.copy()
        del metadata["n_vocab"]
        self.write_metadata(self.right, metadata)
        with self.assertRaises(KeyError):
            comparator.compare(self.left, self.right)
        self.write_capture(self.right)
        comparator.capture_path(self.right, "logits.f32").unlink()
        with self.assertRaises(FileNotFoundError):
            comparator.compare(self.left, self.right)

    def test_cli_reports_success_and_fails_closed_on_corruption(self):
        command = [sys.executable, str(Path(comparator.__file__)), str(self.left), str(self.right)]
        success = subprocess.run(command, text=True, capture_output=True, check=False)
        self.assertEqual(success.returncode, 0, success.stderr)
        self.assertTrue(json.loads(success.stdout)["bitwise_equal"])
        self.flip_bit("logits.f32", 8)
        failure = subprocess.run(command, text=True, capture_output=True, check=False)
        self.assertEqual(failure.returncode, 1)
        self.assertEqual(failure.stdout, "")
        self.assertIn("logits.f32 mismatch at byte 8", failure.stderr)


if __name__ == "__main__":
    unittest.main()
