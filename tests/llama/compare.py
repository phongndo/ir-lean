#!/usr/bin/env python3
"""Require complete captures and compare every raw FP32 bit, token ID and position."""

import argparse
import json
import sys
from pathlib import Path

sys.path.append(str(Path(__file__).resolve().parents[2] / "tools"))
from irlean import hashing


def capture_path(prefix, suffix):
    return Path(f"{prefix}.{suffix}")


def check(prefix):
    metadata = json.loads(capture_path(prefix, "json").read_text())
    if metadata["format"] != "llama-completion-exact-v1" or metadata["endianness"] != "little":
        raise ValueError(f"{prefix}: unexpected capture format")
    for key in ("n_vocab", "prompt_tokens", "sampled_tokens", "logit_rows", "logits_bytes"):
        if type(metadata[key]) is not int or metadata[key] <= 0:
            raise ValueError(f"{prefix}: {key} must be a positive integer")
    if metadata["sampled_tokens"] != metadata["logit_rows"]:
        raise ValueError(f"{prefix}: each sampled token must have a logits row")
    sizes = {
        "logits.f32": 4 * metadata["n_vocab"] * metadata["logit_rows"],
        "tokens.i32": 4 * metadata["sampled_tokens"],
        "positions.i32": 4 * metadata["logit_rows"],
        "prompt.i32": 4 * metadata["prompt_tokens"],
    }
    if metadata["logits_bytes"] != sizes["logits.f32"]:
        raise ValueError(f"{prefix}: logits byte count disagrees with its shape")
    for suffix, expected in sizes.items():
        path = capture_path(prefix, suffix)
        actual = path.stat().st_size
        if actual != expected:
            raise ValueError(f"{path}: expected {expected} bytes, found {actual}")
    return metadata, sizes


def compare(left, right):
    left_meta, sizes = check(left)
    right_meta, right_sizes = check(right)
    if left_meta != right_meta or sizes != right_sizes:
        raise ValueError(f"capture manifests differ: {left_meta} != {right_meta}")
    hashes = {}
    for suffix, expected in sizes.items():
        digest = hashing.new()
        with capture_path(left, suffix).open("rb") as a, capture_path(right, suffix).open("rb") as b:
            offset = 0
            while True:
                av, bv = a.read(1024 * 1024), b.read(1024 * 1024)
                if av != bv:
                    mismatch = next(
                        (index for index, (x, y) in enumerate(zip(av, bv, strict=False)) if x != y),
                        min(len(av), len(bv)),
                    )
                    raise ValueError(f"{suffix} mismatch at byte {offset + mismatch}")
                if not av:
                    break
                digest.update(av)
                offset += len(av)
        if offset != expected:
            raise ValueError(f"{suffix}: size changed while comparing, expected {expected}, read {offset}")
        hashes[suffix] = digest.hexdigest()
    return {"bitwise_equal": True, "metadata": left_meta, "sha256": hashes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    args = parser.parse_args()
    try:
        result = compare(args.left, args.right)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"compare: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
