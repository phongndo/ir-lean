#!/usr/bin/env python3
"""Tier-1 proof tests: runs one property of one function in LLVM IR on generated inputs, and answers in JSON.

A property is a Lean statement about the function ir-lean generates, as `tools/verify.py` takes one. This runs
it on inputs, edge cases and bit patterns first and then seeded random ones, and stops at the first that makes
it false. It shrinks that input, has the Lean kernel check a theorem that the statement is false there, or
else has `tools/verify.py` confirm it by running the model's compiled code, and stores it, so the next run of
the same property tries it first. docs/proof-tests.md has the design, the contract and what was measured.

Tier 1 never proves anything. `passed_tier1` means no input it tried made the statement false: tested, not
proved.

usage: tools/prooftest/prooftest.py run [REQUEST.json|-] [--ir FILE | --c FILE [--cflags FLAGS]]
                                    [--function F] [--statement S | --equivalent-to G [--arguments A,B,..]
                                    [--max-length N]] [--namespace NS] [--seed N]
                                    [--max-inputs N] [--timeout S] [--memory-mb MB] [--input-timeout S]
                                    [--store DIR | --no-store] [--no-shrink] [--work-dir DIR] [--pretty]
       tools/prooftest/prooftest.py capabilities [--pretty]

With `-`, the request is read from stdin, with paths relative to the working directory, as irl's MCP server
sends it.
"""

from __future__ import annotations

import argparse
import contextlib
import importlib.util
import itertools
import json
import math
import os
import queue
import random
import re
import secrets
import shutil
import sys
import threading
import time
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, NoReturn

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, lean, proc, schemas  # noqa: E402
from irlean import verdict as core  # noqa: E402


def load_verify() -> Any:
    """tools/verify.py, by path: tests/verify.py has the same module name."""
    spec = importlib.util.spec_from_file_location("irlean_verify_tool", ROOT / "tools" / "verify.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


verify: Any = load_verify()

HARNESS = Path(__file__).resolve().parent / "Harness.lean"
RUNS = ROOT / "build" / "prooftest" / "runs"
DEFAULT_STORE = ROOT / "build" / "prooftest" / "store"
# Runs kept under build/prooftest/runs when no --work-dir is given. An explicit one is never deleted.
RUNS_KEPT = 20

SCHEMA = schemas.PROOFTEST
REQUEST_SCHEMA = schemas.PROOFTEST_REQUEST
STORE_SCHEMA = schemas.PROOFTEST_STORE

DEFAULTS: dict[str, Any] = {
    "seed": 0,
    "max_inputs": 10_000,
    # A pass needs at least this many inputs that meet the hypotheses, unless every input was tried.
    "min_satisfied": 10,
    "shrink": True,
    "timeout_seconds": 300,
    "memory_mb": 4000,
    "input_timeout_seconds": 2.0,
    # How many times the harness is started again after an input that didn't finish, or crashed it.
    "restarts": 2,
    "kernel_timeout_seconds": 60.0,
    # Steps of IRLean.run the kernel follows when it confirms a counterexample.
    "fuel": 1_000_000,
    "kernel_heartbeats": 2_000_000,
    # `auto` asks tools/verify.py only when the kernel couldn't confirm. `always` asks it too.
    "verify_confirm": "auto",
    # The most bytes an equivalence's buffers hold.
    "max_length": 256,
}

STATUSES = {
    "passed_tier1": "Tested, not proved: no input tried made the statement false. Inputs not tried may",
    "counterexample": "The statement is false on the input in `counterexample`, in the model, confirmed as "
    "`counterexample.evidence` says",
    "vacuous": "No input tried meets the hypotheses, so nothing was tested. Perhaps they can't be met",
    "unknown": "Nothing was decided: the property couldn't run, a run didn't finish, or a limit stopped it",
}
EXIT_CODES = {"passed_tier1": 0, "unknown": 1, "counterexample": 2, "vacuous": 3}

# Every reason, and the status it gives. A new one goes at the end of its status, and keeps its meaning.
REASONS: dict[str, tuple[str, str]] = {
    "sampled": (
        "passed_tier1",
        "Every planned input ran, none made the statement false, and enough met the hypotheses",
    ),
    "exhaustive": (
        "passed_tier1",
        "Every input the binders' types allow ran, and none made the statement false. This was compiled "
        "evaluation, not a proof",
    ),
    "kernel_refuted": (
        "counterexample",
        "The kernel checked a theorem that the statement is false at this input",
    ),
    "compiled_evaluation": (
        "counterexample",
        "tools/verify.py's compiled evaluation confirmed it. The kernel didn't check it",
    ),
    "no_input_meets_hypotheses": ("vacuous", "Every input tried made a hypothesis false"),
    "too_few_satisfying": ("unknown", "Fewer than `min_satisfied` inputs met the hypotheses"),
    "input_timeout": (
        "unknown",
        "An input's run didn't finish in `input_timeout_seconds`, and nothing failed",
    ),
    "evaluation_crashed": ("unknown", "Evaluating an input stopped Lean, and nothing failed"),
    "time_limit": ("unknown", "`limits.timeout_seconds` ran out before the planned inputs had run"),
    "memory_limit": ("unknown", "Lean ran past `limits.memory_mb`"),
    "unconfirmed": (
        "unknown",
        "An input failed in the search, and neither the kernel nor tools/verify.py confirmed it",
    ),
    "confirmation_disagrees": (
        "unknown",
        "An input failed in the search, and the kernel or tools/verify.py found the statement true there. "
        "A bug in "
        "this tool, Lean's compiler or IRLean's code",
    ),
    "binder_unsupported": (
        "unknown",
        "A binder isn't `BitVec w`, `IRLean.Val w`, `Bool`, or a buffer, pointer or length from "
        "IRLean.Ptf. A `Mem` or a `PtrVal` is one",
    ),
    "undecidable": ("unknown", "Lean can't decide the statement at an input"),
    "statement_unsupported": (
        "unknown",
        "The statement uses a hypothesis's proof, or needs an instance Lean can't find",
    ),
    "statement_invalid": ("unknown", "The statement doesn't elaborate"),
    "statement_not_about_target": ("unknown", "The statement doesn't name the generated function itself"),
    "function_unsupported": ("unknown", "The emitter left the function out, for the reason given"),
    "function_not_found": ("unknown", "The module has no such function"),
    "compile_failed": ("unknown", "clang couldn't compile the C input"),
    "ir_invalid": ("unknown", "LLVM couldn't read the IR"),
    "input_not_found": ("unknown", "A file the request names doesn't exist"),
    "toolchain_missing": ("unknown", "ir-lean, Lean, the IRLean library, clang or opt isn't there"),
    "generated_module_failed": ("unknown", "Lean rejected what ir-lean generated, which is a bug in ir-lean"),
    "tool_failed": ("unknown", "A tool crashed or answered in a way this doesn't understand"),
    "invalid_request": ("unknown", "The request is malformed. `detail` says how"),
    "internal_error": ("unknown", "A bug in this tool"),
    "model_stopped": (
        "unknown",
        "A function the property needs an answer from stopped the model on an input, which says nothing "
        "there, and nothing failed",
    ),
}
# What tools/verify.py answers that stops a proof test before it starts, as the reason here. Anything else is
# tool_failed.
FROM_VERIFY = {
    reason
    for reason, (status, _) in REASONS.items()
    if status == "unknown"
    and reason
    not in {
        "too_few_satisfying",
        "input_timeout",
        "evaluation_crashed",
        "unconfirmed",
        "confirmation_disagrees",
        "binder_unsupported",
        "undecidable",
        "statement_unsupported",
        "model_stopped",
    }
}
EVIDENCE = {
    "kernel": "A theorem `¬ statement`, built from the input and checked by the Lean kernel. It rests on the "
    "axioms "
    "listed, and on the elaborated statement meaning what was written",
    "compiled_evaluation": "tools/verify.py elaborated the statement again, substituted the input, and "
    "decided it by "
    "running the model's compiled code. That trusts Lean's compiler and runtime, as native_decide does",
}

# What each argument of a function in an equivalence is.
ROLES = ("value", "buffer", "length")

REQUEST_FIELDS = {
    "schema": "Optional. Must be " + REQUEST_SCHEMA,
    "input": '{"ir": PATH} for .ll or .bc, or {"c": PATH, "cflags": [...]}, as tools/verify.py takes it',
    "function": "The LLVM name, without @",
    "namespace": "The Lean namespace of the generated module. Defaults to the input's name",
    "statement": "The property: a Lean proposition naming the generated function, over `BitVec w`, "
    "`IRLean.Val w`, `Bool` and `IRLean.Ptf.Buffer n` binders, with a `IRLean.Ptf.Pointer` and a "
    "`IRLean.Ptf.Length` into a buffer, and hypotheses as implications. Give this or `equivalence`",
    "equivalence": "Instead of `statement`: {with, arguments, max_length}. The property that `function` "
    "and the function `with`, in the same module, give the same result and leave the same memory on the "
    "same inputs. `arguments` says what each argument is, `value`, `buffer` or `length`, by default a "
    "buffer for a pointer, its length for an i64 right after it, and a value for any other integer. "
    "Buffers hold at most `max_length` bytes, default 256",
    "seed": "The seed for random inputs. Default 0",
    "max_inputs": "How many inputs to plan, after stored ones. Default 10,000",
    "min_satisfied": "How many inputs have to meet the hypotheses for a pass. Default 10",
    "shrink": "Whether to shrink a counterexample. Default true",
    "store": "A directory of failing inputs, tried first and added to. null for none. "
    "Default build/prooftest/store",
    "verify_confirm": "auto, always or never: when tools/verify.py confirms a counterexample. Default auto",
    "limits": "{timeout_seconds, memory_mb, input_timeout_seconds}",
}

# REQUEST_FIELDS as a JSON Schema, which irl's MCP server gives as `ptf_run`'s input. load_request is still
# what decides a request is valid: this is what a client checks before it asks. irl/schema_test.go checks
# its properties are REQUEST_FIELDS.
REQUEST_JSON_SCHEMA: dict[str, Any] = {
    "type": "object",
    "properties": {
        name: {**schema, "description": REQUEST_FIELDS[name]}
        for name, schema in {
            "schema": {"const": REQUEST_SCHEMA},
            "input": verify.REQUEST_JSON_SCHEMA["properties"]["input"],
            "function": {"type": "string", "minLength": 1},
            "namespace": {"type": "string", "minLength": 1},
            "statement": {"type": "string", "minLength": 1},
            "equivalence": {
                "type": "object",
                "properties": {
                    "with": {"type": "string", "minLength": 1},
                    "arguments": {"type": "array", "items": {"enum": list(ROLES)}},
                    "max_length": {"type": "integer", "minimum": 0, "maximum": 1 << 20},
                },
                "required": ["with"],
                "additionalProperties": False,
            },
            "seed": {"type": "integer", "minimum": 0, "maximum": 2**63},
            "max_inputs": {"type": "integer", "minimum": 1, "maximum": 10_000_000},
            "min_satisfied": {"type": "integer", "minimum": 1, "maximum": 10_000_000},
            "shrink": {"type": "boolean"},
            "store": {"type": ["string", "null"], "minLength": 1},
            "verify_confirm": {"enum": ["auto", "always", "never"]},
            "limits": {
                "type": "object",
                "properties": {
                    "timeout_seconds": {"type": "number", "minimum": 1, "maximum": 86400},
                    "memory_mb": {"type": "integer", "minimum": 64, "maximum": 1048576},
                    "input_timeout_seconds": {"type": "number", "minimum": 0.05, "maximum": 3600},
                },
                "additionalProperties": False,
            },
        }.items()
    },
    "required": ["input", "function"],
    "additionalProperties": False,
}


class Stop(Exception):
    """Ends a run early, with a reason from REASONS."""

    def __init__(self, reason: str, detail: str) -> None:
        super().__init__(detail)
        self.reason = reason
        self.detail = detail


# Values and how they're generated


def width_of(binder: dict[str, Any]) -> int:
    return int(binder.get("width", 1))


# A buffer, a pointer into it and a length past the pointer are generated together. A buffer's value is a
# tuple of bytes, a pointer's its offset into the buffer's allocation, and a length's a number.
MEMORY = {"buffer", "pointer", "length"}


def is_memory(binder: dict[str, Any]) -> bool:
    return binder["kind"] in MEMORY


def domain_size(binder: dict[str, Any]) -> int:
    if binder["kind"] == "bool":
        return 2
    if is_memory(binder):
        # Never every input: a buffer of one byte already has 256.
        return 1 << 64 if binder["kind"] == "buffer" else 1
    size = 1 << width_of(binder)
    return size + 1 if binder["kind"] == "val" else size


def encode(binder: dict[str, Any], value: int | None) -> int:
    """A value as the harness takes it: a natural number, with poison as `2 ^ w`."""
    if value is None:
        return 1 << width_of(binder)
    return int(value)


def wire(binders: list[dict[str, Any]], values: tuple) -> list[int]:
    """An input as the harness takes it: an entry for each binder, and after them each buffer's length and
    bytes,
    with the buffer's entry saying where they start."""
    out: list[int] = []
    tail: list[int] = []
    for b, v in zip(binders, values, strict=True):
        if b["kind"] == "buffer":
            out.append(len(binders) + len(tail))
            tail += [len(v), *v]
        else:
            out.append(encode(b, v))
    return out + tail


def jsonable(binders: list[dict[str, Any]], values: tuple) -> list[Any]:
    """An input as JSON: poison as `2 ^ w`, as the harness takes it, and a buffer as a list of bytes."""
    return [list(v) if b["kind"] == "buffer" else encode(b, v) for b, v in zip(binders, values, strict=True)]


def lean_term(binder: dict[str, Any], value: Any) -> str:
    """A value as a Lean term, as tools/verify.py takes a witness. A pointer's or a length's type names the
    buffer
    it's into, which Lean fills in for `_`."""
    if binder["kind"] == "bool":
        return "true" if value else "false"
    if binder["kind"] == "buffer":
        return f"IRLean.Ptf.Buffer.ofList {binder['max']} [{', '.join(f'{b}#8' for b in value)}]"
    if binder["kind"] == "pointer":
        return f"IRLean.Ptf.Pointer.ofNat _ {value}"
    if binder["kind"] == "length":
        return f"IRLean.Ptf.Length.ofNat _ {value}"
    w = width_of(binder)
    if binder["kind"] == "val":
        return "none" if value is None else f"some {value}#{w}"
    return f"{value}#{w}"


def shown(binder: dict[str, Any], value: Any) -> str:
    """A value for people: hex for wide ones, and poison by name. A buffer's bytes in hex, with how many."""
    if binder["kind"] == "buffer":
        return f"{len(value)} bytes: {bytes(value).hex(' ') if value else '(none)'}"
    if binder["kind"] == "pointer":
        return f"{value} bytes in"
    if binder["kind"] == "length":
        return str(value)
    if value is None:
        return "poison"
    if binder["kind"] == "bool":
        return "true" if value else "false"
    w = width_of(binder)
    return f"{value:#x}#{w}" if w > 8 else f"{value}#{w}"


def repeat_byte(byte: int, w: int) -> int:
    return int.from_bytes(bytes([byte]) * ((w + 7) // 8), "little") & ((1 << w) - 1)


def edges(binder: dict[str, Any]) -> list[int | None]:
    """The values most likely to tell code apart: zero, one, all ones, the signed limits, and neighbors."""
    if binder["kind"] == "bool":
        return [0, 1]
    w = width_of(binder)
    values: list[int | None] = [0]
    if w > 0:
        m = (1 << w) - 1
        top = 1 << (w - 1)
        values = [v & m for v in (0, 1, m, top, top - 1, 2, m - 1, top + 1, 3)]
    if binder["kind"] == "val":
        values.insert(2, None)
    return list(dict.fromkeys(values))


def patterns(binder: dict[str, Any]) -> list[int | None]:
    """Bit patterns: repeated bytes, single bits, runs of ones from either end, and all ones but one bit."""
    if binder["kind"] == "bool" or width_of(binder) == 0:
        return []
    w = width_of(binder)
    m = (1 << w) - 1
    values: list[int | None] = [
        repeat_byte(b, w) for b in (0x55, 0xAA, 0x0F, 0xF0, 0x33, 0xCC, 0x01, 0x80, 0x7F, 0xFE, 0x11)
    ]
    values += [1 << i for i in range(w)]
    values += [(1 << i) - 1 for i in range(1, w)]
    values += [m ^ ((1 << i) - 1) for i in range(1, w)]
    values += [m ^ (1 << i) for i in range(w)]
    return list(dict.fromkeys(values))


def random_value(binder: dict[str, Any], rng: random.Random) -> int | None:
    """A value from a mix: uniform, small, near all ones, few bits set, few bits clear, or near an edge."""
    if binder["kind"] == "bool":
        return rng.getrandbits(1)
    if binder["kind"] == "val" and rng.random() < 0.05:
        return None
    w = width_of(binder)
    m = (1 << w) - 1
    if w == 0:
        return 0
    pick = rng.random()
    if pick < 0.3:
        return rng.getrandbits(w)
    if pick < 0.5:
        return rng.getrandbits(rng.randint(0, w))
    if pick < 0.65:
        return m - rng.getrandbits(rng.randint(0, w))
    sparse = 0
    for _ in range(rng.randint(1, 3)):
        sparse |= 1 << rng.randrange(w)
    if pick < 0.8:
        return sparse
    if pick < 0.9:
        return m ^ sparse
    base = rng.choice([v for v in edges(binder) + patterns(binder) if v is not None])
    return (base + rng.randint(-3, 3)) & m


def every_value(binder: dict[str, Any]) -> list[int | None]:
    """Every value of a scalar binder, in order, poison last."""
    if binder["kind"] == "bool":
        return [0, 1]
    return [*range(1 << width_of(binder)), *([None] if binder["kind"] == "val" else [])]


# Buffers

# Lengths a buffer's edges take, up to its most: the block sizes of SSE, AVX2 and AVX-512 and each side of
# them.
LENGTHS = (0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 31, 32, 33, 47, 48, 63, 64, 65, 127, 128, 129, 255, 256, 257)
LENGTHS += (511, 512, 513, 1023, 1024, 1025, 4095, 4096, 4097)
# How far an unaligned pointer is from alignment, and the lengths that get one.
MISALIGNED = (1, 3, 4, 8, 15)
MISALIGNED_LENGTHS = (1, 16, 17, 32, 33, 64, 65)
PATTERN_BYTES = (0x55, 0xAA, 0x0F, 0xF0, 0x01, 0x80, 0x7F, 0xFE, 0x11)


def ascending(n: int) -> tuple[int, ...]:
    """1, 2, 3, ...: no byte zero but every 256th, and each different from its neighbors, so a byte read from
    the
    wrong place, or left out, shows."""
    return tuple((j + 1) & 0xFF for j in range(n))


class Scalar:
    """One `BitVec`, `Val` or `Bool` binder, generated as tier 1 always has."""

    def __init__(self, index: int, binder: dict[str, Any]) -> None:
        self.indices = [index]
        self.binder = binder

    def edges(self) -> list[tuple]:
        return [(v,) for v in edges(self.binder)]

    def patterns(self) -> list[tuple]:
        return [(v,) for v in patterns(self.binder)]

    def draw(self, rng: random.Random) -> tuple:
        return (random_value(self.binder, rng),)

    def domain(self) -> int:
        return domain_size(self.binder)

    def every(self) -> list[tuple]:
        return [(v,) for v in every_value(self.binder)]

    def bytes_phase(self) -> bool:
        return self.binder["kind"] != "bool" and width_of(self.binder) > 8

    def candidates(self, value: tuple) -> list[tuple]:
        return [(c,) for c in shrink_candidates(self.binder, value[0])]


class Memory:
    """A buffer binder, the pointers into its allocation, and the lengths past each pointer, generated
    together so
    every pointer is into the buffer and every length fits. A value is theirs in binder order."""

    def __init__(self, index: int, binders: list[dict[str, Any]]) -> None:
        self.buffer = index
        self.max = int(binders[index]["max"])
        self.pointers = [i for i, b in enumerate(binders) if b["kind"] == "pointer" and b.get("of") == index]
        self.lengths = {
            p: [i for i, b in enumerate(binders) if b["kind"] == "length" and b.get("of") == p]
            for p in self.pointers
        }
        self.indices = sorted([index, *self.pointers, *(i for ls in self.lengths.values() for i in ls)])

    def make(self, data: tuple[int, ...], offsets: dict[int, int], lengths: dict[int, int]) -> tuple:
        by_index = {self.buffer: tuple(data), **offsets, **lengths}
        return tuple(by_index[i] for i in self.indices)

    def split(self, value: tuple) -> tuple[tuple[int, ...], dict[int, int], dict[int, int]]:
        by_index = dict(zip(self.indices, value, strict=True))
        offsets = {p: by_index[p] for p in self.pointers}
        lengths = {i: by_index[i] for ls in self.lengths.values() for i in ls}
        return by_index[self.buffer], offsets, lengths

    def shape(self, offset: int, length: int, slack: int, content: Callable[[int], tuple[int, ...]]) -> tuple:
        """`offset` bytes before every pointer, `length` bytes past it, and `slack` more after."""
        data = content(offset + length + slack)
        return self.make(
            data,
            dict.fromkeys(self.pointers, offset),
            {i: length for ls in self.lengths.values() for i in ls},
        )

    def edges(self) -> list[tuple]:
        """The empty buffer, then each length at an aligned pointer, ascending and all ones, then the block
        sizes at unaligned pointers, then a length of 0 in a buffer that isn't empty, bytes past the end of
        what's read,
        and zeros."""
        n = self.max
        lengths = sorted({x for x in LENGTHS if x <= n} | {n, max(n - 1, 0)})
        ones: Callable[[int], tuple[int, ...]] = lambda k: (0xFF,) * k  # noqa: E731
        zeros: Callable[[int], tuple[int, ...]] = lambda k: (0,) * k  # noqa: E731
        out = [self.shape(0, 0, 0, ascending)]
        out += [self.shape(0, x, 0, ascending) for x in lengths]
        out += [self.shape(0, x, 0, ones) for x in lengths if x]
        out += [
            self.shape(k, x, 0, ascending)
            for x in MISALIGNED_LENGTHS
            for k in MISALIGNED
            if k + x <= n and x <= n
        ]
        out += [self.shape(k, 0, s, ascending) for k, s in ((0, 16), (8, 8)) if k + s <= n]
        out += [self.shape(0, x, 1, ascending) for x in (15, 16, 63) if x + 1 <= n]
        out += [self.shape(0, x, 0, zeros) for x in (1, 16, 64, n) if 0 < x <= n]
        return list(dict.fromkeys(out))

    def patterns(self) -> list[tuple]:
        """Repeated bytes at the block sizes, then one byte set at each place in 64, which finds a lane that's
        wrong."""
        n = self.max
        out = [
            self.shape(0, x, 0, lambda k, b=b: (b,) * k)
            for x in (4, 16, 32, 64)
            if x <= n
            for b in PATTERN_BYTES
        ]
        width = min(n, 64)
        for j in range(width):
            out.append(self.shape(0, width, 0, lambda k, j=j: tuple(int(i == j) for i in range(k))))
        return list(dict.fromkeys(out))

    def draw(self, rng: random.Random) -> tuple:
        """A length that's uniform, near a multiple of a block size, or small; an aligned pointer half the
        time;
        sometimes bytes past the end; and bytes that are uniform, mostly zero, extremes, or all one byte."""
        n = self.max
        pick = rng.random()
        if pick < 0.35:
            length = rng.randint(0, n)
        elif pick < 0.75:
            block = rng.choice((4, 8, 16, 32, 64))
            length = min(max(block * rng.randint(0, max(n // block, 0)) + rng.randint(-2, 2), 0), n)
        else:
            length = rng.randint(0, min(n, 70))
        offset = 0 if rng.random() < 0.5 else rng.randint(0, min(63, n - length))
        room = n - length - offset
        slack = rng.randint(1, min(32, room)) if room >= 1 and rng.random() < 0.2 else 0
        total = offset + length + slack
        kind = rng.random()
        if kind < 0.6:
            data = tuple(rng.getrandbits(8) for _ in range(total))
        elif kind < 0.75:
            data = tuple(rng.getrandbits(8) if rng.random() < 0.1 else 0 for _ in range(total))
        elif kind < 0.9:
            data = tuple(rng.choice((0, 0xFF, 0x80, 0x7F, 0x01)) for _ in range(total))
        else:
            data = (rng.getrandbits(8),) * total
        offsets = {p: offset if k == 0 else rng.randint(0, total) for k, p in enumerate(self.pointers)}
        lengths = {
            i: length if k == 0 and j == 0 else rng.randint(0, total - offsets[p])
            for k, (p, ls) in enumerate(self.lengths.items())
            for j, i in enumerate(ls)
        }
        return self.make(data, offsets, lengths)

    def domain(self) -> int:
        return 1 << 64

    def every(self) -> list[tuple]:
        return []

    def bytes_phase(self) -> bool:
        return False

    def remove(self, value: tuple, start: int, count: int) -> tuple:
        """The bytes from `start` up to `start + count` taken out, with each pointer and the end of each
        length moved
        to where the same byte is, or to `start` if theirs is gone."""
        data, offsets, lengths = self.split(value)

        def moved(at: int) -> int:
            return at - count if at >= start + count else min(at, start)

        new_offsets = {p: moved(k) for p, k in offsets.items()}
        new_lengths = {
            i: moved(offsets[p] + lengths[i]) - new_offsets[p] for p, ls in self.lengths.items() for i in ls
        }
        return self.make(data[:start] + data[start + count :], new_offsets, new_lengths)

    def candidates(self, value: tuple) -> list[tuple]:
        """Shorter first: the whole buffer, halves and quarters of it, what's before each pointer and past
        each length, halves of what each length covers, and a byte at each end of it. Then simpler bytes: all
        zero,
        each nonzero byte zero, and the first nonzero byte smaller."""
        data, offsets, lengths = self.split(value)
        total = len(data)
        cuts = {
            (0, total),
            (0, total // 2),
            (total // 2, total - total // 2),
            (total - total // 4, total // 4),
        }
        cuts |= {(0, 1), (total - 1, 1)}
        for p, k in offsets.items():
            cuts.add((0, k))
            for i in self.lengths[p]:
                x = lengths[i]
                end = k + x
                cuts |= {(end, total - end), (k, x // 2), (k + x // 2, x - x // 2), (k, 1), (end - 1, 1)}
                cuts |= {(end - 16, 16), (k, 16)}
        out = [
            self.remove(value, start, count)
            for start, count in sorted(cuts)
            if count > 0 and start >= 0 and start + count <= total
        ]
        if any(data):
            out.append(self.make((0,) * total, offsets, lengths))
        for j, b in enumerate(data):
            if b:
                out.append(self.make((*data[:j], 0, *data[j + 1 :]), offsets, lengths))
        first = next((j for j, b in enumerate(data) if b), None)
        if first is not None:
            b = data[first]
            for smaller in (b >> 1, b & (b - 1), b - 1):
                out.append(self.make((*data[:first], smaller, *data[first + 1 :]), offsets, lengths))
        return list(dict.fromkeys(out))


def units_of(binders: list[dict[str, Any]]) -> list[Scalar | Memory]:
    """The binders as they're generated: each scalar alone, and each buffer with its pointers and lengths, in
    the
    order of their first binder."""
    units: list[Scalar | Memory] = []
    for i, b in enumerate(binders):
        if b["kind"] == "buffer":
            units.append(Memory(i, binders))
        elif not is_memory(b):
            units.append(Scalar(i, b))
    covered = {i for u in units for i in u.indices}
    if covered != set(range(len(binders))):
        raise Stop("binder_unsupported", "a pointer or a length that isn't into a buffer the statement binds")
    return units


def assemble(units: list[Scalar | Memory], parts: Iterable[tuple], size: int) -> tuple:
    """One input, from each unit's part of it."""
    out: list[Any] = [None] * size
    for unit, part in zip(units, parts, strict=True):
        for i, v in zip(unit.indices, part, strict=True):
            out[i] = v
    return tuple(out)


@dataclass
class Plan:
    """The inputs to try, in order, and where each came from."""

    inputs: list[tuple] = field(default_factory=list)
    phases: list[str] = field(default_factory=list)
    exhaustive: bool = False
    domain: int | None = None


# How long tools/verify.py gets to confirm a counterexample. Deciding one input takes it seconds, apart from
# setting up, unless the statement makes Lean try every value of an `∃`, which never ends.
VERIFY_CONFIRM_SECONDS = 60
# Inputs sent to Lean in one request: few at first, so an early failure isn't kept waiting while thousands of
# inputs are written and read, and four times as many each time after, up to the most.
FIRST_BATCH = 64
BATCH = 20_000
# The most tuples of edge values tried together before sampling them.
EDGE_PRODUCT_CAP = 512


def plan(binders: list[dict[str, Any]], seed: int, max_inputs: int, replay: Iterable[tuple] = ()) -> Plan:
    """Stored failures first, then edges, then bit patterns, then every byte, then random values, up to
    `max_inputs` after the stored ones. If every input fits in `max_inputs`, every input, edges and patterns
    first. A buffer, its pointers and their lengths count as one binder here, whose edges, patterns and random
    values `Memory` gives."""
    result = Plan()
    seen: set[tuple] = set()

    def add(phase: str, values: tuple) -> None:
        if values not in seen:
            seen.add(values)
            result.inputs.append(values)
            result.phases.append(phase)

    for values in replay:
        add("replay", tuple(values))
    budget = len(result.inputs) + max_inputs
    units = units_of(binders)
    domain = math.prod(u.domain() for u in units)
    result.domain = domain
    result.exhaustive = domain <= max_inputs
    if not binders:
        add("edges", ())
        return result

    def whole(parts: Iterable[tuple]) -> tuple:
        return assemble(units, parts, len(binders))

    rng = random.Random(seed)
    edge_sets = [u.edges() for u in units]
    product = math.prod(len(e) for e in edge_sets)
    if product <= EDGE_PRODUCT_CAP:
        for parts in itertools.product(*edge_sets):
            add("edges", whole(parts))
    else:
        # Every edge of each binder at least once, the rest of each tuple drawn from the other binders' edges.
        for i, edge_set in enumerate(edge_sets):
            for v in edge_set:
                add("edges", whole(v if j == i else rng.choice(e) for j, e in enumerate(edge_sets)))
        while sum(p == "edges" for p in result.phases) < EDGE_PRODUCT_CAP:
            add("edges", whole(rng.choice(e) for e in edge_sets))
    pattern_sets = [u.edges() + u.patterns() for u in units]
    for i, unit in enumerate(units):
        for k, v in enumerate(unit.patterns()):
            others = [ps[(k * 7 + j) % len(ps)] for j, ps in enumerate(pattern_sets)]
            others[i] = v
            add("patterns", whole(others))
    # The same value everywhere, for properties that relate the binders.
    kinds = {json.dumps({k: b.get(k) for k in ("kind", "width")}) for b in binders}
    if len(kinds) == 1 and len(binders) > 1 and all(isinstance(u, Scalar) for u in units):
        for v in pattern_sets[0]:
            add("patterns", whole(v for _ in units))
    # Every byte, for code over characters and small counts, with the other binders cycling through edges.
    for i, unit in enumerate(units):
        if not unit.bytes_phase():
            continue
        for v in range(256):
            others = [es[(v * 7 + j) % len(es)] for j, es in enumerate(edge_sets)]
            others[i] = (v,)
            add("bytes", whole(others))
    if result.exhaustive:
        # Every input, in order, after the edges and patterns. Poison last.
        for parts in itertools.product(*(u.every() for u in units)):
            add("exhaustive", whole(parts))
    else:
        attempts = 0
        while len(result.inputs) < budget and attempts < 20 * max_inputs:
            attempts += 1
            add("random", whole(u.draw(rng) for u in units))
    result.inputs = result.inputs[:budget]
    result.phases = result.phases[:budget]
    return result


# Shrinking


def simplicity(values: tuple) -> tuple:
    """Smaller is simpler: fewer bytes of buffers, then fewer bits in all, then smaller values. Poison is left
    as
    it is."""

    def bits(v: Any) -> int:
        return sum(b.bit_length() for b in v) if isinstance(v, tuple) else (v or 0).bit_length()

    size = sum(len(v) for v in values if isinstance(v, tuple))
    return (size, sum(bits(v) for v in values), tuple(-1 if v is None else v for v in values))


def shrink_candidates(binder: dict[str, Any], value: int | None) -> list[int | None]:
    """Simpler values to try in place of `value`."""
    if value is None or value == 0:
        return []
    if binder["kind"] == "bool":
        return [0]
    m = (1 << width_of(binder)) - 1
    top = value.bit_length() - 1
    out = [0, 1, value >> 1, value & (value - 1), value ^ (1 << top), value - 1, (-value) & m]
    out += [value ^ (1 << i) for i in range(top) if value >> i & 1]
    out += [value >> k for k in (2, 4, 8, 16, 32)]
    return [
        c for c in dict.fromkeys(out) if 0 <= c <= m and (c.bit_length(), c) < (value.bit_length(), value)
    ]


def shrink(
    start: tuple,
    binders: list[dict[str, Any]],
    still_fails: Callable[[list[tuple]], int | None],
    rounds: int = 200,
) -> tuple[tuple, int]:
    """Greedily replaces one binder's value at a time, or one buffer's with its pointers and lengths, with a
    simpler one that still fails, until none does. `still_fails` takes candidates, simplest first, and returns
    the index of the first that fails, or None. Deterministic: the same start and the same answers give the
    same
    result. Returns the input and how many steps it took."""
    units = units_of(binders)
    current, steps = tuple(start), 0
    for _ in range(rounds):
        candidates = []
        for unit in units:
            part = tuple(current[i] for i in unit.indices)
            for c in unit.candidates(part):
                t = list(current)
                for i, v in zip(unit.indices, c, strict=True):
                    t[i] = v
                if simplicity(tuple(t)) < simplicity(current):
                    candidates.append(tuple(t))
        candidates = sorted(dict.fromkeys(candidates), key=simplicity)
        if not candidates:
            break
        found = still_fails(candidates)
        if found is None:
            break
        current, steps = candidates[found], steps + 1
    return current, steps


# The store of failing inputs


def property_key(statement: str, binders: list[dict[str, Any]]) -> str:
    """Names a property by its elaborated statement and binders, and not by the code. So an input that once
    failed is tried again after the code changes, as Hypothesis keys its database by the test."""
    shape = [
        [b["name"], b["kind"], b.get("width"), *([b.get("max"), b.get("of")] if is_memory(b) else [])]
        for b in binders
    ]
    return hashing.sha256_text(json.dumps({"statement": statement, "binders": shape}, sort_keys=True))[:32]


def natural(v: Any) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0


def fits(binders: list[dict[str, Any]], values: list[Any]) -> bool:
    if len(values) != len(binders):
        return False
    for b, v in zip(binders, values, strict=True):
        if b["kind"] == "buffer":
            if (
                not isinstance(v, list | tuple)
                or len(v) > int(b["max"])
                or not all(natural(x) and x < 256 for x in v)
            ):
                return False
        elif b["kind"] == "pointer":
            buffer = values[b["of"]] if 0 <= b["of"] < len(values) else None
            if not natural(v) or not isinstance(buffer, list | tuple) or v > len(buffer):
                return False
        elif b["kind"] == "length":
            pointer = values[b["of"]] if 0 <= b["of"] < len(values) else None
            of = binders[b["of"]].get("of", -1) if 0 <= b["of"] < len(binders) else -1
            buffer = values[of] if 0 <= of < len(values) else None
            if not natural(v) or not natural(pointer) or not isinstance(buffer, list | tuple):
                return False
            if pointer + v > len(buffer):
                return False
        elif v is None:
            if b["kind"] != "val":
                return False
        elif not natural(v) or not v < domain_size(b) - (b["kind"] == "val"):
            return False
    return True


def stored_value(v: Any) -> Any:
    """A value as JSON keeps it: a buffer as a list."""
    return list(v) if isinstance(v, tuple) else v


def value_of(v: Any) -> Any:
    """A value as the plan keeps it: a buffer as a tuple, so an input can be a key."""
    return tuple(v) if isinstance(v, list) else v


class Store:
    """Failing inputs, one JSON file a property in a directory. Writes go through a rename, so a reader never
    sees a file half written."""

    KEPT = 100

    def __init__(self, directory: Path | None) -> None:
        self.directory = directory

    def path(self, key: str) -> Path | None:
        return self.directory / f"{key}.json" if self.directory else None

    def read(self, key: str) -> dict[str, Any]:
        path = self.path(key)
        if path is None or not path.exists():
            return {"entries": []}
        try:
            data = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            return {"entries": []}
        if (
            not isinstance(data, dict)
            or data.get("schema") != STORE_SCHEMA
            or not isinstance(data.get("entries"), list)
        ):
            return {"entries": []}
        return data

    def load(self, key: str, binders: list[dict[str, Any]]) -> list[tuple]:
        """The stored inputs that still fit the binders, newest first."""
        entries = self.read(key)["entries"]
        values = [e.get("values") for e in reversed(entries) if isinstance(e, dict)]
        return [tuple(value_of(x) for x in v) for v in values if isinstance(v, list) and fits(binders, v)]

    def add(self, key: str, entry: dict[str, Any], header: dict[str, Any]) -> bool:
        path = self.path(key)
        if path is None:
            return False
        data = self.read(key)
        entries = [e for e in data["entries"] if isinstance(e, dict) and e.get("values") != entry["values"]]
        entries = [*entries, entry][-self.KEPT :]
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(f".{path.name}.{os.getpid()}.{secrets.token_hex(4)}")
        temporary.write_text(
            json.dumps({"schema": STORE_SCHEMA, **header, "entries": entries}, indent=2) + "\n"
        )
        temporary.replace(path)
        return True


# The Lean harness


@dataclass
class Evaluated:
    """What one batch of inputs gave: 0, 1 or 2 for each input that finished, in order."""

    codes: list[int] = field(default_factory=list)
    # Nanoseconds from the start of the batch to each answer, as Lean measured them.
    nanos: list[int] = field(default_factory=list)
    batch_ns: int = 0
    # Why it stopped early, with the index of the input that didn't finish: input_timeout, evaluation_crashed,
    # memory_limit or time_limit.
    stopped: str | None = None
    stuck: int | None = None


class Harness:
    """tools/prooftest/Harness.lean, running as a server in one Lean process, with a memory watchdog."""

    def __init__(self, run: Run) -> None:
        self.run = run
        self.process: proc.Popen[str] | None = None
        self.answers: queue.Queue[str | None] = queue.Queue()
        # Set by the watchdog when Lean runs past the memory limit, and it kills Lean.
        self.over_memory = threading.Event()
        self.other: list[str] = []
        self.starts = 0
        # How the last harness process ended, once stop() ended it: what its answers rest on.
        self.ended: core.Step | None = None

    def start(self) -> dict[str, Any]:
        run = self.run
        self.starts += 1
        self.ended = None
        self.over_memory = threading.Event()
        self.answers = queue.Queue()
        directory = run.work / "harness"
        directory.mkdir(exist_ok=True)
        namespace = run.request["namespace"]
        source = directory / "Harness.lean"
        # The copy on ExecMem, if there is one, is imported too, for the search. Statements see the same
        # names.
        copy = f"import {run.exec_namespace}\n" if run.exec_namespace else ""
        source.write_text(
            f"import Lean\nimport IRLean\nimport {namespace}\n{copy}open IRLean {namespace}\n\n"
            + HARNESS.read_text()
        )
        config = directory / "config.json"
        config.write_text(
            json.dumps(
                {
                    "nonce": run.nonce,
                    "statement": run.request["statement"],
                    "generated": namespace,
                    "exec": run.exec_namespace,
                    "fuel": DEFAULTS["fuel"],
                    "kernel_heartbeats": DEFAULTS["kernel_heartbeats"],
                },
                ensure_ascii=False,
            )
        )
        verify_work = run.work / "verify"
        env = {
            **os.environ,
            "LEAN_PATH": f"{verify_work / 'lean'}{os.pathsep}{verify_work / 'library'}",
            "IRLEAN_PROOFTEST_CONFIG": str(config),
            # A panic in compiled code returns a default value and carries on, which could pass for an answer.
            "LEAN_ABORT_ON_PANIC": "1",
        }
        memory = run.request["limits"]["memory_mb"]
        argv = lean.argv(memory, f"--load-dynlib={verify.DYLIB}")
        argv += ["-Dinterpreter.prefer_native=true", str(source)]
        run.commands.append({"step": f"harness:{self.starts}", "argv": argv, "cwd": str(ROOT)})
        try:
            self.process = proc.spawn(
                argv,
                stdin=proc.PIPE,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                text=True,
                bufsize=1,
                cwd=ROOT,
                env=env,
            )
        except OSError as error:
            raise Stop("toolchain_missing", f"can't run lean: {error}") from error
        threading.Thread(target=self._read, args=(self.process, self.answers), daemon=True).start()
        threading.Thread(
            target=self._watch, args=(self.process, memory, self.over_memory), daemon=True
        ).start()
        answer = self._next(run.remaining())
        if answer is None:
            self.stop()
            raise Stop(self.limit() or "time_limit", "the harness didn't start in time")
        if answer == "":
            self.stop()
            if self.over_memory.is_set():
                raise Stop("memory_limit", f"Lean ran past {memory} MB starting the harness")
            raise Stop(
                "tool_failed", "the harness stopped before answering: " + "".join(self.other[-20:])[-2000:]
            )
        data = json.loads(answer)
        if data.get("kind") == "failure":
            self.stop()
            reason = data.get("reason", "internal_error")
            raise Stop(reason if reason in REASONS else "internal_error", str(data.get("detail", "")))
        if data.get("kind") != "ready":
            self.stop()
            raise Stop("internal_error", f"the harness answered {answer[:200]}")
        return data

    def limit(self) -> str | None:
        return "memory_limit" if self.over_memory.is_set() else None

    def _read(self, process: proc.Popen[str], answers: queue.Queue[str | None]) -> None:
        marker = f"IRLEAN_PROOFTEST {self.run.nonce} "
        assert process.stdout is not None
        for line in process.stdout:
            if line.startswith(marker):
                answers.put(line[len(marker) :].rstrip("\n"))
            elif len(self.other) < 200:
                self.other.append(line)
        answers.put("")

    def _watch(self, process: proc.Popen[str], memory_mb: int, over: threading.Event) -> None:
        while process.poll() is None:
            used = proc.rss_mb(process.pid)
            if used is not None and used > memory_mb:
                over.set()
                proc.kill_tree(process.pid)
                return
            time.sleep(0.05)

    def _next(self, timeout: float) -> str | None:
        """The next answer: None if `timeout` ran out, and "" if Lean stopped."""
        try:
            return self.answers.get(timeout=max(timeout, 0.0))
        except queue.Empty:
            return None

    def send(self, request: dict[str, Any]) -> None:
        assert self.process is not None and self.process.stdin is not None
        try:
            self.process.stdin.write(json.dumps(request) + "\n")
            self.process.stdin.flush()
        except (BrokenPipeError, OSError):
            pass

    def evaluate(self, inputs: list[list[int]], stop: bool, input_timeout: float) -> Evaluated:
        """Runs a batch, stopping at the first failure if `stop`. An input that takes longer than
        `input_timeout` stops the batch, and the harness with it."""
        out = Evaluated()
        if not inputs:
            return out
        self.send({"op": "eval", "inputs": inputs, "stop": stop})
        while True:
            remaining = self.run.remaining()
            answer = self._next(min(input_timeout, remaining))
            if answer is None:
                out.stopped = "time_limit" if remaining <= input_timeout else "input_timeout"
                out.stuck = len(out.codes)
                self.stop()
                return out
            if answer == "":
                self.wait()
                out.stopped = self.limit() or "evaluation_crashed"
                out.stuck = len(out.codes)
                return out
            if answer.startswith("r "):
                _, index, code, ns = answer.split()
                if int(index) != len(out.codes):
                    raise Stop("internal_error", f"the harness answered input {index} out of order")
                out.codes.append(int(code))
                out.nanos.append(int(ns))
                continue
            data = json.loads(answer)
            if data.get("kind") == "done":
                out.batch_ns = int(data["ns"])
                return out
            raise Stop("internal_error", f"the harness answered {answer[:200]}")

    def kernel(self, values: list[int], timeout: float) -> dict[str, Any]:
        self.send({"op": "kernel", "input": values})
        answer = self._next(min(timeout, self.run.remaining()))
        if answer is None:
            self.stop()
            return {"ok": False, "reason": "kernel_timeout", "detail": f"no answer in {timeout:.0f} s"}
        if answer == "":
            self.wait()
            return {"ok": False, "reason": self.limit() or "evaluation_crashed", "detail": "Lean stopped"}
        data = json.loads(answer)
        if data.get("kind") != "kernel":
            raise Stop("internal_error", f"the harness answered {answer[:200]}")
        return data

    def wait(self) -> None:
        if self.process is not None:
            with contextlib.suppress(proc.TimeoutExpired):
                self.process.wait(timeout=5)

    def stop(self) -> None:
        if self.process is None:
            return
        # Asked to quit, it returns, and exits 0. Its answers count only if it does.
        killed = False
        if self.process.poll() is None:
            self.send({"op": "quit"})
            try:
                self.process.wait(timeout=5)
            except proc.TimeoutExpired:
                killed = True
        proc.stop(self.process)
        limit = self.limit() or ("stopped" if killed else None)
        self.ended = core.Step("harness", self.process.returncode, limit, "".join(self.other[-50:]))
        self.process = None


# A run


@dataclass
class Run:
    request: dict[str, Any]
    work: Path
    tool: Path
    deadline: float
    started: float
    nonce: str = field(default_factory=lambda: secrets.token_hex(16))
    commands: list[dict[str, Any]] = field(default_factory=list)
    setup: dict[str, Any] | None = None
    ready: dict[str, Any] | None = None
    binders: list[dict[str, Any]] = field(default_factory=list)
    key: str | None = None
    stored: list[tuple] = field(default_factory=list)
    plan: Plan | None = None
    tried: int = 0
    satisfied: int = 0
    discarded: int = 0
    by_phase: dict[str, int] = field(default_factory=dict)
    undecided: list[dict[str, Any]] = field(default_factory=list)
    failing: dict[str, Any] | None = None
    counterexample: dict[str, Any] | None = None
    # How the processes that confirmed it ended: the harness that asked the kernel, and tools/verify.py's
    # evaluation of the witness.
    confirmed_by: dict[str, core.Step] = field(default_factory=dict)
    disagreement: str | None = None
    store_added: bool = False
    timing: dict[str, float] = field(default_factory=dict)
    stop: Stop | None = None
    limit_hit: str | None = None
    planned_all: bool = False
    # Which inputs met the hypotheses, by their place in the plan, kept for a property with memory.
    met: list[int] = field(default_factory=list)
    # The generated module's copy on ExecMem the search runs, if there is one, or why there isn't.
    exec_namespace: str | None = None
    exec_missing: str | None = None
    # For an equivalence: the two functions, their signature and what each argument is.
    equivalence: dict[str, Any] | None = None
    # Hypotheses, by their place, that are false only where a function stops the model, and that function. An
    # input that makes one false isn't discarded: it's counted here, by function, and is never part of a pass.
    model_hypotheses: dict[int, str] = field(default_factory=dict)
    model_stopped: dict[str, int] = field(default_factory=dict)

    def remaining(self) -> float:
        return self.deadline - time.monotonic()


def load_request(raw: Any, base: Path) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raise Stop("invalid_request", "the request must be a JSON object")
    unknown = sorted(set(raw) - set(REQUEST_FIELDS))
    if unknown:
        raise Stop(
            "invalid_request", f"unknown fields: {', '.join(unknown)}. Known: {', '.join(REQUEST_FIELDS)}"
        )
    if raw.get("schema", REQUEST_SCHEMA) != REQUEST_SCHEMA:
        raise Stop("invalid_request", f"schema must be {REQUEST_SCHEMA!r}")
    statement = raw.get("statement")
    equivalence = raw.get("equivalence")
    if (statement is None) == (equivalence is None):
        raise Stop("invalid_request", "give a statement, or an equivalence to build one, and not both")
    if statement is not None and (not isinstance(statement, str) or not statement.strip()):
        raise Stop("invalid_request", "statement must be a Lean proposition about the function")
    try:
        checked = verify.load_request(
            {k: raw[k] for k in ("input", "function", "namespace") if k in raw}
            # An equivalence's statement is built once the functions' signatures are known.
            | {"statement": statement if statement is not None else "True"},
            base,
        )
    except verify.Stop as stop:
        raise Stop("invalid_request", stop.detail) from stop
    request: dict[str, Any] = {
        "schema": REQUEST_SCHEMA,
        "input": checked["input"],
        "function": checked["function"],
        "namespace": checked["namespace"],
        "statement": checked["statement"] if statement is not None else None,
    }
    if equivalence is not None:
        request["equivalence"] = load_equivalence(equivalence, checked["function"])

    def number(key: str, low: int, high: int) -> int:
        value = raw.get(key, DEFAULTS[key])
        if not isinstance(value, int) or isinstance(value, bool) or not low <= value <= high:
            raise Stop("invalid_request", f"{key} must be a whole number from {low} to {high}")
        return value

    request["seed"] = number("seed", 0, 2**63)
    request["max_inputs"] = number("max_inputs", 1, 10_000_000)
    request["min_satisfied"] = number("min_satisfied", 1, 10_000_000)
    shrink_flag = raw.get("shrink", DEFAULTS["shrink"])
    if not isinstance(shrink_flag, bool):
        raise Stop("invalid_request", "shrink must be true or false")
    request["shrink"] = shrink_flag
    store = raw.get("store", str(DEFAULT_STORE))
    if store is not None and (not isinstance(store, str) or not store):
        raise Stop("invalid_request", "store must be a directory, or null")
    request["store"] = str((base / store).resolve()) if store is not None else None
    confirm = raw.get("verify_confirm", DEFAULTS["verify_confirm"])
    if confirm not in ("auto", "always", "never"):
        raise Stop("invalid_request", "verify_confirm must be auto, always or never")
    request["verify_confirm"] = confirm
    limits = raw.get("limits", {})
    if not isinstance(limits, dict) or set(limits) - {
        "timeout_seconds",
        "memory_mb",
        "input_timeout_seconds",
    }:
        raise Stop(
            "invalid_request", "limits can only have timeout_seconds, memory_mb and input_timeout_seconds"
        )
    timeout = limits.get("timeout_seconds", DEFAULTS["timeout_seconds"])
    memory = limits.get("memory_mb", DEFAULTS["memory_mb"])
    per_input = limits.get("input_timeout_seconds", DEFAULTS["input_timeout_seconds"])
    if not isinstance(timeout, int | float) or isinstance(timeout, bool) or not 1 <= timeout <= 86400:
        raise Stop("invalid_request", "limits.timeout_seconds must be between 1 and 86400")
    if not isinstance(memory, int) or isinstance(memory, bool) or not 64 <= memory <= 1048576:
        raise Stop("invalid_request", "limits.memory_mb must be a whole number between 64 and 1048576")
    if not isinstance(per_input, int | float) or isinstance(per_input, bool) or not 0.05 <= per_input <= 3600:
        raise Stop("invalid_request", "limits.input_timeout_seconds must be between 0.05 and 3600")
    request["limits"] = {"timeout_seconds": timeout, "memory_mb": memory, "input_timeout_seconds": per_input}
    return request


# Equivalence: a property built from two functions' signatures, with no spec written by hand

LLVM_NAME = re.compile(r"[A-Za-z0-9_.$-]+")


def load_equivalence(raw: Any, function: str) -> dict[str, Any]:
    if not isinstance(raw, dict) or set(raw) - {"with", "arguments", "max_length"}:
        raise Stop("invalid_request", "equivalence is {with, arguments, max_length}")
    other = raw.get("with")
    if not isinstance(other, str) or not LLVM_NAME.fullmatch(other.lstrip("@")):
        raise Stop("invalid_request", "equivalence.with must be the LLVM name of the other function")
    other = other.lstrip("@")
    if other == function:
        raise Stop("invalid_request", "equivalence.with must be another function than `function`")
    arguments = raw.get("arguments")
    if arguments is not None and (
        not isinstance(arguments, list) or not all(isinstance(a, str) and a in ROLES for a in arguments)
    ):
        raise Stop("invalid_request", f"equivalence.arguments must be a list of {', '.join(ROLES)}")
    max_length = raw.get("max_length", DEFAULTS["max_length"])
    if not isinstance(max_length, int) or isinstance(max_length, bool) or not 0 <= max_length <= 1 << 20:
        raise Stop("invalid_request", "equivalence.max_length must be a whole number from 0 to 1048576")
    return {"with": other, "arguments": arguments, "max_length": max_length}


def report(run: Run) -> dict[str, dict[str, Any]]:
    """What `ir-lean --report` says of each function in the request's IR, compiling C first, as
    tools/verify.py
    does."""
    source = Path(run.request["input"].get("ir") or run.request["input"]["c"])
    ll = source
    if "c" in run.request["input"]:
        cflags = run.request["input"].get("cflags")
        flags = [
            *os.environ.get("PROOF_CFLAGS", "").split(),
            *(verify.DEFAULT_CFLAGS if cflags is None else cflags),
        ]
        ll = run.work / "equivalence" / f"{run.request['namespace']}.ll"
        ll.parent.mkdir(parents=True, exist_ok=True)
        argv = ["clang", *flags, "-S", "-emit-llvm", "-fno-discard-value-names", "-o", str(ll), source.name]
        run.commands.append({"step": "equivalence:compile_c", "argv": argv, "cwd": str(source.parent)})
        ran = proc.run(argv, cwd=source.parent, timeout=max(1.0, run.remaining()))
        if ran.limit == "time_limit":
            raise Stop("time_limit", "clang didn't finish in time")
        if not ran.ok:
            raise Stop("compile_failed", f"clang exited with {ran.exit}: {ran.err[-1000:]}")
    argv = [str(run.tool), str(ll), "--report"]
    run.commands.append({"step": "equivalence:report", "argv": argv, "cwd": str(ROOT)})
    ran = proc.run(argv, timeout=max(1.0, run.remaining()))
    if ran.limit == "time_limit":
        raise Stop("time_limit", "ir-lean --report didn't finish in time")
    if not ran.ok:
        raise Stop("ir_invalid" if ran.exit == 1 else "tool_failed", f"ir-lean --report: {ran.err[-1000:]}")
    functions: dict[str, dict[str, Any]] = {}
    for line in ran.out.splitlines():
        parts = line.split("\t")
        if parts[0] == "ok" and len(parts) == 7:
            functions[parts[1]] = {
                "lean_name": parts[2],
                "signature": parts[3],
                "uses_memory": parts[6] == "memory",
            }
        elif parts[0] == "unsupported" and len(parts) == 3:
            functions[parts[1]] = {"unsupported": parts[2]}
    return functions


def roles(params: list[str], given: list[str] | None) -> list[str]:
    """What each argument is: by default a pointer is a buffer, an `i64` right after one is its length, and
    any
    other integer is a value."""
    if given is not None:
        if len(given) != len(params):
            raise Stop(
                "invalid_request", f"equivalence.arguments has {len(given)} roles for {len(params)} arguments"
            )
        out = given
    else:
        out = [
            "buffer"
            if p == "ptr"
            else "length"
            if p == "i64" and i > 0 and params[i - 1] == "ptr"
            else "value"
            for i, p in enumerate(params)
        ]
    for i, (p, r) in enumerate(zip(params, out, strict=True)):
        wanted = {"buffer": p == "ptr", "length": p == "i64", "value": bool(re.fullmatch(r"i\d+", p))}[r]
        if not wanted:
            raise Stop(
                "binder_unsupported",
                f"argument {i} is {p}, which can't be a {r}: a buffer is a ptr, a length an i64, and a value "
                "an integer. Tier 1 generates no other argument",
            )
        if r == "length" and "buffer" not in out[:i]:
            raise Stop("invalid_request", f"argument {i} is a length, and no buffer comes before it")
    return out


def equivalence_statement(run: Run) -> str:
    """The property that wherever `function` returns, `equivalence.with` returns the same value and leaves the
    same memory, from the same memory and arguments: each pointer into a buffer of its own, each length one
    that fits past its pointer, and each other integer any value. The memory is the module's `initial`, which
    holds its globals, with each buffer in an allocation of its own after them.

    Its hypotheses are that `function` answers, that it returns, and that the other answers. An input where
    `function` is undefined, or never finishes, makes the second false, and is discarded and counted: there
    the reference allows anything. One where either stops the model makes the first or the third false, and
    is counted in `run.model_stopped` instead: there the model says nothing, so a pass can't rest on it."""
    eq = run.request["equivalence"]
    functions = report(run)
    names = [run.request["function"], eq["with"]]
    for name in names:
        if name not in functions:
            raise Stop("function_not_found", f"the module has no function @{name}")
        if "unsupported" in functions[name]:
            raise Stop(
                "function_unsupported", f"ir-lean leaves out @{name}: {functions[name]['unsupported']}"
            )
    first, second = (functions[n] for n in names)
    if (first["signature"], first["uses_memory"]) != (second["signature"], second["uses_memory"]):
        raise Stop(
            "invalid_request",
            f"@{names[0]} is {first['signature']} and @{names[1]} {second['signature']}: an equivalence "
            "needs one signature, and both using memory or neither",
        )
    m = re.fullmatch(r"\((.*)\)->(.+)", first["signature"])
    if m is None:
        raise Stop(
            "tool_failed", f"ir-lean --report gave a signature this doesn't read: {first['signature']}"
        )
    params = [p for p in m[1].split(",") if p]
    kinds = roles(params, eq["arguments"])
    memory = first["uses_memory"]
    if "buffer" in kinds and not memory:
        raise Stop("binder_unsupported", "a pointer argument of a function that doesn't use memory")
    ns = run.request["namespace"]
    n = eq["max_length"]
    buffers = [i for i, k in enumerate(kinds) if k == "buffer"]
    binders, args = [], []
    for i in buffers:
        binders += [f"(b{i} : IRLean.Ptf.Buffer {n})", f"(p{i} : IRLean.Ptf.Pointer b{i})"]
    for i, k in enumerate(kinds):
        if k == "length":
            of = max(j for j in buffers if j < i)
            binders.append(f"(n{i} : IRLean.Ptf.Length p{of})")
    for i, k in enumerate(kinds):
        if k == "value":
            binders.append(f"(x{i} : BitVec {params[i][1:]})")
    for i, k in enumerate(kinds):
        args.append(
            f"(p{i}.into {ns}.initial {buffers.index(i)})"
            if k == "buffer"
            else f"n{i}.toVal"
            if k == "length"
            else f"(some x{i})"
        )
    mem = (
        f"(IRLean.Ptf.place {ns}.initial [{', '.join(f'b{i}.bytes' for i in buffers)}])"
        if buffers
        else f"{ns}.initial"
    )
    calls = [
        " ".join([f"({ns}.{functions[name]['lean_name']}", *args, *([mem] if memory else [])]) + ")"
        for name in names
    ]
    conclusion = f"IRLean.Ptf.Same {mem} {calls[0]} {calls[1]}" if memory else f"{calls[0]} = {calls[1]}"
    body = (
        f"IRLean.Ptf.Answers {calls[0]} → IRLean.Ptf.Returns {calls[0]} → IRLean.Ptf.Answers {calls[1]} → "
        f"{conclusion}"
    )
    run.model_hypotheses = {0: names[0], 2: names[1]}
    run.equivalence = {
        "functions": names,
        "signature": first["signature"],
        "arguments": kinds,
        "max_length": n,
    }
    return f"∀ {' '.join(binders)}, {body}" if binders else body


def executable_copy(run: Run) -> None:
    """For a function with memory, the generated module again on `ExecMem`, from `ir-lean
    --executable-memory`, compiled next to the module, for the search to run. If it can't be made, the search
    runs on `Mem`, and the
    result says why."""
    setup = run.setup or {}
    if not (setup.get("target") or {}).get("uses_memory"):
        return
    artifacts = setup.get("artifacts") or {}
    ir = (artifacts.get("ir") or {}).get("path") or ((artifacts.get("files") or {}).get("input") or {}).get(
        "copy"
    )
    namespace = f"{run.request['namespace']}Exec"
    lean_dir = run.work / "verify" / "lean"
    source = lean_dir / f"{namespace}.lean"
    started = time.monotonic()
    emit = [str(run.tool), str(ir), "--namespace", namespace, "--executable-memory", "-o", str(source)]
    run.commands.append({"step": "exec_copy:generate", "argv": emit, "cwd": str(ROOT)})
    ran = proc.run(emit, timeout=max(1.0, run.remaining()))
    if ran.exit not in (0, 3) or not source.exists():
        run.exec_missing = f"ir-lean --executable-memory exited with {ran.exit}: {ran.err[-500:]}"
        return
    olean = source.with_suffix(".olean")
    argv = lean.argv(run.request["limits"]["memory_mb"], "-R", str(lean_dir), "-o", str(olean), str(source))
    env = {**os.environ, "LEAN_PATH": f"{lean_dir}{os.pathsep}{run.work / 'verify' / 'library'}"}
    run.commands.append({"step": "exec_copy:compile", "argv": argv, "cwd": str(ROOT)})
    ran = proc.run(argv, env=env, timeout=max(1.0, run.remaining()))
    run.timing["exec_copy_seconds"] = round(time.monotonic() - started, 3)
    if ran.limit == "time_limit":
        raise Stop("time_limit", "compiling the module's copy on ExecMem didn't finish in time")
    if not ran.ok or not olean.exists():
        run.exec_missing = f"lean couldn't compile the copy on ExecMem, exit {ran.exit}: {ran.output[-500:]}"
        return
    run.exec_namespace = namespace


def set_up(run: Run) -> None:
    """Has tools/verify.py check the input and the statement, and generate and compile the module, without a
    proof or a witness. Its answer is then `error/not_proved`, and its work directory has the module the
    harness imports."""
    request = run.request
    started = time.monotonic()
    raw = {
        "input": request["input"],
        "function": request["function"],
        "namespace": request["namespace"],
        "statement": request["statement"],
        "limits": {
            "timeout_seconds": max(1, int(run.remaining())),
            "memory_mb": request["limits"]["memory_mb"],
        },
    }
    result = verify.verify(raw, ROOT, run.tool, run.work / "verify")
    run.timing["verify_setup_seconds"] = round(time.monotonic() - started, 3)
    run.setup = result
    if result["status"] == "error" and result["reason"] == "not_proved":
        return
    reason = result["reason"]
    if result["status"] == "timeout":
        reason = "memory_limit" if reason == "memory_limit" else "time_limit"
    elif reason not in FROM_VERIFY:
        reason = "tool_failed"
    raise Stop(reason, f"tools/verify.py: {result['status']}/{result['reason']}: {result.get('detail', '')}")


def search(run: Run, harness: Harness) -> None:
    """Runs the plan in order, until an input fails, the plan ends, or something stops it. An input that
    doesn't finish, or crashes Lean, is undecided: it's recorded, the harness starts again, and the search
    goes on."""
    assert run.plan is not None
    request = run.request
    per_input = request["limits"]["input_timeout_seconds"]
    inputs = run.plan.inputs
    keep_met = any(is_memory(b) for b in run.binders)
    position = 0
    search_ns = 0
    size = FIRST_BATCH
    started = time.monotonic()
    while position < len(inputs):
        if run.remaining() <= 0:
            run.limit_hit = "time_limit"
            break
        batch = inputs[position : position + size]
        size = min(size * 4, BATCH)
        out = harness.evaluate(
            [wire(run.binders, values) for values in batch], stop=True, input_timeout=per_input
        )
        for offset, code in enumerate(out.codes):
            index = position + offset
            phase = run.plan.phases[index]
            run.tried += 1
            run.by_phase[phase] = run.by_phase.get(phase, 0) + 1
            if code not in (1, 2):
                # Which hypothesis was false: 0 the first, and 2 + k hypothesis k after it.
                stopped = run.model_hypotheses.get(0 if code == 0 else code - 2)
                if stopped is None:
                    run.discarded += 1
                else:
                    run.model_stopped[stopped] = run.model_stopped.get(stopped, 0) + 1
                continue
            run.satisfied += 1
            if keep_met:
                run.met.append(index)
            if code == 2:
                run.failing = {"index": index, "phase": phase, "values": inputs[index]}
                run.timing["search_ns"] = search_ns + out.nanos[offset]
                run.timing["search_wall_ms"] = round((time.monotonic() - started) * 1000, 3)
                return
        search_ns += out.batch_ns or (out.nanos[-1] if out.nanos else 0)
        if out.stopped is None:
            position += len(batch)
            continue
        stuck = position + (out.stuck or 0)
        if out.stopped in ("time_limit", "memory_limit"):
            run.limit_hit = out.stopped
            break
        run.undecided.append(
            {
                "index": stuck,
                "phase": run.plan.phases[stuck],
                "result": out.stopped,
                "values": jsonable(run.binders, inputs[stuck]),
            }
        )
        if len(run.undecided) > DEFAULTS["restarts"]:
            break
        position = stuck + 1
        try:
            harness.start()
        except Stop as stop:
            run.limit_hit = stop.reason if stop.reason in ("time_limit", "memory_limit") else None
            if run.limit_hit is None:
                raise
            break
    run.planned_all = position >= len(inputs) and not run.undecided and run.limit_hit is None
    run.timing["search_ns"] = search_ns
    run.timing["search_wall_ms"] = round((time.monotonic() - started) * 1000, 3)


def shrink_failing(run: Run, harness: Harness) -> tuple:
    assert run.failing is not None
    start = run.failing["values"]
    if not run.request["shrink"]:
        return start
    per_input = run.request["limits"]["input_timeout_seconds"]
    started = time.monotonic()

    def still_fails(candidates: list[tuple]) -> int | None:
        if run.remaining() <= 0 or harness.process is None:
            return None
        out = harness.evaluate([wire(run.binders, c) for c in candidates], stop=True, input_timeout=per_input)
        if out.stopped is not None:
            # A candidate that doesn't finish ends shrinking. The harness has to be there for confirming.
            with contextlib.suppress(Stop):
                harness.start()
            return None
        return next((i for i, code in enumerate(out.codes) if code == 2), None)

    values, steps = shrink(start, run.binders, still_fails)
    run.timing["shrink_ms"] = round((time.monotonic() - started) * 1000, 3)
    run.failing["shrink_steps"] = steps
    return values


def assignment(binders: list[dict[str, Any]], values: tuple) -> dict[str, str]:
    """Binder names to Lean terms, by name where names are unique, and as #0, #1, ... where they aren't."""
    names = [b["name"] for b in binders]
    unique = len(set(names)) == len(names) and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", n) for n in names)
    return {
        (b["name"] if unique else f"#{i}"): lean_term(b, v)
        for i, (b, v) in enumerate(zip(binders, values, strict=True))
    }


def witness_step(result: dict[str, Any]) -> core.Step | None:
    """How the process that evaluated a witness ended, as a tools/verify.py result records it, or None."""
    commands = (result.get("reproduce") or {}).get("commands") or []
    ran = [c for c in commands if isinstance(c, dict) and c.get("step") == "claim:witness"]
    if not ran:
        return None
    return core.Step("claim:witness", ran[-1].get("exit"), "time_limit" if ran[-1].get("timed_out") else None)


def confirm_with_verify(run: Run, values: tuple) -> tuple[dict[str, Any], core.Step | None]:
    """Asks tools/verify.py, which elaborates the statement again on its own, to decide it at the input.
    Returns what it said, and how the process that evaluated the witness ended, as it recorded it."""
    started = time.monotonic()
    witness = assignment(run.binders, values)
    raw = {
        "input": run.request["input"],
        "function": run.request["function"],
        "namespace": run.request["namespace"],
        "statement": run.request["statement"],
        "witnesses": [witness],
        "limits": {
            "timeout_seconds": max(1, int(min(run.remaining(), VERIFY_CONFIRM_SECONDS))),
            "memory_mb": run.request["limits"]["memory_mb"],
        },
    }
    result = verify.verify(raw, ROOT, run.tool, run.work / "confirm")
    run.timing["verify_confirm_seconds"] = round(time.monotonic() - started, 3)
    witnesses = result.get("witnesses") or [{}]
    step = witness_step(result)
    return {
        "status": result["status"],
        "reason": result["reason"],
        "result": witnesses[0].get("result"),
        "instance": witnesses[0].get("instance"),
        "witness": witness,
        "result_json": str(run.work / "confirm" / "result.json"),
        "reproduce": [str(ROOT / "tools" / "verify.py"), "check", str(run.work / "confirm" / "request.json")],
    }, step


def refutes(run: Run, how: str, said: bool) -> bool:
    """Whether irlean.verdict grants a refutation on what confirmed a failing input, `how`, the kernel or
    compiled evaluation: that it `said` the input fails, and how the process that said it ended."""
    kernel, evaluated = (said, False) if how == "kernel" else (False, said)
    evidence = core.Evidence(lean=run.confirmed_by.get(how), kernel=kernel, evaluated=evaluated)
    return core.decide(core.Verdict.REFUTED, evidence).granted


def confirm(run: Run, harness: Harness, values: tuple) -> None:
    """Counts a failing input only once the kernel, or tools/verify.py, confirms it."""
    started = time.monotonic()
    kernel = (
        harness.kernel(wire(run.binders, values), DEFAULTS["kernel_timeout_seconds"])
        if harness.process is not None
        else {"ok": False, "reason": "harness_stopped"}
    )
    run.timing["kernel_ms"] = round((time.monotonic() - started) * 1000, 3)
    # Nothing more is asked of the harness. Stopping it keeps one Lean process at a time, and says how it
    # ended, which its answer rests on.
    harness.stop()
    evidence: list[str] = []
    if harness.ended is not None:
        run.confirmed_by["kernel"] = harness.ended
    if refutes(run, "kernel", kernel.get("ok") is True):
        evidence.append("kernel")
    checked: dict[str, Any] | None = None
    mode = run.request["verify_confirm"]
    if mode == "always" or (mode == "auto" and not evidence):
        checked, step = confirm_with_verify(run, values)
        if step is not None:
            run.confirmed_by["compiled_evaluation"] = step
        failed = checked["status"] == "counterexample" and checked["result"] == "fails"
        if refutes(run, "compiled_evaluation", failed):
            evidence.append("compiled_evaluation")
        elif checked["result"] == "holds":
            run.disagreement = "tools/verify.py found the statement true at the input"
    run.counterexample = {
        "values": [stored_value(v) for v in values],
        "assignment": assignment(run.binders, values),
        "shown": {b["name"]: shown(b, v) for b, v in zip(run.binders, values, strict=True)},
        "instance": kernel.get("instance") or (checked or {}).get("instance"),
        "evidence": evidence,
        "kernel": {k: v for k, v in kernel.items() if k != "kind"},
        "verify": checked,
        "found": {
            "phase": run.failing["phase"] if run.failing else None,
            "index": run.failing["index"] if run.failing else None,
            "assignment": assignment(run.binders, run.failing["values"]) if run.failing else None,
        },
        "shrink_steps": (run.failing or {}).get("shrink_steps", 0),
    }


def prooftest(
    raw: Any, base: Path, tool: Path = verify.DEFAULT_TOOL, work: Path | None = None
) -> dict[str, Any]:
    """Runs one tier-1 proof test, from a dict as in a request file with paths relative to `base`, and returns
    the result. This is the API: `tools/prooftest/prooftest.py run` is a thin layer over it."""
    started = time.monotonic()
    try:
        request = load_request(raw, base)
    except Stop as stop:
        return invalid_result(stop.detail, raw)
    digest = hashing.sha256_text(json.dumps(request, sort_keys=True))[:12]
    if work is None:
        RUNS.mkdir(parents=True, exist_ok=True)
        prune_runs()
        work = RUNS / f"{digest}-{time.time_ns()}"
    work = work.resolve()
    run = Run(request, work, tool.resolve(), started + request["limits"]["timeout_seconds"], started)
    harness = Harness(run)
    try:
        if work.exists() and any(work.iterdir()):
            raise Stop("invalid_request", f"work directory {work} isn't empty")
        work.mkdir(parents=True, exist_ok=True)
        (work / "request.json").write_text(json.dumps(request, indent=2, ensure_ascii=False) + "\n")
        if request.get("equivalence"):
            request["statement"] = equivalence_statement(run)
        set_up(run)
        executable_copy(run)
        t0 = time.monotonic()
        run.ready = harness.start()
        run.timing["harness_start_seconds"] = round(time.monotonic() - t0, 3)
        run.binders = run.ready["binders"]
        statement = run.ready["statement"]
        run.key = property_key(statement, run.binders)
        store = Store(Path(request["store"]) if request["store"] else None)
        run.stored = store.load(run.key, run.binders)
        run.plan = plan(run.binders, request["seed"], request["max_inputs"], run.stored)
        search(run, harness)
        if run.failing is not None:
            values = shrink_failing(run, harness)
            confirm(run, harness, values)
            if run.counterexample and run.counterexample["evidence"]:
                artifact = (run.setup or {}).get("artifacts", {}).get("generated", {})
                run.store_added = store.add(
                    run.key,
                    {
                        "values": run.counterexample["values"],
                        "assignment": run.counterexample["assignment"],
                        "found": datetime.now(UTC).isoformat(timespec="seconds"),
                        "generated_sha256": artifact.get("sha256"),
                        "evidence": run.counterexample["evidence"],
                    },
                    {"function": request["function"], "statement": statement},
                )
    except Stop as stop:
        run.stop = stop
    except Exception as error:  # Any bug here has to come back as unknown, never as a pass.
        run.stop = Stop("internal_error", f"{type(error).__name__}: {error}")
    finally:
        harness.stop()
    result = build_result(run, started)
    with contextlib.suppress(OSError):
        (work / "result.json").write_text(
            json.dumps(result, indent=2, ensure_ascii=False, default=str) + "\n"
        )
    return result


def decide(run: Run) -> tuple[str, str, str]:
    """The status, reason and a one-line detail, in this order of precedence: a confirmed counterexample, what
    stopped the run, a failure nothing confirmed, an input that didn't finish, a limit, an input where the
    model stopped, and then what the inputs that met the hypotheses say."""
    counterexample = run.counterexample
    if counterexample and counterexample["evidence"]:
        # Each kind of evidence, as irlean.verdict grants it: the kernel first.
        granted = [how for how in counterexample["evidence"] if refutes(run, how, True)]
        if not granted:
            return (
                "unknown",
                "internal_error",
                "the evidence recorded isn't a refutation irlean.verdict grants",
            )
        reason = "kernel_refuted" if "kernel" in granted else "compiled_evaluation"
        return "counterexample", reason, f"the statement is false at {counterexample['shown']}"
    if run.stop is not None:
        return "unknown", run.stop.reason, run.stop.detail
    if run.disagreement:
        return "unknown", "confirmation_disagrees", run.disagreement
    if counterexample is not None:
        kernel = counterexample.get("kernel") or {}
        return (
            "unknown",
            "unconfirmed",
            f"an input failed in the search, and nothing confirmed it: {kernel.get('detail', '')}"[:2000],
        )
    if run.limit_hit:
        return "unknown", run.limit_hit, f"{run.limit_hit.replace('_', ' ')} after {run.tried} inputs"
    if run.undecided:
        first = run.undecided[0]
        return (
            "unknown",
            first["result"],
            f"input {first['index']} ({first['phase']}) didn't finish, and nothing failed",
        )
    if not run.planned_all:
        return (
            "unknown",
            "time_limit",
            f"stopped after {run.tried} of {len(run.plan.inputs) if run.plan else 0} inputs",
        )
    if run.model_stopped:
        by = ", ".join(f"@{name} on {n}" for name, n in run.model_stopped.items())
        return (
            "unknown",
            "model_stopped",
            f"the model stopped on {sum(run.model_stopped.values())} of {run.tried} inputs, running {by}, "
            "where the property needs an answer, and nothing failed",
        )
    if run.satisfied == 0:
        return "vacuous", "no_input_meets_hypotheses", f"none of {run.tried} inputs met the hypotheses"
    exhaustive = bool(run.plan and run.plan.exhaustive and run.tried >= (run.plan.domain or 0))
    if run.satisfied < run.request["min_satisfied"] and not exhaustive:
        return (
            "unknown",
            "too_few_satisfying",
            f"only {run.satisfied} of {run.tried} inputs met the hypotheses",
        )
    if exhaustive:
        return "passed_tier1", "exhaustive", f"all {run.tried} inputs ran, and none failed. Not a proof"
    return (
        "passed_tier1",
        "sampled",
        f"{run.satisfied} of {run.tried} inputs met the hypotheses, and none failed. Not a proof",
    )


def trusted(run: Run, status: str) -> list[dict[str, str]]:
    out = [
        {
            "id": "scope.modeled_ir",
            "text": "About the function as this LLVM IR, in IRLean's semantics, as tools/verify.py's "
            "claims are",
            "see": "docs/trust.md#what-a-theorem-covers",
        },
        {
            "id": "search.compiled_evaluation",
            "text": "Inputs were decided by Lean's compiled code for the statement, with IRLean's own "
            "code run "
            "natively. A bug there could hide a failure. A failure counts only once confirmed",
            "see": "docs/proof-tests.md#confirming-a-counterexample",
        },
    ]
    if status == "passed_tier1":
        out.append(
            {
                "id": "tier1.not_a_proof",
                "text": f"No counterexample among {run.tried} inputs. An input not tried may fail. "
                "This is a test, "
                "not a proof",
                "see": "docs/proof-tests.md#statuses",
            }
        )
    if status == "counterexample" and run.counterexample:
        for kind in run.counterexample["evidence"]:
            out.append(
                {
                    "id": f"evidence.{kind}",
                    "text": EVIDENCE[kind],
                    "see": "docs/proof-tests.md#confirming-a-counterexample",
                }
            )
    calls = (run.ready or {}).get("calls") or {}
    if calls.get("exec_memory"):
        out.append(
            {
                "id": "search.executable_memory",
                "text": f"The search ran {calls['exec_memory']} of the property's calls of functions with "
                f"memory on the module's copy on ExecMem, from ir-lean --executable-memory, and "
                f"{calls.get('mem', 0)} on Mem as written. The memory a call starts from is the one the "
                "property names: IRLean.Ptf.toMem_placeExec for the buffers, and ExecMem.toMem_empty, "
                "toMem_addGlobal, toMem_addReloc and toMem_reserve for the module's initial, whose copy is "
                "the same Lean with ExecMem for Mem. That the copy then returns what the function does on "
                "that memory, f args x.toMem = Outcome.map ExecMem.out (f' args x), follows from run_map, "
                "stay_map, runPromised_map and promised_map, call_agrees, withFrame_agrees and each memory "
                "operation's _agrees theorem once each block of each function it runs agrees with its copy, "
                "which is argued for these functions, not proved. A counterexample doesn't rest on this: "
                "it's confirmed on Mem",
                "see": "docs/memory.md#why-a-test-on-execmem-is-a-test-of-mem",
            }
        )
    if run.exec_missing:
        out.append(
            {
                "id": "search.on_mem",
                "text": "The search ran on Mem, as the property is written, since it had no copy on "
                f"ExecMem: {run.exec_missing}",
                "see": "docs/proof-tests.md#memory",
            }
        )
    if run.equivalence:
        f, g = run.equivalence["functions"]
        out.append(
            {
                "id": "property.equivalence",
                "text": f"The property was built from @{f} and @{g}'s signature, "
                f"{run.equivalence['signature']}, with arguments {', '.join(run.equivalence['arguments'])}. "
                "Wherever the first returns, the second has to return the same value and leave the same "
                "sizes, flags and bytes in every allocation the memory they start from has, not counting the "
                "bytes of a constant one, which the model makes writing undefined: IRLean.Ptf.Same. An input "
                "where the first is undefined is discarded, and counted as not meeting the hypotheses. One "
                "where either stops the model is counted in inputs.model_stopped, and makes the result "
                "unknown. Buffers hold at most "
                f"{run.equivalence['max_length']} bytes, each in an allocation of its own after the module's "
                "globals, and integers are never poison",
                "see": "docs/proof-tests.md#equivalence",
            }
        )
    for item in (run.setup or {}).get("assumptions", []):
        if item.get("id") not in {"scope.modeled_ir", "statement.unpinned", "proof.code_runs"}:
            out.append(item)
    return out


def memory_inputs(run: Run) -> dict[str, Any] | None:
    """What the inputs that ran held, and those that met the hypotheses, which are what was tested, for each
    buffer, pointer and length: how many bytes, how far from 16- and 64-byte alignment, and how long, so a
    pass
    says which sizes it covered."""
    if not run.plan or not any(is_memory(b) for b in run.binders):
        return None
    # The search runs the plan in order, and skips only an input that didn't finish.
    skipped = {u["index"] for u in run.undecided}
    tried = [v for k, v in enumerate(run.plan.inputs[: run.tried + len(skipped)]) if k not in skipped]
    return {
        "tried": described(run, tried),
        "met_hypotheses": described(run, [run.plan.inputs[k] for k in run.met]),
    }


def described(run: Run, tried: list[tuple]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for i, b in enumerate(run.binders):
        values = [v[i] for v in tried]
        if b["kind"] == "buffer":
            sizes = [len(v) for v in values]
            out[b["name"]] = {"bytes": spread(sizes)}
        elif b["kind"] == "pointer":
            out[b["name"]] = {
                "offsets": spread(values),
                "unaligned_16": sum(v % 16 != 0 for v in values),
                "unaligned_64": sum(v % 64 != 0 for v in values),
            }
        elif b["kind"] == "length":
            out[b["name"]] = {
                **spread(values),
                "by_size": {
                    label: sum(low <= v <= high for v in values)
                    for label, (low, high) in {
                        "0": (0, 0),
                        "1-15": (1, 15),
                        "16-63": (16, 63),
                        "64-255": (64, 255),
                        "256-1023": (256, 1023),
                        "1024+": (1024, 1 << 62),
                    }.items()
                },
            }
    return out


def spread(values: list[int]) -> dict[str, int]:
    return {"min": min(values), "max": max(values), "distinct": len(set(values))} if values else {}


def assert_contract(result: dict[str, Any]) -> None:
    """The promises every result keeps. Breaking one is a bug here, so it turns the result into unknown."""
    status, reason = result["status"], result["reason"]
    problems = []
    if status not in STATUSES or reason not in REASONS or REASONS[reason][0] != status:
        problems.append(f"{status}/{reason} isn't in the contract")
    if result["exit_code"] != EXIT_CODES.get(status):
        problems.append("the exit code doesn't match the status")
    if result["proved"] is not False:
        problems.append("tier 1 never proves anything")
    counterexample = result.get("counterexample")
    if (status == "counterexample") != (counterexample is not None):
        problems.append("a counterexample comes with status counterexample, and only then")
    if counterexample is not None:
        evidence = counterexample.get("evidence") or []
        if not evidence or any(e not in EVIDENCE for e in evidence):
            problems.append("a counterexample needs evidence")
        if "kernel" in evidence and not (counterexample.get("kernel") or {}).get("ok"):
            problems.append("kernel evidence without the kernel's answer")
    inputs = result["inputs"]
    if status in ("passed_tier1", "vacuous") and (inputs["undecided"] or not inputs["planned_all"]):
        problems.append(f"{status} with inputs that didn't run")
    if status in ("passed_tier1", "vacuous") and inputs["model_stopped"]:
        problems.append(f"{status} with inputs where the model stopped")
    if status == "passed_tier1" and inputs["satisfied"] == 0:
        problems.append("a pass with no input that met the hypotheses")
    if status == "vacuous" and inputs["satisfied"] != 0:
        problems.append("vacuous with inputs that met the hypotheses")
    if problems:
        raise AssertionError("; ".join(problems))


def build_result(run: Run, started: float) -> dict[str, Any]:
    status, reason, detail = decide(run)
    setup = run.setup or {}
    plan_ = run.plan
    timing = dict(run.timing)
    if "search_ns" in timing:
        timing["search_ms"] = round(timing.pop("search_ns") / 1e6, 3)
    if run.counterexample:
        timing["to_counterexample_ms"] = round(
            timing.get("search_wall_ms", 0) + timing.get("shrink_ms", 0) + timing.get("kernel_ms", 0), 3
        )
    timing["total_seconds"] = round(time.monotonic() - started, 3)
    result: dict[str, Any] = {
        "schema": SCHEMA,
        "tier": 1,
        "status": status,
        "reason": reason,
        "detail": detail[:4000],
        "meaning": STATUSES[status],
        "exit_code": EXIT_CODES[status],
        "proved": False,
        "request": run.request,
        "property": {
            "function": run.request.get("function"),
            "namespace": run.request.get("namespace"),
            "statement": (run.ready or {}).get("statement") or (setup.get("claim") or {}).get("statement"),
            "key": run.key,
            "binders": run.binders,
            "target": setup.get("target"),
            "equivalence": run.equivalence,
        },
        # What the search ran a property with memory on: the copy on ExecMem, or Mem as written, and why.
        "memory": {
            "exec_copy": run.exec_namespace,
            "exec_missing": run.exec_missing,
            "calls": (run.ready or {}).get("calls"),
        },
        "counterexample": run.counterexample if status == "counterexample" else None,
        # A disagreement the kernel's proof outweighs is still a bug somewhere, and said here.
        "warnings": [run.disagreement] if run.disagreement and status == "counterexample" else [],
        "candidate": run.counterexample if status != "counterexample" else None,
        "inputs": {
            "seed": run.request.get("seed"),
            "max_inputs": run.request.get("max_inputs"),
            "planned": len(plan_.inputs) if plan_ else 0,
            "planned_all": run.planned_all,
            "tried": run.tried,
            "satisfied": run.satisfied,
            "discarded": run.discarded,
            "model_stopped": sum(run.model_stopped.values()),
            "by_phase": run.by_phase,
            "replayed": len(run.stored),
            "exhaustive": bool(plan_ and plan_.exhaustive),
            "domain": plan_.domain if plan_ else None,
            "undecided": run.undecided,
            "memory": memory_inputs(run),
        },
        "store": {
            "directory": run.request.get("store"),
            "key": run.key,
            "replayed": len(run.stored),
            "added": run.store_added,
        },
        "trusted": trusted(run, status),
        "timing": timing,
        "setup": {
            "status": setup.get("status"),
            "reason": setup.get("reason"),
            "work": str(run.work / "verify"),
        }
        if setup
        else None,
        "versions": {
            **(setup.get("versions") or {}),
            "harness_sha256": hashing.sha256_file(HARNESS),
            "prooftest_sha256": hashing.sha256_file(Path(__file__)),
        },
        "reproduce": {
            "request": str(run.work / "request.json"),
            "command": [str(Path(__file__).resolve()), "run", str(run.work / "request.json")],
            "commands": run.commands,
        },
    }
    try:
        assert_contract(result)
    except AssertionError as error:
        result.update(
            status="unknown",
            reason="internal_error",
            detail=f"the result broke its own contract: {error}",
            meaning=STATUSES["unknown"],
            exit_code=EXIT_CODES["unknown"],
            counterexample=None,
        )
    return result


def invalid_result(detail: str, raw: Any) -> dict[str, Any]:
    run = Run(
        {
            "invalid": raw
            if isinstance(raw, dict | list | str | int | float | bool) or raw is None
            else repr(raw)
        },
        Path(),
        Path(),
        time.monotonic(),
        time.monotonic(),
    )
    run.stop = Stop("invalid_request", detail)
    result = build_result(run, time.monotonic())
    result["reproduce"] = None
    return result


def prune_runs() -> None:
    try:
        runs = sorted(
            (p for p in RUNS.iterdir() if p.is_dir() and re.fullmatch(r"[0-9a-f]{12}-\d+", p.name)),
            key=lambda p: p.stat().st_mtime,
            reverse=True,
        )
    except OSError:
        return
    for old in runs[RUNS_KEPT:]:
        shutil.rmtree(old, ignore_errors=True)


def capabilities() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "request_schema": REQUEST_SCHEMA,
        "tier": 1,
        "statuses": STATUSES,
        "exit_codes": EXIT_CODES,
        "reasons": {code: {"status": s, "meaning": m} for code, (s, m) in REASONS.items()},
        "evidence": EVIDENCE,
        "request_fields": REQUEST_FIELDS,
        "request_json_schema": REQUEST_JSON_SCHEMA,
        "defaults": {**DEFAULTS, "store": str(DEFAULT_STORE)},
        "binders": "BitVec w, IRLean.Val w (poison included), Bool, and memory: IRLean.Ptf.Buffer n, "
        "the bytes of an allocation, and a IRLean.Ptf.Pointer and a IRLean.Ptf.Length into a buffer the "
        "statement binds. Hypotheses are binders whose type is a proposition. Anything else, such as a Mem "
        "or a PtrVal, comes back unknown",
    }


class ArgumentError(Exception):
    pass


class Parser(argparse.ArgumentParser):
    """Raises on bad arguments, where argparse would exit with 2, which means counterexample here."""

    def error(self, message: str) -> NoReturn:
        raise ArgumentError(message)


def main(argv: list[str] | None = None) -> int:
    parser = Parser(
        prog="tools/prooftest/prooftest.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = parser.add_subparsers(dest="command", required=True)
    caps = sub.add_parser("capabilities", help="print the contract as JSON")
    caps.add_argument("--pretty", action="store_true")
    go = sub.add_parser("run", help="run one property")
    go.add_argument(
        "request_file", nargs="?", type=Path, help="a request as JSON, or - to read it from stdin"
    )
    source = go.add_mutually_exclusive_group()
    source.add_argument("--ir", help="LLVM IR, .ll or .bc")
    source.add_argument("--c", help="C source, compiled with clang")
    go.add_argument("--cflags", help="flags for --c, as one string")
    go.add_argument("--function")
    go.add_argument("--namespace")
    go.add_argument("--statement")
    go.add_argument(
        "--equivalent-to", metavar="G", help="instead of --statement: that --function and G agree"
    )
    go.add_argument(
        "--arguments", help="for --equivalent-to: value, buffer or length for each argument, by commas"
    )
    go.add_argument("--max-length", type=int, help="for --equivalent-to: the most bytes a buffer holds")
    go.add_argument("--seed", type=int)
    go.add_argument("--max-inputs", type=int)
    go.add_argument("--min-satisfied", type=int)
    go.add_argument("--timeout", type=float)
    go.add_argument("--memory-mb", type=int)
    go.add_argument("--input-timeout", type=float)
    stores = go.add_mutually_exclusive_group()
    stores.add_argument("--store", help=f"a directory of failing inputs. Default {DEFAULT_STORE}")
    stores.add_argument("--no-store", action="store_true")
    go.add_argument("--no-shrink", action="store_true")
    go.add_argument("--verify-confirm", choices=["auto", "always", "never"])
    go.add_argument("--tool", type=Path, default=verify.DEFAULT_TOOL, help="the ir-lean binary")
    go.add_argument("--work-dir", type=Path, help="an empty or new directory for the run. Kept")
    go.add_argument("--pretty", action="store_true")
    try:
        args = parser.parse_args(argv)
    except ArgumentError as error:
        result = invalid_result(f"bad arguments: {error}", None)
        print(json.dumps(result, ensure_ascii=False))
        return result["exit_code"]
    if args.command == "capabilities":
        print(json.dumps(capabilities(), indent=2 if args.pretty else None, ensure_ascii=False))
        return 0
    raw: Any
    base = Path.cwd()
    flags = {
        "function": args.function,
        "namespace": args.namespace,
        "statement": args.statement,
        "seed": args.seed,
        "max_inputs": args.max_inputs,
        "min_satisfied": args.min_satisfied,
        "verify_confirm": args.verify_confirm,
    }
    limits = {
        k: v
        for k, v in (
            ("timeout_seconds", args.timeout),
            ("memory_mb", args.memory_mb),
            ("input_timeout_seconds", args.input_timeout),
        )
        if v is not None
    }
    given = [v for v in flags.values() if v is not None] + list(limits.values())
    given += [x for x in (args.ir, args.c, args.cflags, args.store) if x is not None]
    equivalence = {
        k: v
        for k, v in (
            ("with", args.equivalent_to),
            ("arguments", args.arguments.split(",") if args.arguments is not None else None),
            ("max_length", args.max_length),
        )
        if v is not None
    }
    given += list(equivalence.values())
    given += [x for x in (args.no_store, args.no_shrink) if x]
    if args.request_file is not None:
        if given:
            raw = "a request file and request flags together"
        else:
            # From stdin, paths are relative to the working directory, as they are for flags.
            stdin = str(args.request_file) == "-"
            if not stdin:
                base = args.request_file.resolve().parent
            try:
                raw = json.loads(sys.stdin.read() if stdin else args.request_file.read_text())
            except OSError as error:
                raw = f"can't read {args.request_file}: {error}"
            except json.JSONDecodeError as error:
                raw = f"{'stdin' if stdin else args.request_file} isn't JSON: {error}"
    else:
        raw = {k: v for k, v in flags.items() if v is not None}
        if args.ir is not None:
            raw["input"] = {"ir": args.ir}
        elif args.c is not None:
            raw["input"] = {
                "c": args.c,
                **({"cflags": args.cflags.split()} if args.cflags is not None else {}),
            }
        if limits:
            raw["limits"] = limits
        if args.no_store:
            raw["store"] = None
        elif args.store is not None:
            raw["store"] = args.store
        if args.no_shrink:
            raw["shrink"] = False
        if equivalence:
            raw["equivalence"] = equivalence
    try:
        result = (
            invalid_result(raw, None)
            if isinstance(raw, str)
            else prooftest(raw, base, args.tool, args.work_dir)
        )
        text = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False, default=str)
    except Exception as error:  # Even a bug here answers in the contract, as unknown.
        result = invalid_result(f"internal error: {type(error).__name__}: {error}", None)
        result.update(reason="internal_error", detail=f"{type(error).__name__}: {error}")
        text = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False, default=str)
    print(text)
    return result["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
