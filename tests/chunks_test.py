#!/usr/bin/env python3
"""Checks tests/llvm_scope/chunks.json, which puts each name the pinned LLVM registers a pass under in one
of the nine chunks of docs/chunks.md, against INV-01's inventory, tests/llvm_scope/inventory.json.

It fails if a pass is in no chunk or in two, if a chunk names a pass the inventory doesn't have, if a pass
the decision of 2026-11-09 names is in another chunk, if chunk 9 leaves out a pass the inventory files as a
printer, verifier, debug aid or instrumentation, or holds another without a reason, if an `asm-printer` or an
option's codegen implementation is outside chunk 8, or if the counts in docs/chunks.md differ from the
file's. Cases built to break each rule show it's refused. Only the standard library and
tests/llvm_scope.py, in well under a second.

usage: tests/chunks_test.py
"""

import copy
import json
import re
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any

import llvm_scope

ROOT = Path(__file__).resolve().parent.parent
INVENTORY = ROOT / "tests" / "llvm_scope" / "inventory.json"
CHUNKS = ROOT / "tests" / "llvm_scope" / "chunks.json"
DOC = ROOT / "docs" / "chunks.md"

# The chunks, as the maintainer decided them on 2026-11-09, in the roadmap.
NAMES = {
    1: "Peepholes",
    2: "Scalar, no memory",
    3: "Memory",
    4: "Loops",
    5: "Interprocedural",
    6: "Vectorization",
    7: "Pipelines",
    8: "Codegen",
    9: "The rest",
}
# The passes the decision names, by the names they're registered under.
NAMED = {
    1: {"instsimplify", "instcombine", "aggressive-instcombine", "reassociate"},
    2: {
        "sccp",
        "correlated-propagation",
        "adce",
        "bdce",
        "simplifycfg",
        "jump-threading",
        "div-rem-pairs",
        "constraint-elimination",
    },
    3: {"sroa", "mem2reg", "early-cse", "gvn", "newgvn", "dse", "memcpyopt"},
    4: {
        "loop-simplify",
        "lcssa",
        "loop-rotate",
        "licm",
        "indvars",
        "loop-unroll",
        "loop-deletion",
        "loop-reduce",
    },
    5: {
        "inline",
        "function-attrs",
        "globalopt",
        "ipsccp",
        "argpromotion",
        "deadargelim",
        "wholeprogramdevirt",
    },
    6: {"loop-vectorize", "slp-vectorizer", "load-store-vectorizer"},
    7: {"default", "thinlto-pre-link", "thinlto", "lto-pre-link", "lto"},
}
# The inventory's categories the decision puts in chunk 9, and the one it puts in chunk 8.
REST = {"printer-verifier-debug", "instrumentation"}
EMISSION = "emission"
# A row of the table of counts in docs/chunks.md.
ROW = re.compile(r"^\| (\d)? ?\| ([^|]+?) \| ([\d,]+) \| ([\d,]+) \| ([\d,]+) \| ([\d,]+) \|$", re.M)


def where(chunks: dict[str, Any]) -> dict[str, list[int]]:
    """Each pass the file names, and every chunk that names it."""
    found: dict[str, list[int]] = {}
    for c in chunks["chunks"]:
        for p in c.get("passes", []):
            found.setdefault(p, []).append(c.get("chunk"))
    return found


def check(inv: dict[str, Any], chunks: dict[str, Any], named: dict[int, set[str]] = NAMED) -> list[str]:
    """What's wrong with `chunks` as an assignment of `inv`'s passes, one line each."""
    errors = []
    items = {x["name"]: x for x in inv["items"]}
    numbers = [c.get("chunk") for c in chunks["chunks"]]
    if numbers != sorted(NAMES):
        errors.append(f"the chunks are {numbers}, not {sorted(NAMES)} in order")
    for c in chunks["chunks"]:
        n = c.get("chunk")
        if n in NAMES and c.get("name") != NAMES[n]:
            errors.append(f"chunk {n} is named {c.get('name')!r}, not {NAMES[n]!r}")
        if c.get("passes") != sorted(set(c.get("passes", []))):
            errors.append(f"chunk {n}'s passes aren't sorted, or name one twice")
    found = where(chunks)
    for p in sorted(items):
        if p not in found:
            errors.append(f"{p}: in no chunk")
    for p, ns in sorted(found.items()):
        if len(ns) > 1:
            errors.append(f"{p}: in chunks {ns}, not one")
        if p not in items:
            errors.append(f"{p}: in chunk {ns[0]}, and not in the inventory")
    for n, ps in sorted(named.items()):
        for p in sorted(ps):
            if found.get(p) != [n]:
                errors.append(
                    f"{p}: the decision puts it in chunk {n}, and the file in {found.get(p, 'none')}"
                )
    for p, x in sorted(items.items()):
        selector = {r["registry"] for r in x["registrations"]} == {"selector"}
        if x["category"] in REST and found.get(p) != [9]:
            errors.append(
                f"{p}: the inventory files it as {x['category']}, so it's chunk 9's, not {found.get(p)}"
            )
        if (x["category"] == EMISSION or selector) and found.get(p) != [8]:
            errors.append(f"{p}: emits code or is an option's codegen implementation, so it's chunk 8's")
    nine = next((c for c in chunks["chunks"] if c.get("chunk") == 9), {})
    reasons = nine.get("beyond_category", {})
    beyond = {p for p in nine.get("passes", []) if p in items and items[p]["category"] not in REST}
    for p in sorted(beyond - set(reasons)):
        errors.append(
            f"{p}: in chunk 9 though the inventory files it as {items[p]['category']}, with no reason"
        )
    for p in sorted(set(reasons) - beyond):
        errors.append(f"{p}: has a reason to be in chunk 9 beyond its category, and isn't there as such")
    for p, why in sorted(reasons.items()):
        if not isinstance(why, str) or not why.strip():
            errors.append(f"{p}: its reason to be in chunk 9 is empty")
    return errors


def counts(inv: dict[str, Any], chunks: dict[str, Any]) -> dict[str, tuple[int, int, int, int]]:
    """For each chunk, by its number and name, and for all: passes, analyses, passes in `default<O2>`, and
    passes in `llc`'s pipelines."""
    items = {x["name"]: x for x in inv["items"]}
    o2 = set(llvm_scope.opt_names(inv["pipelines"]["opt"]["default<O2>"]))
    llc = {
        p for levels in inv["pipelines"]["llc"].values() for r in levels.values() for p in r["passes"].split()
    }

    def row(ps: list[str]) -> tuple[int, int, int, int]:
        analyses = sum(1 for p in ps if p in items and items[p]["category"] == "analysis")
        return len(ps), analyses, len(o2 & set(ps)), len(llc & set(ps))

    out = {f"{c['chunk']} {c['name']}": row(c["passes"]) for c in chunks["chunks"]}
    out["All"] = row(sorted(where(chunks)))
    return out


def check_doc(text: str, want: dict[str, tuple[int, int, int, int]]) -> list[str]:
    """What's wrong with the table of counts in docs/chunks.md, against `want`."""
    rows = {
        f"{m.group(1) or ''} {m.group(2)}".strip(): tuple(int(g.replace(",", "")) for g in m.groups()[2:])
        for m in ROW.finditer(text)
    }
    errors = []
    for label, got in sorted(want.items()):
        if label not in rows:
            errors.append(f"docs/chunks.md has no row of counts for {label}")
        elif rows[label] != got:
            errors.append(f"docs/chunks.md counts {rows[label]} for {label}, and the files give {got}")
    for label in sorted(set(rows) - set(want)):
        errors.append(f"docs/chunks.md counts {label}, which isn't a chunk")
    return errors


def small() -> tuple[dict[str, Any], dict[str, Any]]:
    """An inventory of four passes, and an assignment of them that's right."""

    def item(name: str, category: str, registry: str = "PassRegistry.def") -> dict[str, Any]:
        return {"name": name, "category": category, "registrations": [{"registry": registry}]}

    inv = {
        "items": [
            item("foo", "transform"),
            item("print<foo>", "printer-verifier-debug"),
            item("x-asm-printer", "emission"),
            item("helloworld", "transform"),
        ]
    }
    passes: dict[int, list[str]] = {n: [] for n in NAMES}
    passes[2] = ["foo"]
    passes[8] = ["x-asm-printer"]
    passes[9] = ["helloworld", "print<foo>"]
    listed: list[dict[str, Any]] = [{"chunk": n, "name": NAMES[n], "passes": passes[n]} for n in NAMES]
    chunks: dict[str, Any] = {"chunks": listed}
    chunks["chunks"][8]["beyond_category"] = {"helloworld": "prints function names"}
    return inv, chunks


def chunk(chunks: dict[str, Any], n: int) -> dict[str, Any]:
    return chunks["chunks"][n - 1]


# Each breaks one rule of a right assignment, and has to be refused with a message saying so.
BROKEN: list[tuple[str, Callable[[dict[str, Any], dict[str, Any]], object], str]] = [
    ("a pass in no chunk", lambda _, c: chunk(c, 2)["passes"].remove("foo"), "foo: in no chunk"),
    (
        "a pass in two chunks",
        lambda _, c: chunk(c, 3)["passes"].append("foo"),
        "foo: in chunks [2, 3], not one",
    ),
    ("a pass named twice in one chunk", lambda _, c: chunk(c, 2)["passes"].append("foo"), "name one twice"),
    (
        "a pass the inventory doesn't have",
        lambda _, c: chunk(c, 4)["passes"].append("ghost"),
        "not in the inventory",
    ),
    ("a chunk left out", lambda _, c: c["chunks"].pop(6), "not [1, 2, 3, 4, 5, 6, 7, 8, 9] in order"),
    ("a chunk renamed", lambda _, c: chunk(c, 7).update(name="Pipes"), "chunk 7 is named 'Pipes'"),
    (
        "a printer outside chunk 9",
        lambda _, c: (
            chunk(c, 9)["passes"].remove("print<foo>"),
            chunk(c, 2)["passes"].insert(0, "print<foo>"),
        ),
        "print<foo>: the inventory files it as printer-verifier-debug",
    ),
    (
        "an asm-printer outside chunk 8",
        lambda _, c: (chunk(c, 8)["passes"].clear(), chunk(c, 9)["passes"].append("x-asm-printer")),
        "x-asm-printer: emits code",
    ),
    (
        "a transform in chunk 9 with no reason",
        lambda _, c: chunk(c, 9).pop("beyond_category"),
        "helloworld: in chunk 9 though the inventory files it as transform, with no reason",
    ),
    (
        "a reason for a pass not in chunk 9",
        lambda _, c: chunk(c, 9)["beyond_category"].update(foo="a test"),
        "foo: has a reason to be in chunk 9",
    ),
    (
        "an empty reason",
        lambda _, c: chunk(c, 9)["beyond_category"].update(helloworld=" "),
        "helloworld: its reason to be in chunk 9 is empty",
    ),
]


def negatives() -> list[str]:
    """Runs each broken case, and the right one, and returns what didn't behave."""
    failures = []
    inv, good = small()
    if errors := check(inv, good, {2: {"foo"}}):
        failures.append(f"a right assignment is refused: {errors}")
    else:
        print("ok    a right assignment passes")
    for name, brk, want in BROKEN:
        bad = copy.deepcopy(good)
        brk(inv, bad)
        errors = check(inv, bad, {2: {"foo"}})
        if not any(want in e for e in errors):
            failures.append(f"{name}: expected an error with {want!r}, got {errors}")
        else:
            print(f"ok    {name} is refused")
    bad = copy.deepcopy(good)
    errors = check(inv, bad, {5: {"foo"}})
    if not any("the decision puts it in chunk 5" in e for e in errors):
        failures.append(f"a named pass in another chunk: expected an error, got {errors}")
    else:
        print("ok    a pass the decision names, in another chunk, is refused")
    want = {"1 Peepholes": (4, 0, 4, 1)}
    for name, text in [
        ("a count that differs", "| 1 | Peepholes | 5 | 0 | 4 | 1 |\n"),
        ("a chunk with no row", "| 2 | Peepholes | 4 | 0 | 4 | 1 |\n"),
        ("a row for no chunk", "| 1 | Peepholes | 4 | 0 | 4 | 1 |\n| 2 | Extra | 1 | 0 | 0 | 0 |\n"),
    ]:
        if not check_doc(text, want):
            failures.append(f"docs/chunks.md with {name} passes")
        else:
            print(f"ok    docs/chunks.md with {name} is refused")
    if errors := check_doc("| 1 | Peepholes | 4 | 0 | 4 | 1 |\n", want):
        failures.append(f"docs/chunks.md with the right counts is refused: {errors}")
    return failures


def main() -> int:
    if len(sys.argv) != 1:
        sys.exit(__doc__.rsplit("usage: ", 1)[1].strip())
    failures = negatives()
    inv = json.loads(INVENTORY.read_text())
    chunks = json.loads(CHUNKS.read_text())
    errors = check(inv, chunks) + check_doc(DOC.read_text(), counts(inv, chunks))
    failures += errors
    if not errors:
        for label, (n, analyses, o2, llc) in counts(inv, chunks).items():
            print(f"ok    {label}: {n} passes, {analyses} analyses, {o2} in default<O2>, {llc} in llc's")
    for f in failures:
        print(f"FAIL  {f}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
