#!/usr/bin/env python3
"""Writes the whole-function proof for one function of the Argon2 round's rewrite: README.md. A prototype,
outside CI.

It reads the two translations, `Base.lean` and `Cand.lean`, which are the same text but in the regions, and the
regions' index, and writes a Lean file that proves the candidate's function refines the baseline's from the
slices' theorems, `rN_oK_same`, with `Whole.lean`'s tactics. Nothing in what it writes is about the function but
its blocks' names and fields, and which blocks hold a region.

usage: gen.py BASE.lean CAND.lean BASE.ll regions.json FUNCTION NAMESPACE > OUT.lean
"""

import json
import re
import sys
from pathlib import Path

base_lean, cand_lean, base_ll, regions_json, fn, namespace = sys.argv[1:7]
A = Path(base_lean).read_text().splitlines()
B = Path(cand_lean).read_text().splitlines()
IR = Path(base_ll).read_text().splitlines()
regions = json.loads(Path(regions_json).read_text())
assert len(A) == len(B)

# The function's namespace in the translation: its blocks, its `step`, its `promise`.
lo = A.index(f"namespace {fn}")
hi = A.index(f"end {fn}")
BINDER = re.compile(r"\(([^():]+) : ((?:[^()]|\([^()]*\))+)\)")
CTOR = re.compile(r"^  \| (\w+)((?: \(.*\))?)$")


def constructors(start: int) -> list[tuple[str, str, list[str]]]:
    """The constructors of the inductive type that starts at line `start`: name, binders as written, field names."""
    found = []
    for line in A[start + 1 : hi]:
        m = CTOR.match(line)
        if not m:
            break
        names = [n for group, _ in BINDER.findall(m.group(2)) for n in group.split()]
        found.append((m.group(1), m.group(2).strip(), names))
    return found


# A function with many blocks has them in groups, `G0`, `G1`, ..., each with its own `step`, under one `Block`.
inductives = {m.group(1): i for i, line in enumerate(A[lo:hi], lo) if (m := re.match(r"^inductive (\w+) where$", line))}
groups = [g for g in inductives if g != "Block"]
if groups:
    blocks = [(g, c) for g in groups for c in constructors(inductives[g])]
else:
    blocks = [("", c) for c in constructors(inductives["Block"])]


def pattern(group: str, name: str, fields: list[str], where: str = "") -> str:
    """The block `name` of `group` with `fields`, as a term of `Block`."""
    inner = f".{name} {' '.join(fields)}".rstrip()
    return f"(.g{group[1:]} ({inner}))" if group else f"({inner})"


# The lines of each block's code, to find the blocks that hold a region.
STEP = re.compile(r"^  \| \.(\w+)\b.* =>$")
block_of_line: dict[int, str] = {}
current = None
for i in range(lo, hi):
    m = STEP.match(A[i])
    if m:
        current = m.group(1)
    elif A[i].startswith("noncomputable def") or A[i].startswith("def "):
        current = None
    if current:
        block_of_line[i] = current
differs = [i for i in range(lo, hi) if A[i] != B[i]]
cut_blocks: list[str] = []
for i in differs:
    assert i in block_of_line, f"line {i + 1} differs outside a block's code"
    if block_of_line[i] not in cut_blocks:
        cut_blocks.append(block_of_line[i])

# The function's regions, in the IR's order, are its cut blocks', in the translation's.
define = next(i for i, line in enumerate(IR) if line.startswith("define") and f"@{fn}(" in line)
end = next(i for i in range(define, len(IR)) if IR[i] == "}")
mine = [r for r in regions if define < r["lines"][0] - 1 < end]
assert len(mine) == len(cut_blocks), (len(mine), cut_blocks)
cuts = {}
for region, block in zip(mine, cut_blocks, strict=True):
    # A value's number in the translation is the IR's, less the block labels before it, which the IR numbers too.
    labels = 1 + sum(1 for line in IR[define : region["lines"][0] - 1] if re.match(r"^\d+:", line))
    cuts[block] = (region["region"], [f"v{int(p[1:]) - labels}" for p in region["params"]], len(region["outputs"]))

src = f"Base.{fn}"
tgt = f"Cand.{fn}"
rel = "(Next.Rel (fun b b' => same b = b') Eq)"
out = [
    "import Whole",
    "import Base",
    "import Cand",
    *[f"import T{n}" for n, _, _ in cuts.values()],
    "",
    "open IRLean IRLean.Whole",
    "",
    "set_option maxRecDepth 100000",
    "",
    f"namespace {namespace}",
    "",
    "/-- The candidate's block of the same name, with the same fields and the same memory. -/",
    f"def same : {src}.Block → {tgt}.Block",
]
for group, (name, _, fields) in blocks:
    out.append(f"  | {pattern(group, name, fields)} => {pattern(group, name, fields)}")
out.append("")
for group, (name, binders, fields) in blocks:
    step = f"{group}.step" if group else "step"
    inner = f"(.{name} {' '.join(fields)})".replace(" )", ")")
    out += [
        "set_option maxHeartbeats 4000000 in",
        f"theorem step_{name} {binders} :".replace("  :", " :"),
        f"    Outcome.Sim {rel} ({src}.{step} {inner})",
        f"      ({tgt}.{step} {inner}) := by",
        "  sim_unfold",
        "  sim_same",
    ]
    if name in cuts:
        n, params, outputs = cuts[name]
        p = " ".join(params)
        for k in range(outputs):
            out.append(
                f"  cut_store (r{n}_o{k}_same {p}) (R{n}Src.r{n}_o{k}_src.step (.bb1 {p}))"
                f" (R{n}Tgt.r{n}_o{k}_tgt.step (.bb1 {p}))"
            )
        out.append("  sim_same")
    out += ["  sim_end", ""]

out += [
    "/-- Blocks that are the same block step to the same block, or return the same result and memory. -/",
    f"theorem step_sim (b : {src}.Block) (b' : {tgt}.Block) (h : same b = b') :",
    f"    Outcome.Sim {rel} ({src}.step b) ({tgt}.step b') := by",
    "  subst h",
]
if groups:
    out.append("  cases b with")
    for g in groups:
        out.append(f"  | g{g[1:]} b =>")
        out.append("    cases b with")
        for group, (name, _, fields) in blocks:
            if group == g:
                out.append(f"    | {name} {' '.join(fields)} => exact step_{name} {' '.join(fields)}".rstrip())
else:
    out.append("  cases b with")
    for _, (name, _, fields) in blocks:
        out.append(f"  | {name} {' '.join(fields)} => exact step_{name} {' '.join(fields)}".rstrip())
out += [
    "",
    "/-- They're under the loops' promise together. -/",
    f"theorem promise_eq (b : {src}.Block) (b' : {tgt}.Block) (h : same b = b') :",
    f"    {tgt}.promise b' = {src}.promise b := by",
    "  subst h",
    "  cases b with" if not groups else "  rcases b with b | b | b <;> cases b <;> rfl",
]
if not groups:
    out[-1] = "  cases b <;> rfl"
print("\n".join(out))
print()
print(Path(sys.argv[7]).read_text().rstrip() if len(sys.argv) > 7 else "")
print()
print(f"end {namespace}")
