#!/usr/bin/env python3
"""Writes the whole-function proof for one function of the Argon2 round's rewrite: README.md. A prototype,
outside CI.

It reads the baseline's translation, `Base.lean`, the baseline's IR and the regions' index, and writes a Lean file
that proves the candidate's function does what the baseline's does from the slices' theorems, `rN_oK_same`, with
`Whole.lean`'s tactics. It doesn't read the candidate: what it writes is the proof for any candidate with those
regions, and Lean decides whether a candidate is one. Nothing in what it writes is about the function but its blocks'
names and fields, which blocks hold a region and where it starts, and which call a function that has a proof of its
own.

usage: gen.py BASE.lean BASE.ll regions.json FUNCTION NAMESPACE MAIN.lean [CALLEE=THEOREM:MODULE ...]
MAIN.lean holds the function's own theorem, about its attributes, and is appended as it is. Writes to stdout.
"""

import json
import re
import sys
from pathlib import Path

base_lean, base_ll, regions_json, fn, namespace, main = sys.argv[1:7]
callees = {}
for arg in sys.argv[7:]:
    callee, proof = arg.split("=")
    callees[callee] = tuple(proof.split(":"))
A = Path(base_lean).read_text().splitlines()
IR = Path(base_ll).read_text().splitlines()
regions = json.loads(Path(regions_json).read_text())

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


def pattern(group: str, name: str, fields: list[str]) -> str:
    """The block `name` of `group` with `fields`, as a term of `Block`."""
    inner = f".{name} {' '.join(fields)}".rstrip()
    return f"(.g{group[1:]} ({inner}))" if group else f"({inner})"


# The lines of each block's code.
STEP = re.compile(r"^  \| \.(\w+)\b.* =>$")
lines_of: dict[str, list[int]] = {}
current = None
for i in range(lo, hi):
    m = STEP.match(A[i])
    if m:
        current = m.group(1)
        lines_of[current] = []
    elif A[i].startswith(("noncomputable def", "def ", "/--")) or not A[i].strip():
        current = None
    elif current:
        lines_of[current].append(i)
# The function's regions. A region is in one block: the IR's blocks are the translation's, in the same order. A value's
# number in the translation is the IR's, less the block labels before it, which the IR numbers too.
define = next(i for i, line in enumerate(IR) if line.startswith("define") and f"@{fn}(" in line)
end = next(i for i in range(define, len(IR)) if IR[i] == "}")
order = list(lines_of)
cuts: dict[str, tuple[dict, int]] = {}
for region in regions:
    first = region["lines"][0] - 1
    if define < first < end:
        labels = 1 + sum(1 for line in IR[define:first] if re.match(r"^\d+:", line))
        assert order[labels - 1] not in cuts, "two regions in one block"
        cuts[order[labels - 1]] = (region, labels)
CALL = re.compile(r"^\s*andThen \((\w+) ")
script: dict[str, list[str]] = {}
modules = ["Whole", "Base", "Cand"]
for name, ls in lines_of.items():
    steps = ["sim_unfold", "sim_same"]
    start = None
    if name in cuts:
        region, labels = cuts[name]
        start = "v" + str(int(re.match(r"^\s*%(\d+) = ", IR[region["lines"][0] - 1]).group(1)) - labels)
    cut = False
    for i in ls:
        m = CALL.match(A[i])
        if m and m.group(1) in callees:
            assert not cut, f"line {i + 1}: a call after a region's start, in its block"
            theorem, module = callees[m.group(1)]
            modules.append(module)
            steps += [f"call_same {theorem}", "sim_same"]
        elif start and re.match(rf"^\s*let {start} :=", A[i]):
            cut = True
            n = region["region"]
            modules.append(f"T{n}")
            p = " ".join(f"v{int(p[1:]) - labels}" for p in region["params"])
            steps.append(f"sim_at {start}")
            for k in range(len(region["outputs"])):
                steps.append(
                    f"cut_store (r{n}_o{k}_same {p}) (R{n}Src.r{n}_o{k}_src.step (.bb1 {p}))"
                    f" (R{n}Tgt.r{n}_o{k}_tgt.step (.bb1 {p}))"
                )
            steps.append("sim_same")
    assert cut == (name in cuts), f"{name}: its region's first value isn't in its code"
    script[name] = [*steps, "sim_end"]

src = f"Base.{fn}"
tgt = f"Cand.{fn}"
rel = "(Next.Rel (fun b b' => same b = b') Eq)"
out = [
    *[f"import {m}" for m in dict.fromkeys(modules)],
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
        *[f"  {s}" for s in script[name]],
        "",
    ]

out += [
    "/-- Blocks that are the same block step to the same block, or return the same result and memory. -/",
    f"theorem step_sim (b : {src}.Block) (b' : {tgt}.Block) (h : same b = b') :",
    f"    Outcome.Sim {rel} ({src}.step b) ({tgt}.step b') := by",
    "  subst h",
    "  cases b with",
]
indent = "  "
for g in groups or [""]:
    if g:
        out += [f"  | g{g[1:]} b =>", "    cases b with"]
        indent = "    "
    for group, (name, _, fields) in blocks:
        if group == g:
            out.append(f"{indent}| {name} {' '.join(fields)} => exact step_{name} {' '.join(fields)}".rstrip())
out += [
    "",
    "/-- They're under the loops' promise together. -/",
    f"theorem promise_eq (b : {src}.Block) (b' : {tgt}.Block) (h : same b = b') :",
    f"    {tgt}.promise b' = {src}.promise b := by",
    "  subst h",
    f"  rcases b with {' | '.join('b' for _ in groups)} <;> cases b <;> rfl" if groups else "  cases b <;> rfl",
    "",
    Path(main).read_text().rstrip(),
    "",
    f"end {namespace}",
]
print("\n".join(out))
