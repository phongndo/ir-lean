#!/usr/bin/env python3
"""Cuts the regions where the candidate's IR differs from clang's into slices: docs/argon2.md. A prototype,
outside CI.

The two IRs have the same instructions under the same numbers, since clang compiled the same code with other
shuffles, so they're compared line by line. A region runs from the first to the last differing line of one
round. What it reads from before it becomes a parameter, and each value it defines that a `store` or a later
line reads is an output. For each output, this writes a source and a target function whose body is the
region's own lines that define a value, and which returns that output. It stops if the two versions of a
region don't take the same parameters and give the same outputs, or if a line of a region that defines
nothing isn't a `store`.

`uselistorder` lines differ too. They say in what order a value's uses are listed, and nothing of what the
code computes.

usage: regions.py BASE.ll CANDIDATE.ll OUT_DIR
Writes OUT_DIR/rN.src.ll and rN.tgt.ll for each region N, and OUT_DIR/regions.json.
"""

import json
import re
import sys
from pathlib import Path

base, cand, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
A, B = base.read_text().splitlines(), cand.read_text().splitlines()
assert len(A) == len(B)
DEF = re.compile(r"^\s*(%[\w.]+) = ")
USE = re.compile(r"%[\w.]+")
skip = ("; ModuleID", "source_filename", "  uselistorder")
differs = [i for i, (x, y) in enumerate(zip(A, B, strict=True)) if x != y and not x.startswith(skip)]
# Function bounds, by `define` and the closing brace.
bounds, start = [], None
for i, line in enumerate(A):
    if line.startswith("define"):
        start = i
    elif line == "}" and start is not None:
        bounds.append((start, i))
        start = None
# Regions: differing lines of one function, split where more than 60 lines pass with no difference.
regions = []
for lo, hi in bounds:
    mine = [i for i in differs if lo < i < hi]
    cur = []
    for i in mine:
        if cur and i - cur[-1] > 60:
            regions.append(cur)
            cur = []
        cur.append(i)
    if cur:
        regions.append(cur)
out.mkdir(parents=True, exist_ok=True)
report = []
for n, r in enumerate(regions):
    first, last = r[0], r[-1]
    fn = next((lo, hi) for lo, hi in bounds if lo < first < hi)
    for side, L in (("src", A), ("tgt", B)):
        whole = L[first : last + 1]
        # The lines that define a value are the slice. A store among them writes one of its outputs.
        body = [line for line in whole if DEF.match(line)]
        assert all(line.lstrip().startswith("store ") for line in whole if line not in body), n
        # And each is the same line in both versions: the argument from equal outputs to an equal function
        # rests on that.
        rest = [[x for x in V[first : last + 1] if not DEF.match(x)] for V in (A, B)]
        assert rest[0] == rest[1], n
        defined = [m[1] for line in body if (m := DEF.match(line))]
        used = [u for line in body for u in USE.findall(DEF.sub("", line))]
        params = sorted({u for u in used if u not in defined}, key=lambda s: int(s[1:]))
        after = [line for line in whole if line not in body] + [
            line for line in L[last + 1 : fn[1]] if not line.startswith("  uselistorder")
        ]
        later = {u for line in after for u in USE.findall(DEF.sub("", line))}
        outputs = [d for d in defined if d in later]
        if side == "src":
            src_params, src_outputs = params, outputs
        else:
            assert (params, outputs) == (src_params, src_outputs), (
                n,
                params,
                src_params,
                outputs,
                src_outputs,
            )
        text = []
        for k, o in enumerate(outputs):
            sig = ", ".join(f"<8 x i64> {p}" for p in params)
            text += [f"define <8 x i64> @r{n}_o{k}_{side}({sig}) {{", *body, f"  ret <8 x i64> {o}", "}", ""]
        # Numbered values have to be defined in order, so each gets a name.
        (out / f"r{n}.{side}.ll").write_text(re.sub(r"%(\d+)", r"%v\1", "\n".join(text)))
    same = [i for i in range(first, last + 1) if A[i] == B[i]]
    report.append(
        {
            "region": n,
            "lines": [first + 1, last + 1],
            "differing": len(r),
            "same": len(same),
            "params": src_params,
            "outputs": src_outputs,
        }
    )
    print(
        f"region {n}: lines {first + 1}-{last + 1}, {len(r)} differ, "
        f"params {src_params}, outputs {src_outputs}"
    )
# Every differing line is in a region, by construction; say what's outside.
(out / "regions.json").write_text(json.dumps(report, indent=1))
