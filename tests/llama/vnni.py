#!/usr/bin/env python3
"""Rewrites clang's IR for llama.cpp's q4_K kernels to use VNNI, which clang -O3 doesn't.

For each block of quantized weights, clang leaves

  %p_k = pmaddubsw(a_k, b_k)                k = 0 to 7, <2N x i16>
  %s   = an add tree over the eight %p_k    <2N x i16>
  %r   = pmaddwd(%s, %c)                    <N x i32>

and this makes it

  %d_0 = vpdpbusd(0, a_0, b_0)  ...  %d_7 = vpdpbusd(%d_6, a_7, b_7)
  %r   = mul %d_7, sext(the low half of each 32-bit lane of %c)

keeping the name %r, so everything after it is untouched. That's only the same when no pmaddubsw saturates, no
16-bit add wraps, and the two halves of each 32-bit lane of %c are equal. Nothing here checks that.
tests/llama/Vnni.lean proves it of each place this rewrites, from the instructions that compute the operands.

usage: vnni.py IN.ll OUT.ll FUNCTION... [--report REPORT.json] [--mutant NAME]

`--mutant` writes a wrong rewrite on purpose, which the proofs and tests/llama/native_check.py have to reject:
`signs` swaps which operand of each vpdpbusd is unsigned, `seven` leaves out the last vpdpbusd, and `scale`
multiplies by the whole 32-bit lane of %c.
"""

import json
import re
import sys
from pathlib import Path

NAME = r"%[\w.]+"
CALL = re.compile(rf"^  ({NAME}) = tail call <(\d+) x (i\d+)> @(llvm\.x86\.[\w.]+)\((.*)\)$")
ADD = re.compile(rf"^  ({NAME}) = add <(\d+) x i16> ({NAME}), ({NAME})$")
OPERAND = re.compile(rf"<\d+ x i\d+> ({NAME})")
MADDUBS = {"llvm.x86.avx2.pmadd.ub.sw": 256, "llvm.x86.avx512.pmaddubs.w.512": 512}
MADDWD = {"llvm.x86.avx2.pmadd.wd": 256, "llvm.x86.avx512.pmaddw.d.512": 512}
DPBUSD = {256: "llvm.x86.avx512.vpdpbusd.256", 512: "llvm.x86.avx512.vpdpbusd.512"}
MUTANTS = ("signs", "seven", "scale")


def found(m: re.Match[str] | None, what: str) -> re.Match[str]:
    """A match that has to be there."""
    if m is None:
        raise SystemExit(f"no {what}")
    return m


def uses(body: list[str], name: str) -> int:
    pattern = re.compile(re.escape(name) + r"(?![\w.])")
    return sum(len(pattern.findall(line.split(" = ", 1)[1] if " = " in line else line)) for line in body)


def walk(
    body: list[str], defs: dict[str, int], name: str, bits: int, leaves: list[int], tree: list[int]
) -> bool:
    """Collects the add tree under `name`: its leaves, left to right, and its adds. Each value in it has to
    have one use, its parent."""
    j = defs.get(name)
    if j is None or uses(body, name) != 1:
        return False
    if a := ADD.match(body[j]):
        tree.append(j)
        return walk(body, defs, a.group(3), bits, leaves, tree) and walk(
            body, defs, a.group(4), bits, leaves, tree
        )
    cm = CALL.match(body[j])
    if cm and MADDUBS.get(cm.group(4)) == bits:
        leaves.append(j)
        return True
    return False


def rewrite_function(body: list[str], fn: str, report: list, mutant: str | None) -> list[str]:
    defs = {}
    for i, line in enumerate(body):
        m = re.match(rf"^  ({NAME}) = ", line)
        if m:
            defs[m.group(1)] = i
    remove: set[int] = set()
    replace: dict[int, list[str]] = {}
    for i, line in enumerate(body):
        m = CALL.match(line)
        if not m or m.group(4) not in MADDWD:
            continue
        bits, lanes, result = MADDWD[m.group(4)], int(m.group(2)), m.group(1)
        s, c = OPERAND.findall(m.group(5))
        leaves: list[int] = []
        tree: list[int] = []
        if not walk(body, defs, s, bits, leaves, tree) or len(leaves) != 8:
            continue
        tag = f"%vnni.{result[1:]}"
        acc, new = "zeroinitializer", []
        for k, j in enumerate(leaves[:7] if mutant == "seven" else leaves):
            a, b = OPERAND.findall(found(CALL.match(body[j]), body[j]).group(5))
            if mutant == "signs":
                a, b = b, a
            new.append(
                f"  {tag}.{k} = tail call <{lanes} x i32> @{DPBUSD[bits]}(<{lanes} x i32> {acc}, "
                f"<{lanes * 4} x i8> {a}, <{lanes * 4} x i8> {b})"
            )
            acc = f"{tag}.{k}"
        new.append(f"  {tag}.scale = bitcast <{lanes * 2} x i16> {c} to <{lanes} x i32>")
        if mutant == "scale":
            new.append(f"  {result} = mul <{lanes} x i32> {acc}, {tag}.scale")
        else:
            new += [
                f"  {tag}.hi = shl <{lanes} x i32> {tag}.scale, splat (i32 16)",
                f"  {tag}.s = ashr <{lanes} x i32> {tag}.hi, splat (i32 16)",
                f"  {result} = mul <{lanes} x i32> {acc}, {tag}.s",
            ]
        replace[i] = new
        remove.update(leaves)
        remove.update(tree)
        report.append({"function": fn, "pmaddwd": result, "width": bits})
    out = []
    for i, line in enumerate(body):
        if i in remove:
            continue
        if i in replace:
            out += replace[i]
        # Use-list orders in a rewritten function no longer match its uses, and don't change what it computes.
        elif not (replace and line.lstrip().startswith("uselistorder")):
            out.append(line)
    return out


def main() -> int:
    args = sys.argv[1:]
    report_path = mutant = None
    if "--report" in args:
        k = args.index("--report")
        report_path = args[k + 1]
        del args[k : k + 2]
    if "--mutant" in args:
        k = args.index("--mutant")
        mutant = args[k + 1]
        del args[k : k + 2]
        if mutant not in MUTANTS:
            sys.exit(f"no mutant {mutant}: {MUTANTS}")
    src, dst, *functions = args
    lines = Path(src).read_text().split("\n")
    out: list[str] = []
    report: list = []
    i = 0
    while i < len(lines):
        m = re.match(r"^define .*@([\w.]+)\(", lines[i])
        if m and m.group(1) in functions:
            j = lines.index("}", i)
            out += [lines[i], *rewrite_function(lines[i + 1 : j], m.group(1), report, mutant), "}"]
            i = j + 1
        else:
            out.append(lines[i])
            i += 1
    # Module-level use-list orders of intrinsics whose calls changed no longer match either.
    changed = (*MADDUBS, *MADDWD, *DPBUSD.values())
    text = "\n".join(
        line
        for line in out
        if not (line.startswith("uselistorder") and any(f"@{n}," in line for n in changed))
    )
    for bits, name in DPBUSD.items():
        lanes = bits // 32
        if f"@{name}(" in text and f"declare <{lanes} x i32> @{name}(" not in text:
            operands = f"<{lanes} x i32>, <{lanes * 4} x i8>, <{lanes * 4} x i8>"
            text += f"\ndeclare <{lanes} x i32> @{name}({operands})\n"
    Path(dst).write_text(text)
    counts: dict[str, int] = {}
    for r in report:
        counts[r["function"]] = counts.get(r["function"], 0) + 1
    print(f"rewrote {len(report)} places: {counts}", file=sys.stderr)
    if report_path:
        Path(report_path).write_text(json.dumps(report, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
