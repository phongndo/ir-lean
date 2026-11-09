#!/usr/bin/env python3
"""Cuts each place vnni.py rewrote out of a kernel, before and after, as two functions ir-lean can
translate, and checks that those places are everything that changed.

The slice of a value %R is everything %R is a pure function of. Values are SSA, so an instruction in a block
that dominates the use gives the same value wherever it's read, and the slice follows definitions into other
blocks. It stops at what isn't a pure function of its operands alone: loads, phis, `select`s and comparisons
it has no rule to cut through, stack slots and addresses, calls that aren't one of the dot-product intrinsics,
and the function's arguments. `freeze` is cut too: it picks some value, and a theorem for every value of a
parameter covers whichever it picks. What's cut becomes a parameter, so a theorem about the slice holds
whatever those values are.

Both slices of a place take the same parameters in the same order, and every line of a slice is a line of the
kernel, as is apart from attribute groups and metadata. Then, for the theorem about each slice to say the
rewritten kernel computes what clang's did, this checks that the two kernels differ only in slices, in
order: lined up as a diff, every line clang's kernel has and the rewritten one doesn't is in a source slice,
every line the other way is in a target slice, and every other line is where it was. Which lines each has
isn't enough, since moving a store into another block changes what the kernel does and keeps the same lines.
A slice's lines only compute values, so they can move, but none the rewrite puts somewhere may divide, which
could be undefined where nothing was before. The rewrite keeps the name %R, so the rest of the kernel reads
the same value.

usage: slices.py ORIGINAL.ll REWRITTEN.ll REPORT.json OUT_DIR
Writes OUT_DIR/<name>.src.ll and OUT_DIR/<name>.tgt.ll for each place, and OUT_DIR/slices.json.
"""

import difflib
import json
import re
import sys
from pathlib import Path

NAME = r"%[\w.]+"
TYPE = r"(?:i\d+|ptr|<\d+ x i\d+>)"
DEF = re.compile(rf"^  ({NAME}) = (.*)$")
LAYOUT = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
DECLS = {
    "llvm.x86.avx2.pmadd.ub.sw": "<16 x i16> @llvm.x86.avx2.pmadd.ub.sw(<32 x i8>, <32 x i8>)",
    "llvm.x86.avx512.pmaddubs.w.512": "<32 x i16> @llvm.x86.avx512.pmaddubs.w.512(<64 x i8>, <64 x i8>)",
    "llvm.x86.avx2.pmadd.wd": "<8 x i32> @llvm.x86.avx2.pmadd.wd(<16 x i16>, <16 x i16>)",
    "llvm.x86.avx512.pmaddw.d.512": "<16 x i32> @llvm.x86.avx512.pmaddw.d.512(<32 x i16>, <32 x i16>)",
    "llvm.x86.avx512.vpdpbusd.256": (
        "<8 x i32> @llvm.x86.avx512.vpdpbusd.256(<8 x i32>, <32 x i8>, <32 x i8>)"
    ),
    "llvm.x86.avx512.vpdpbusd.512": (
        "<16 x i32> @llvm.x86.avx512.vpdpbusd.512(<16 x i32>, <64 x i8>, <64 x i8>)"
    ),
}
# Opcodes whose operands after the first are untyped and share its type.
BINARY = {"add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "udiv", "sdiv", "urem", "srem"}
FLAGS = {"nuw", "nsw", "exact", "disjoint", "nneg", "samesign"}
CUT = re.compile(r"^(load|phi|alloca|getelementptr|select|icmp|extractvalue|insertvalue|freeze) ")
# What a slice can have that may be undefined on some input, and so can't be put where it wasn't.
DIVIDES = re.compile(r"^\s*%[\w.]+ = [us](div|rem) ")


def found(m: re.Match[str] | None, what: str) -> re.Match[str]:
    """A match that has to be there."""
    if m is None:
        raise SystemExit(f"no {what}")
    return m


def function_body(text: str, name: str) -> list[str]:
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if re.match(rf"^define .*@{re.escape(name)}\(", line):
            return lines[i + 1 : lines.index("}", i)]
    raise SystemExit(f"no function {name}")


def operand_types(rhs: str) -> dict[str, str]:
    """The type of each value an instruction uses."""
    words = rhs.split(" ")
    if words[0] in BINARY:
        rest = words[1:]
        while rest and rest[0] in FLAGS:
            rest = rest[1:]
        ty = found(re.match(rf"^({TYPE})", " ".join(rest)), f"type in {rhs}").group(1)
        return dict.fromkeys(re.findall(rf"{NAME}(?![\w.])", rhs), ty)
    return {v: t for t, v in re.findall(rf"({TYPE}) ({NAME})(?![\w.])", rhs)}


def result_type(rhs: str) -> str:
    """The type an instruction produces, for the instructions slices end with."""
    m = re.match(rf"^(?:tail )?call (?:\w+ )*({TYPE}) ", rhs) or re.match(
        rf"^\w+ (?:(?:{'|'.join(FLAGS)}) )*({TYPE}) ", rhs
    )
    return found(m, f"result type of {rhs}").group(1)


def clean(line: str) -> str:
    """A kernel line as it goes in a slice: attribute groups belong to the module, and metadata isn't
    needed."""
    return re.sub(r",\s*!\w+ ![\w.]+", "", re.sub(r"\s*#\d+\s*$", "", line))


def slice_of(body: list[str], root: str) -> tuple[list[str], dict[str, str | None]]:
    """The lines `root` is a pure function of, each defined before its uses, and the values they're given."""
    defs = {}
    for i, line in enumerate(body):
        if d := DEF.match(line):
            defs[d.group(1)] = (i, d.group(2))
    order: list[int] = []
    seen: set[str] = set()
    params: dict[str, str | None] = {}

    def cut(rhs: str) -> bool:
        m = re.match(r"^(?:tail )?call .*@([\w.]+)\(", rhs)
        return bool(CUT.match(rhs)) or (bool(m) and m.group(1) not in DECLS)

    def visit(v: str, ty: str | None) -> None:
        if v in seen:
            if v in params and params[v] is None:
                params[v] = ty
            return
        seen.add(v)
        if v not in defs or cut(defs[v][1]):
            params[v] = ty
            return
        i, rhs = defs[v]
        types = operand_types(rhs)
        for u in re.findall(rf"{NAME}(?![\w.])", rhs):
            if u != v:
                visit(u, types.get(u))
        order.append(i)

    visit(root, None)
    return [body[i] for i in order], params


def module(
    name: str, header: str, lines: list[str], params: dict[str, str | None], root: str, ret: str
) -> str:
    used = sorted({m for line in lines for m in re.findall(r"@([\w.]+)\(", line)})
    plist = ", ".join(f"{t} {p}" for p, t in params.items())

    # Numbered values would have to be numbered in order, so every value gets a name instead.
    def named(s: str) -> str:
        return re.sub(r"%(\d+)(?![\w.])", r"%v\1", s)

    return (
        f"; {header}\n"
        f'target datalayout = "{LAYOUT}"\n'
        'target triple = "x86_64-unknown-linux-gnu"\n\n'
        + "".join(f"declare {DECLS[u]}\n" for u in used)
        + f"\ndefine {ret} @{name}({named(plist)}) {{\nentry:\n"
        + "\n".join(named(clean(line)) for line in lines)
        + f"\n  ret {ret} {named(root)}\n}}\n"
    )


def main() -> int:
    original, rewritten, report, out = (Path(a) for a in sys.argv[1:5])
    out.mkdir(parents=True, exist_ok=True)
    orig_text, rw_text = original.read_text(), rewritten.read_text()
    places = json.loads(report.read_text())
    index, covered = [], {}
    for n, place in enumerate(places):
        fn, root = place["function"], place["pmaddwd"]
        src_body, tgt_body = function_body(orig_text, fn), function_body(rw_text, fn)
        src_lines, src_params = slice_of(src_body, root)
        tgt_lines, tgt_params = slice_of(tgt_body, root)
        if src_params != tgt_params:
            raise SystemExit(f"{fn} {root}: the slices take different values\n{src_params}\n{tgt_params}")
        if None in src_params.values():
            raise SystemExit(f"{fn} {root}: couldn't tell a parameter's type: {src_params}")
        definition = next(line for line in src_body if line.startswith(f"  {root} = "))
        ret = result_type(found(DEF.match(definition), root).group(2))
        name = f"s{n:02d}"
        for kind, lines, file in (("src", src_lines, original), ("tgt", tgt_lines, rewritten)):
            header = f"{kind} slice {name}: {root} of {fn}, from {file.name}"
            (out / f"{name}.{kind}.ll").write_text(
                module(f"{name}_{kind}", header, lines, src_params, root, ret)
            )
        cover = covered.setdefault(fn, (set(), set()))
        cover[0].update(src_lines)
        cover[1].update(tgt_lines)
        index.append(
            {
                "name": name,
                "function": fn,
                "value": root,
                "params": len(src_params),
                "src_lines": len(src_lines),
                "tgt_lines": len(tgt_lines),
            }
        )
    # Every change is inside a slice, and every other line is where it was.
    for fn, (src_cover, tgt_cover) in covered.items():
        a = [line for line in function_body(orig_text, fn) if not line.lstrip().startswith("uselistorder")]
        b = [line for line in function_body(rw_text, fn) if not line.lstrip().startswith("uselistorder")]
        outside, removed, added = [], 0, 0
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if tag == "equal":
                continue
            outside += [f"- {line}" for line in a[i1:i2] if line not in src_cover]
            outside += [f"+ {line}" for line in b[j1:j2] if line not in tgt_cover or DIVIDES.match(line)]
            removed, added = removed + i2 - i1, added + j2 - j1
        if outside:
            raise SystemExit(
                f"{fn}: {len(outside)} changed lines aren't in any slice, or divide where nothing did, "
                f"such as\n" + "\n".join(outside[:5])
            )
        print(
            f"{fn}: all {removed} removed and {added} added lines are in slices, and every other line is "
            "where it was",
            file=sys.stderr,
        )
    (out / "slices.json").write_text(json.dumps(index, indent=1))
    print(f"wrote {len(index)} slice pairs to {out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
