#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks the model's scalable vectors, IRLean/Scalable.lean, through the emitter. Alive2 can't read them, so
this ties them to what can be checked:

  - Each operation on `<vscale x N x iW>`, run with `vscale` 1, 2 and 4, has to give exactly what the same
    operation on `<vscale*N x iW>` gives, lane for lane, poison and undefined behavior included, on random
    inputs with poison lanes. The fixed-width operations are checked against Alive2 and LLVM's constant folder
    by tests/opcheck.py, tests/vecopcheck.py and the differential tests.
  - LLVM's constant folder, on splats: each operation on scalable splat constants, which `opt` folds without
    knowing `vscale`, has to give that splat in every lane, for each `vscale`.
  - `llvm.vscale` gives `vscale`, or poison where it doesn't fit the result, and a function with
    `vscale_range` is undefined exactly outside the range, as LangRef says.

usage: tests/scalablecheck.py path/to/ir-lean
"""

import os
import random
import re
import shutil
import sys
import tempfile

from differential import NATIVE, lean_output
from opcheck import lean_env, sh

sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools"))
from irlean import proc

POISON = -1
LOGS = (0, 1, 2)


def operations():
    """Each operation as (name, lanes N, width W, result shape, argument shapes, body defining %r,
    declarations). A shape is ("v", W) for a vector of N lanes of iW, ("s", W) for a scalar iW. `VTY` in a
    body is the vector type, scalable or fixed, and `SUF` its intrinsic suffix."""
    ops = []
    n, w = 4, 8
    v, s = ("v", w), ("s", w)
    for op in [
        "add",
        "sub",
        "mul",
        "shl",
        "lshr",
        "ashr",
        "and",
        "or",
        "xor",
        "add nsw",
        "shl nuw",
        "lshr exact",
    ]:
        ops.append((op.replace(" ", "_"), n, w, v, [v, v], f"%r = {op} VTY %a0, %a1", []))
    for op in ["udiv", "sdiv", "urem", "srem"]:
        ops.append((op, n, w, v, [v, v], f"%r = {op} VTY %a0, %a1", []))
    ops.append(("icmp_ult", n, w, ("v", 1), [v, v], "%r = icmp ult VTY %a0, %a1", []))
    ops.append(("select", n, w, v, [("v", 1), v, v], "%r = select BTY %a0, VTY %a1, VTY %a2", []))
    ops.append(("zext", n, w, ("v", 16), [v], "%r = zext VTY %a0 to WTY", []))
    ops.append(("trunc", n, w, ("v", 4), [v], "%r = trunc VTY %a0 to NTY", []))
    for f in ["umin", "smax", "uadd.sat", "ssub.sat"]:
        ops.append(
            (
                f.replace(".", "_"),
                n,
                w,
                v,
                [v, v],
                f"%r = call VTY @llvm.{f}.SUF(VTY %a0, VTY %a1)",
                [f"declare VTY @llvm.{f}.SUF(VTY, VTY)"],
            )
        )
    for f in ["ctpop", "bitreverse"]:
        ops.append(
            (f, n, w, v, [v], f"%r = call VTY @llvm.{f}.SUF(VTY %a0)", [f"declare VTY @llvm.{f}.SUF(VTY)"])
        )
    ops.append(
        (
            "ctlz",
            n,
            w,
            v,
            [v],
            "%r = call VTY @llvm.ctlz.SUF(VTY %a0, i1 false)",
            ["declare VTY @llvm.ctlz.SUF(VTY, i1)"],
        )
    )
    ops.append(
        (
            "fshl",
            n,
            w,
            v,
            [v, v, v],
            "%r = call VTY @llvm.fshl.SUF(VTY %a0, VTY %a1, VTY %a2)",
            ["declare VTY @llvm.fshl.SUF(VTY, VTY, VTY)"],
        )
    )
    ops.append(
        (
            "uaddo",
            n,
            w,
            ("v", 1),
            [v, v],
            "%p = call { VTY, BTY } @llvm.uadd.with.overflow.SUF(VTY %a0, VTY %a1)\n  %r = extractvalue { "
            "VTY, BTY } %p, 1",
            ["declare { VTY, BTY } @llvm.uadd.with.overflow.SUF(VTY, VTY)"],
        )
    )
    for f in ["add", "umax", "xor"]:
        ops.append(
            (
                f"reduce_{f}",
                n,
                w,
                s,
                [v],
                f"%r = call i{w} @llvm.vector.reduce.{f}.SUF(VTY %a0)",
                [f"declare i{w} @llvm.vector.reduce.{f}.SUF(VTY)"],
            )
        )
    ops.append(("extract", n, w, s, [v, ("s", 32)], "%r = extractelement VTY %a0, i32 %a1", []))
    ops.append(("insert", n, w, v, [v, s, ("s", 32)], "%r = insertelement VTY %a0, i8 %a1, i32 %a2", []))
    ops.append(
        (
            "splat",
            n,
            w,
            v,
            [s],
            "%i = insertelement VTY poison, i8 %a0, i64 0\n  %r = shufflevector VTY %i, VTY poison, MTY "
            "zeroinitializer",
            [],
        )
    )
    ops.append(
        (
            "reverse",
            n,
            w,
            v,
            [v],
            "%r = call VTY @llvm.vector.reverse.SUF(VTY %a0)",
            ["declare VTY @llvm.vector.reverse.SUF(VTY)"],
        )
    )
    ops.append(
        (
            "stepvector",
            n,
            w,
            v,
            [],
            "%r = call VTY @llvm.stepvector.SUF()",
            ["declare VTY @llvm.stepvector.SUF()"],
        )
    )
    # A fixed part into or out of a scalable vector, at lane 2, and a scalable half at the second half, whose
    # start is its index times vscale.
    ops.append(
        (
            "insert_fixed",
            n,
            w,
            v,
            [v, ("f", w)],
            "%r = call VTY @llvm.vector.insert.SUF.v2i8(VTY %a0, <2 x i8> %a1, i64 2)",
            ["declare VTY @llvm.vector.insert.SUF.v2i8(VTY, <2 x i8>, i64)"],
        )
    )
    ops.append(
        (
            "extract_fixed",
            n,
            w,
            ("f", w),
            [v],
            "%r = call <2 x i8> @llvm.vector.extract.v2i8.SUF(VTY %a0, i64 2)",
            ["declare <2 x i8> @llvm.vector.extract.v2i8.SUF(VTY, i64)"],
        )
    )
    ops.append(
        (
            "insert_half",
            n,
            w,
            v,
            [v, ("h", w)],
            "%r = call VTY @llvm.vector.insert.SUF.HSUF(VTY %a0, HTY %a1, i64 HIDX)",
            ["declare VTY @llvm.vector.insert.SUF.HSUF(VTY, HTY, i64)"],
        )
    )
    ops.append(
        (
            "extract_half",
            n,
            w,
            ("h", w),
            [v],
            "%r = call HTY @llvm.vector.extract.HSUF.SUF(VTY %a0, i64 HIDX)",
            ["declare HTY @llvm.vector.extract.HSUF.SUF(VTY, i64)"],
        )
    )
    ops.append(("constant_splat", n, w, v, [v], "%r = add VTY %a0, splat (i8 5)", []))
    ops.append(("zeroinitializer", n, w, v, [v], "%r = or VTY %a0, zeroinitializer", []))
    return ops


def types(n, w, k):
    """The vector types an operation's body names, for `k` the fixed-width lanes, or None for scalable."""

    def vt(width):
        return f"<vscale x {n} x i{width}>" if k is None else f"<{k * n} x i{width}>"

    suffix = f"nxv{n}i{w}" if k is None else f"v{k * n}i{w}"
    half = f"<vscale x {n // 2} x i{w}>" if k is None else f"<{k * n // 2} x i{w}>"
    return {
        "VTY": vt(w),
        "BTY": vt(1),
        "WTY": vt(16),
        "NTY": vt(4),
        "MTY": vt(32),
        "SUF": suffix,
        # Half a vector, scalable or fixed, and the index of the second half, which vscale scales in a
        # scalable one.
        "HTY": half,
        "HSUF": f"nxv{n // 2}i{w}" if k is None else f"v{k * n // 2}i{w}",
        "HIDX": str(n // 2) if k is None else str(k * n // 2),
    }


def substitute(text, table):
    for key, value in table.items():
        text = text.replace(key, value)
    return text


def shape_type(shape, table):
    kind, width = shape
    if kind == "s":
        return f"i{width}"
    if kind == "h":
        return table["HTY"]
    if kind == "f":
        return "<2 x i8>"
    return {8: table["VTY"], 1: table["BTY"], 16: table["WTY"], 4: table["NTY"]}[width]


def module(ops, k):
    """Every operation as a function, scalable if `k` is None and otherwise on `k * N` lanes."""
    decls, funcs = set(), []
    for name, n, w, ret, args, body, ds in ops:
        table = types(n, w, k)
        decls.update(substitute(d, table) for d in ds)
        params = ", ".join(f"{shape_type(a, table)} %a{i}" for i, a in enumerate(args))
        funcs.append(
            f"define {shape_type(ret, table)} @op_{name}({params}) {{\n  {substitute(body, table)}\n"
            f"  ret {shape_type(ret, table)} %r\n}}\n"
        )
    return "\n".join(sorted(decls)) + "\n\n" + "\n".join(funcs)


def lanes(rand, count, width):
    out = []
    for _ in range(count):
        r = rand.random()
        out.append(
            POISON
            if r < 0.1
            else rand.choice([0, 1, (1 << width) - 1])
            if r < 0.3
            else rand.getrandbits(width)
        )
    return out


def cases(op, k, rand):
    _, n, _, _, args, _, _ = op
    out = []
    for _ in range(8):
        case = []
        for kind, width in args:
            if kind == "s":
                case.append([rand.randrange(k * n + 1) if width == 32 else lanes(rand, 1, width)[0]])
            elif kind == "h":
                case.append(lanes(rand, k * n // 2, width))
            elif kind == "f":
                case.append(lanes(rand, 2, width))
            else:
                case.append(lanes(rand, k * n, width))
        out.append(case)
    return out


def lean_value(shape, values, scalable_log):
    """A Lean term for an argument."""
    kind, width = shape
    if kind == "s":
        x = values[0]
        return "none" if x == POISON else f"(some {x}#{width})"
    items = ", ".join("none" if x == POISON else f"some {x}#{width}" for x in values)
    per = 2 if kind == "h" else 4
    count = (
        f"(VScale.val ⟨{scalable_log}⟩ * {per})"
        if scalable_log is not None and kind != "f"
        else str(len(values))
    )
    return f"(⟨#[{items}], by decide⟩ : Vec {count} {width})"


def run_model(tool, ops, work):
    """For each operation, each `vscale`, and each case: (scalable result, fixed result), as printed."""
    for label, k in [("S", None), *[(f"F{2**g}", 2**g) for g in LOGS]]:
        path = os.path.join(work, f"{label}.ll")
        with open(path, "w") as f:
            f.write(module(ops, k))
        r = proc.run([tool, path, "-o", os.path.join(work, f"{label}.lean"), "--namespace", label])
        if r.exit != 0:
            sys.exit(f"the emitter left operations out of {label}:\n{r.err}")
    rand = random.Random(41)
    src = [
        "import S",
        *[f"import F{2**g}" for g in LOGS],
        "set_option maxHeartbeats 0",
        "open IRLean",
        "def showVal {w : Nat} : Val w → String",
        "  | some v => toString v.toNat",
        f'  | none => "{POISON}"',
        "class Shows (α : Type) where shows : α → String",
        "instance : Shows (Val w) := ⟨showVal⟩",
        'instance : Shows (Vec n w) := ⟨fun v => " ".intercalate (v.toList.map showVal)⟩',
        "def showOut {α : Type} [Shows α] : Outcome α → String",
        "  | some (.ok v) => Shows.shows v",
        '  | some (.error (.undefined _)) => "ub"',
        '  | some (.error (.model _)) => "stop"',
        '  | none => "diverged"',
    ]
    lines = []
    count = 0
    for op in ops:
        name, _, _, _, args, _, _ = op
        for g in LOGS:
            k = 2**g
            for case in cases(op, k, rand):
                scalable = " ".join(lean_value(a, c, g) for a, c in zip(args, case, strict=True))
                fixed = " ".join(lean_value(a, c, None) for a, c in zip(args, case, strict=True))
                lines.append(
                    f'  IO.println ("{name} {k} " ++ showOut (S.op_{name} ⟨{g}⟩ {scalable}) ++ " | " ++ '
                    f"showOut (F{k}.op_{name} {fixed}))"
                )
                count += 1
    chunk = 60
    runners = []
    for i in range(0, len(lines), chunk):
        src.append(f"def r{i} : IO Unit := do\n" + "\n".join(lines[i : i + chunk]))
        runners.append(f"r{i}")
    src.append("def main : IO Unit := do\n" + "\n".join(f"  {r}" for r in runners))
    drive = os.path.join(work, "Drive.lean")
    with open(drive, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_modules():
        for label in ["S", *[f"F{2**g}" for g in LOGS]]:
            sh(
                [
                    "lean",
                    "-R",
                    work,
                    "-o",
                    os.path.join(work, f"{label}.olean"),
                    os.path.join(work, f"{label}.lean"),
                ],
                env=env,
            )

    out = lean_output(work, ["lean", *NATIVE, "--run", drive], env, compile_modules).splitlines()
    if len(out) != count:
        sys.exit(f"Lean printed {len(out)} results, not {count}")
    return out


SPLATS = [
    ("add", "add <vscale x 4 x i8> splat (i8 7), splat (i8 250)"),
    ("mul", "mul <vscale x 4 x i8> splat (i8 7), splat (i8 9)"),
    ("udiv", "udiv <vscale x 4 x i8> splat (i8 200), splat (i8 7)"),
    ("shl", "shl <vscale x 4 x i8> splat (i8 3), splat (i8 5)"),
    ("xor", "xor <vscale x 4 x i8> splat (i8 85), splat (i8 15)"),
    (
        "umin",
        "call <vscale x 4 x i8> @llvm.umin.nxv4i8(<vscale x 4 x i8> splat (i8 9), <vscale x 4 x i8> splat "
        "(i8 4))",
    ),
    ("ctpop", "call <vscale x 4 x i8> @llvm.ctpop.nxv4i8(<vscale x 4 x i8> splat (i8 183))"),
]


def check_folder(tool, work):
    """Each operation on splats, folded by `opt`, against the model at each `vscale`."""
    decls = (
        "declare <vscale x 4 x i8> @llvm.umin.nxv4i8(<vscale x 4 x i8>, <vscale x 4 x i8>)\n"
        "declare <vscale x 4 x i8> @llvm.ctpop.nxv4i8(<vscale x 4 x i8>)\n"
    )
    text = decls + "".join(
        f"define <vscale x 4 x i8> @{name}() {{\n  %r = {body}\n  ret <vscale x 4 x i8> %r\n}}\n"
        for name, body in SPLATS
    )
    path = os.path.join(work, "splats.ll")
    with open(path, "w") as f:
        f.write(text)
    folded = sh(["opt", "-passes=instsimplify", "-S", path]).out
    expected = {}
    for m in re.finditer(
        r"define <vscale x 4 x i8> @(\w+)\(\) [^{]*\{\n\s*ret <vscale x 4 x i8> splat \(i8 (-?\d+)\)", folded
    ):
        expected[m.group(1)] = int(m.group(2)) & 0xFF
    r = proc.run([tool, path, "-o", os.path.join(work, "Splats.lean"), "--namespace", "Splats"])
    if r.exit != 0:
        sys.exit(f"the emitter left splats out:\n{r.err}")
    src = ["import Splats", "open IRLean"]
    src.append("def showLanes : Outcome (Vec n 8) → String")
    src.append(
        '  | some (.ok v) => " ".intercalate (v.toList.map fun x => match x with '
        '| some y => toString y.toNat | none => "p")'
    )
    src.append('  | _ => "other"')
    src.append("def main : IO Unit := do")
    for name, _ in SPLATS:
        for g in LOGS:
            src.append(f'  IO.println ("{name} {g} " ++ showLanes (Splats.{name} ⟨{g}⟩))')
    drive = os.path.join(work, "DriveSplats.lean")
    with open(drive, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_splats():
        sh(
            ["lean", "-R", work, "-o", os.path.join(work, "Splats.olean"), os.path.join(work, "Splats.lean")],
            env=env,
        )

    out = lean_output(work, ["lean", *NATIVE, "--run", drive], env, compile_splats).splitlines()
    wrong, agreed = [], 0
    for line in out:
        name, g, *vals = line.split()
        if name not in expected:
            wrong.append(f"{name}: opt didn't fold it to a splat")
            continue
        want = [str(expected[name])] * (4 * 2 ** int(g))
        if vals != want:
            wrong.append(
                f"{name} at vscale {2 ** int(g)}: the model gives {' '.join(vals)}, opt folds to "
                f"{expected[name]}"
            )
        else:
            agreed += 1
    return agreed, wrong


VSCALE = """declare i64 @llvm.vscale.i64()
declare i2 @llvm.vscale.i2()
define i64 @vs64() {
  %r = call i64 @llvm.vscale.i64()
  ret i64 %r
}
define i2 @vs2() {
  %r = call i2 @llvm.vscale.i2()
  ret i2 %r
}
define i8 @ranged() vscale_range(2,4) {
  ret i8 0
}
define i8 @unbounded() vscale_range(2,0) {
  ret i8 0
}
"""


def check_vscale(tool, work):
    """`llvm.vscale`, and `vscale_range` undefined exactly outside its range, for vscale 1 to 16."""
    path = os.path.join(work, "vscale.ll")
    with open(path, "w") as f:
        f.write(VSCALE)
    r = proc.run([tool, path, "-o", os.path.join(work, "VS.lean"), "--namespace", "VS"])
    if r.exit != 0:
        sys.exit(f"the emitter left vscale out:\n{r.err}")
    src = [
        "import VS",
        "open IRLean",
        "def showOut : Outcome (Val w) → String",
        "  | some (.ok (some v)) => toString v.toNat",
        '  | some (.ok none) => "poison"',
        '  | some (.error (.undefined _)) => "ub"',
        '  | _ => "other"',
        "def main : IO Unit := do",
    ]
    for g in range(5):
        for f in ["vs64", "vs2", "ranged", "unbounded"]:
            src.append(f'  IO.println ("{f} {2**g} " ++ showOut (VS.{f} ⟨{g}⟩))')
    drive = os.path.join(work, "DriveVS.lean")
    with open(drive, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_vs():
        sh(["lean", "-R", work, "-o", os.path.join(work, "VS.olean"), os.path.join(work, "VS.lean")], env=env)

    out = lean_output(work, ["lean", *NATIVE, "--run", drive], env, compile_vs).splitlines()
    wrong = []
    for line in out:
        f, k, got = line.split()
        k = int(k)
        want = {
            "vs64": str(k),
            # LangRef: "If the result value does not fit in the result type, then the result is a poison
            # value."
            "vs2": str(k) if k < 4 else "poison",
            "ranged": "0" if 2 <= k <= 4 else "ub",
            "unbounded": "0" if k >= 2 else "ub",
        }[f]
        if got != want:
            wrong.append(f"{f} at vscale {k}: the model gives {got}, LangRef {want}")
    return len(out) - len(wrong), wrong


def main():
    tool = os.path.abspath(sys.argv[1])
    ops = operations()
    work = tempfile.mkdtemp(prefix="scalablecheck-")
    failed = False
    try:
        out = run_model(tool, ops, work)
        differ = [line for line in out if line.split(" ", 2)[2].split(" | ")[0] != line.split(" | ")[1]]
        undefined = sum(" ub | " in line for line in out)
        print(
            f"{len(ops)} operations, {len(out)} inputs at vscale 1, 2 and 4: {len(out) - len(differ)} the "
            f"same as on "
            f"fixed-width vectors, {undefined} of them undefined, {len(differ)} different"
        )
        for line in differ[:15]:
            print("  WRONG", line[:300])
        agreed, fwrong = check_folder(tool, work)
        print(f"constant folder: {agreed} splats folded the same at each vscale, {len(fwrong)} wrong")
        for w in fwrong[:10]:
            print("  WRONG", w)
        right, vwrong = check_vscale(tool, work)
        print(f"llvm.vscale and vscale_range: {right} as LangRef says, {len(vwrong)} wrong")
        for w in vwrong[:10]:
            print("  WRONG", w)
        failed = bool(differ or fwrong or vwrong) or not undefined or not agreed
        print("FAIL" if failed else "ok")
    finally:
        shutil.rmtree(work, ignore_errors=True)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
