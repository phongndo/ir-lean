#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks every floating-point operation in IRLean/Float.lean, through the emitter, against LLVM, as
tests/opcheck.py does for integers. docs/float.md has the design.

Each operation is an IR function that takes and returns bits: a float operand is an integer bitcast to its
format, and a float result is bitcast back, or an `i1` zero-extended to `i8`. The same function goes to four
places:

  - the model, through the emitter, run natively on every case;
  - LLVM's constant folder, `opt -passes=instsimplify`, with the operands as constants, poison among them;
  - the processor, through clang, for operands that aren't poison;
  - Alive2, for a sample: the function on constant operands against a function returning the model's
    result, both ways where the result isn't a NaN, and one way where it is.

A result that isn't a NaN has to be the same everywhere. Where IEEE 754 gives a NaN, LangRef 23.1.3 allows
either sign, and the preferred NaN or a NaN operand quieted or unchanged, with its payload's low bits dropped
or zeros added where the format changes. So a NaN from the constant folder or the processor has to be one of
those, and the model, run again under each of its sixteen choices of a NaN, has to give only those, and all of
them.

Under `nsz`, LangRef lets each operand that's a zero have its sign flipped, and on `uitofp`, `sitofp` and
`select`, whose flags apply to the result, a zero result's sign. The model chooses which, so where an operand
or the result is a zero, its results under every choice have to be the operation's without `nsz` on the
operands with their zeros' signs flipped every way, and nothing else.

At `half`, every operand of an operation of one operand is tried on the model and the processor, and the
operations of two have every edge value against every other, and random pairs. Other formats are sampled.

usage: tests/fpcheck.py path/to/ir-lean [--no-alive] [--no-native]

Without `alive-tv` on PATH this fails, unless `--no-alive` says that's fine. Only `fp128` may be skipped on
the processor, where the host has no library for its arithmetic, and that's said. `--no-native` skips the
processor.
"""

import os
import platform
import random
import re
import shutil
import sys
import tempfile

import alive
from differential import NATIVE, lean_output

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
from irlean import hashing, proc  # noqa: E402

# Exponent bits and significand bits, by IR type.
FORMATS = {"half": (5, 10), "bfloat": (8, 7), "float": (8, 23), "double": (11, 52), "fp128": (15, 112)}
SUFFIX = {"half": "f16", "bfloat": "bf16", "float": "f32", "double": "f64", "fp128": "f128"}
FCMP = "false oeq ogt oge olt ole one ord ueq ugt uge ult ule une uno true".split()
# `llvm.is.fpclass` and `nofpclass` masks: each class alone, and some unions LLVM's tests use.
MASKS = [1 << k for k in range(10)] + [0x3, 0x3FC, 0x204, 0x090, 0x060, 0x3FF, 0]
INTS = [8, 16, 32, 64]
POISON = "poison"
# The choices of a NaN: sign, unchanged or quieted, and which operand.
PICKS = range(16)
# With those, under `nsz`, whether each of up to two operands that's a zero has its sign flipped.
NSZ_PICKS = range(64)


def fwidth(ty):
    e, m = FORMATS[ty]
    return 1 + e + m


def is_nan(ty, x):
    e, m = FORMATS[ty]
    return (x >> m) & ((1 << e) - 1) == (1 << e) - 1 and x & ((1 << m) - 1) != 0


def nan_set(out, ins):
    """Every NaN LangRef allows of an operation on `ins`, (type, bits) pairs, with a result of type `out`."""
    e, m = FORMATS[out]
    top, sign, quiet = ((1 << e) - 1) << m, 1 << (e + m), 1 << (m - 1)
    allowed = {top | quiet, sign | top | quiet}
    for ty, x in ins:
        if not is_nan(ty, x):
            continue
        mi = FORMATS[ty][1]
        frac = x & ((1 << mi) - 1)
        p = frac >> (mi - m) if m <= mi else frac << (m - mi)
        for s in (0, sign):
            allowed.add(s | top | p | quiet)
            if p:
                allowed.add(s | top | p)
    return allowed


def is_zero(ty, x):
    e, m = FORMATS[ty]
    return x & ((1 << (e + m)) - 1) == 0


def op(ident, operands, result, body, decls=(), chooses=False, alive=True):
    """An operation: operands and result are ("f", type), ("i", width), or ("b",) for an `i1` result. With
    `nsz` among its flags, `nsz` says whether the flag flips the sign of zero operands, "in", or of a zero
    result, "out", and `base` names the same operation without the flag."""
    words = ident.split()
    return {
        "id": ident,
        "operands": operands,
        "result": result,
        "body": body,
        "decls": list(decls),
        "chooses": chooses,
        "alive": alive,
        "nsz": None,
        "base": " ".join(w for w in words if w != "nsz") if "nsz" in words else None,
    }


def nsz(o, kind):
    o["nsz"] = kind
    return o


def variants():
    out = []
    for ty in FORMATS:
        f, sfx = ("f", ty), SUFFIX[ty]
        for flags in ["", "nnan", "ninf", "nnan ninf", "nsz", "nnan nsz"]:
            out.append(nsz(op(f"fneg {flags} {ty}", [f], f, f"%r = fneg {flags} {ty} %a0"), "in"))
        fabs = f"declare {ty} @llvm.fabs.{sfx}({ty})"
        copysign = f"declare {ty} @llvm.copysign.{sfx}({ty}, {ty})"
        for flags in ["", "nnan", "ninf", "nsz"]:
            out.append(
                nsz(
                    op(
                        f"fabs {flags} {ty}",
                        [f],
                        f,
                        f"%r = call {flags} {ty} @llvm.fabs.{sfx}({ty} %a0)",
                        [fabs],
                    ),
                    "in",
                )
            )
            out.append(
                nsz(
                    op(
                        f"copysign {flags} {ty}",
                        [f, f],
                        f,
                        f"%r = call {flags} {ty} @llvm.copysign.{sfx}({ty} %a0, {ty} %a1)",
                        [copysign],
                    ),
                    "in",
                )
            )
        for p in FCMP:
            out.append(op(f"fcmp {p} {ty}", [f, f], ("b",), f"%r = fcmp {p} {ty} %a0, %a1"))
        # LangRef says only `nnan`, `ninf` and `reassoc` mean anything on `fcmp`, so the others are allowed
        # and change nothing. Alive2 approximates `arcp`, `contract` and `afn` wherever they are, so it can't
        # check those.
        for flags in ["nnan", "ninf", "nsz", "arcp contract afn"]:
            for p in ["olt", "ueq"]:
                out.append(
                    op(
                        f"fcmp {flags} {p} {ty}",
                        [f, f],
                        ("b",),
                        f"%r = fcmp {flags} {p} {ty} %a0, %a1",
                        alive="arcp" not in flags,
                    )
                )
        fpclass = f"declare i1 @llvm.is.fpclass.{sfx}({ty}, i32)"
        for k in MASKS:
            out.append(
                op(
                    f"is.fpclass {k} {ty}",
                    [f],
                    ("b",),
                    f"%r = call i1 @llvm.is.fpclass.{sfx}({ty} %a0, i32 {k})",
                    [fpclass],
                )
            )
        # Flags on `select` apply to the value it selects, which is the second operand here, and never to the
        # other.
        for flags in ["", "nnan", "ninf", "nnan ninf", "nsz", "nnan ninf nsz"]:
            out.append(
                nsz(
                    op(f"select {flags} {ty}", [f, f], f, f"%r = select {flags} i1 true, {ty} %a1, {ty} %a0"),
                    "out",
                )
            )
        # `nofpclass` on a call's argument, to `copysign` of the operand and itself, which is the operand.
        for k in [*MASKS[:10], 0x3, 0x3FC]:
            out.append(
                op(
                    f"nofpclass {k} {ty}",
                    [f],
                    f,
                    f"%r = call {ty} @llvm.copysign.{sfx}({ty} nofpclass({k}) %a0, {ty} %a0)",
                    [copysign],
                )
            )
        # The arithmetic, which chooses a NaN.
        for name in ["fadd", "fsub", "fmul", "fdiv", "frem"]:
            for flags in ["", "nnan", "ninf", "nsz", "ninf nsz"]:
                out.append(
                    nsz(
                        op(
                            f"{name} {flags} {ty}",
                            [f, f],
                            f,
                            f"%r = {name} {flags} {ty} %a0, %a1",
                            chooses=True,
                        ),
                        "in",
                    )
                )
        # Conversions to and from integers.
        for w in INTS:
            for name in ["fptoui", "fptosi"]:
                out.append(op(f"{name} {ty} i{w}", [f], ("i", w), f"%r = {name} {ty} %a0 to i{w}"))
            for name in ["uitofp", "sitofp"]:
                out.append(op(f"{name} i{w} {ty}", [("i", w)], f, f"%r = {name} i{w} %a0 to {ty}"))
        out.append(op(f"uitofp nneg i32 {ty}", [("i", 32)], f, f"%r = uitofp nneg i32 %a0 to {ty}"))
        # Alive2, at the pin, asserts that `uitofp` and `sitofp` have no fast-math flags, and stops, so it
        # isn't asked about those that do. LLVM's parser takes the flags before `nneg`. Each operation with
        # `nsz` has its operation without it.
        out.append(
            op(f"sitofp nnan i32 {ty}", [("i", 32)], f, f"%r = sitofp nnan i32 %a0 to {ty}", alive=False)
        )
        for name, flags in [
            ("uitofp", "nsz"),
            ("uitofp", "nsz nneg"),
            ("sitofp", "nsz"),
            ("sitofp", "nnan nsz"),
        ]:
            text = f"%r = {name} {flags} i32 %a0 to {ty}"
            out.append(nsz(op(f"{name} {flags} i32 {ty}", [("i", 32)], f, text, alive=False), "out"))
        out.append(
            op(f"uitofp ninf i128 {ty}", [("i", 128)], f, f"%r = uitofp ninf i128 %a0 to {ty}", alive=False)
        )
        out.append(op(f"sitofp i128 {ty}", [("i", 128)], f, f"%r = sitofp i128 %a0 to {ty}"))
        for w in [8, 32]:
            for name in ["fptoui", "fptosi"]:
                decl = f"declare i{w} @llvm.{name}.sat.i{w}.{sfx}({ty})"
                out.append(
                    op(
                        f"{name}.sat {ty} i{w}",
                        [f],
                        ("i", w),
                        f"%r = call i{w} @llvm.{name}.sat.i{w}.{sfx}({ty} %a0)",
                        [decl],
                    )
                )
    # Conversions between formats of different sizes, which choose a NaN.
    for a in FORMATS:
        for b in FORMATS:
            if fwidth(a) == fwidth(b):
                continue
            name = "fptrunc" if fwidth(a) > fwidth(b) else "fpext"
            for flags in ["", "nnan", "nsz"]:
                out.append(
                    nsz(
                        op(
                            f"{name} {flags} {a} {b}",
                            [("f", a)],
                            ("f", b),
                            f"%r = {name} {flags} {a} %a0 to {b}",
                            chooses=True,
                        ),
                        "in",
                    )
                )
    for o in out:
        o["body"] = re.sub(r" +", " ", o["body"])
        o["name"] = re.sub(r"\W+", "_", o["id"].replace("  ", " "))
        o["id"] = re.sub(r" +", " ", o["id"])
        if o["base"] is None:
            o["nsz"] = None
        else:
            o["base"] = re.sub(r" +", " ", o["base"])
    return out


def wrap(o):
    """The operation as a function of bits: its return type, parameters and body."""
    params, lines = [], []
    for k, t in enumerate(o["operands"]):
        if t[0] == "f":
            w = fwidth(t[1])
            params.append(f"i{w} %b{k}")
            lines.append(f"%a{k} = bitcast i{w} %b{k} to {t[1]}")
        else:
            params.append(f"i{t[1]} %a{k}")
    lines.append(o["body"])
    r = o["result"]
    if r[0] == "f":
        w = fwidth(r[1])
        lines += [f"%o = bitcast {r[1]} %r to i{w}", f"ret i{w} %o"]
        ret = f"i{w}"
    elif r[0] == "i":
        lines.append(f"ret i{r[1]} %r")
        ret = f"i{r[1]}"
    else:
        lines += ["%o = zext i1 %r to i8", "ret i8 %o"]
        ret = "i8"
    return ret, ", ".join(params), "\n  ".join(lines)


def bits(t):
    return fwidth(t[1]) if t[0] == "f" else t[1]


def fp_edges(ty):
    """Zeros, the smallest and largest subnormals, normals around one, the largest finite values,
    infinities, and quiet and signaling NaNs with payloads, of both signs."""
    e, m = FORMATS[ty]
    bias, top = (1 << (e - 1)) - 1, (1 << e) - 1
    pos = [
        0,
        1,
        2,
        (1 << m) - 1,
        1 << m,
        (1 << m) + 1,
        bias << m,
        (bias << m) + 1,
        ((bias - 1) << m) | ((1 << m) - 1),
        ((bias + 1) << m) | 1,
        ((top - 1) << m) | ((1 << m) - 1),
        (top - 1) << m,
        top << m,
        (top << m) | (1 << (m - 1)),
        (top << m) | 1,
        (top << m) | (1 << (m - 1)) | 1,
        (top << m) | ((1 << m) - 1),
    ]
    return sorted({v | s for v in pos for s in (0, 1 << (e + m))})


def int_edges(w):
    """Zero, one, the extremes, and integers around where rounding to each format starts."""
    mask = (1 << w) - 1
    vals = {0, 1, 2, 3, mask, mask - 1, 1 << (w - 1), (1 << (w - 1)) - 1, (1 << (w - 1)) + 1}
    for p in (8, 11, 24, 53, 113):
        for d in (-1, 0, 1, 3):
            vals.add(((1 << p) + d) & mask)
            vals.add(((1 << (p + 1)) - d) & mask)
    return sorted(vals)


def edges(t):
    return fp_edges(t[1]) if t[0] == "f" else int_edges(t[1])


def cases_for(o, rand):
    """Every operand of one operand of at most 16 bits, and otherwise edges against edges and random values.
    The list ends with poison operands, which only the model, the constant folder and Alive2 see."""
    ts = o["operands"]
    if len(ts) == 1:
        w = bits(ts[0])
        picked = (
            [[v] for v in range(1 << w)]
            if w <= 16
            else [[v] for v in edges(ts[0])] + [[rand.getrandbits(w)] for _ in range(300)]
        )
        return [*picked, [POISON]]
    es = [edges(t) for t in ts]
    picked = [[a, b] for a in es[0] for b in es[1]] + [
        [rand.getrandbits(bits(t)) for t in ts] for _ in range(400)
    ]
    return [*picked, [POISON, es[1][3]], [es[0][3], POISON]]


def sh(args, **kw):
    r = proc.run(args, **kw)
    if r.exit != 0:
        sys.exit(f"{args[0]} failed:\n{r.output[:3000]}")
    return r


def lean_env(work):
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([os.path.join(ROOT, ".lake", "build", "lib", "lean"), work])
    return env


def build(tool, work):
    rand = random.Random(11)
    table, decls, funcs = variants(), set(), []
    for o in table:
        o["ret"], o["params"], o["text"] = wrap(o)
        o["cases"] = cases_for(o, rand)
        decls.update(o["decls"])
        funcs.append(f"define {o['ret']} @{o['name']}({o['params']}) {{\n  {o['text']}\n}}\n")
    with open(os.path.join(work, "ops.ll"), "w") as f:
        f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(funcs))
    lean = os.path.join(work, "Ops.lean")
    r = proc.run([tool, os.path.join(work, "ops.ll"), "-o", lean, "--namespace", "Ops"])
    if r.exit != 0:
        sys.exit(f"emitter left functions out:\n{r.err}")
    return table, lean


def run_model(table, lean, work, jobs, tag):
    """The model's result for each (operation, choice, operands) in `jobs`. The cases are in a file the driver
    reads, named with a hash of them, so that a cached run is of these cases."""
    text = "".join(f"{i} {p} {' '.join(map(str, c))}\n" for i, p, c in jobs)
    digest = hashing.sha256_text(text)[:16]
    cases = os.path.join(work, f"cases_{tag}_{digest}.txt")
    with open(cases, "w") as f:
        f.write(text)
    src = [
        f"-- cases {digest}",
        "import Ops",
        "open IRLean",
        "def show' {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok (some v)) => toString v.toNat",
        '  | some (.ok none) => "poison"',
        '  | some (.error (.undefined _)) => "ub"',
        '  | some (.error (.model _)) => "stop"',
        '  | none => "diverged"',
        "-- A run that makes choices runs with every choice the given one: each operation has one chooser.",
        "class Run (α : Type) where run : α → Nat → String",
        "instance : Run (Outcome (Val w)) := ⟨fun o _ => show' o⟩",
        "instance : Run (Outcomes (Val w)) := ⟨fun o p => show' (o fun _ => p)⟩",
        "def lit (w : Nat) (s : String) : Val w :=",
        '  if s == "poison" then none else some (BitVec.ofNat w s.toNat!)',
    ]
    for i, o in enumerate(table):
        args = " ".join(f"(lit {bits(t)} c[{k}]!)" for k, t in enumerate(o["operands"]))
        src.append(f"def r{i} (c : Array String) (p : Nat) : String := Run.run (Ops.{o['name']} {args}) p")
    src.append(
        "def runners : Array (Array String → Nat → String) := #["
        + ", ".join(f"r{i}" for i in range(len(table)))
        + "]"
    )
    src.append(f"""def main : IO Unit := do
  let out ← IO.getStdout
  for line in ← IO.FS.lines "{cases}" do
    let w := (line.splitOn " ").toArray
    out.putStrLn (runners[w[0]!.toNat!]! (w.extract 2 w.size) w[1]!.toNat!)""")
    path = os.path.join(work, f"Drive_{tag}.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_ops():
        if not os.path.exists(os.path.join(work, "Ops.olean")):
            sh(["lean", "-R", work, "-o", os.path.join(work, "Ops.olean"), lean], env=env)

    out = lean_output(work, ["lean", *NATIVE, "--run", path], env, compile_ops).split()
    if len(out) != len(jobs):
        sys.exit("Lean printed the wrong number of results")
    return out


def judge(o, case, model, other):
    """`agree`, `refined` where the model is poison, or `wrong`. A NaN from the model, with its first choice,
    means IEEE 754 gives a NaN, and then any NaN LangRef allows is right."""
    if model == POISON:
        return "refined"
    if other == POISON:
        return "wrong"
    r = o["result"]
    if r[0] == "f" and is_nan(r[1], int(model)):
        ins = [(t[1], v) for t, v in zip(o["operands"], case, strict=True) if t[0] == "f"]
        return "agree" if int(other) in nan_set(r[1], ins) else "wrong"
    return "agree" if int(other) == int(model) else "wrong"


def check_choices(table, lean, work, results):
    """Each operation that chooses, where IEEE 754 gives a NaN, under every choice: each result has to be a
    NaN LangRef allows, and together they have to be all of them."""
    jobs = []
    for i, o in enumerate(table):
        if not o["chooses"]:
            continue
        for ci, c in enumerate(o["cases"]):
            model = results[o["name"]][ci]
            if model != POISON and is_nan(o["result"][1], int(model)):
                jobs += [(i, p, c) for p in PICKS]
    out = run_model(table, lean, work, jobs, "choices")
    checked, bad, seen = 0, [], {}
    for (i, p, c), got in zip(jobs, out, strict=True):
        o = table[i]
        key = (i, tuple(c))
        seen.setdefault(key, set()).add(got)
        if p == PICKS[-1]:
            ins = [(t[1], v) for t, v in zip(o["operands"], c, strict=True) if t[0] == "f"]
            allowed = {str(v) for v in nan_set(o["result"][1], ins)}
            checked += 1
            if seen[key] != allowed:
                bad.append((o["name"], c, sorted(seen[key] - allowed)[:4], sorted(allowed - seen[key])[:4]))
    return checked, bad


def has_zero(o, case):
    """Whether an operand is a zero, of either sign if it's a float."""
    return any(
        v != POISON and (is_zero(t[1], v) if t[0] == "f" else v == 0)
        for t, v in zip(o["operands"], case, strict=True)
    )


def check_nsz(table, lean, work, rand):
    """Each operation with `nsz` under every choice, on every case with a zero operand and a sample of the
    rest. Where `nsz` flips operands, its results have to be the operation's without it, under every choice
    of a NaN, on the operands with their zeros' signs flipped every way. Where it flips the result, they have
    to be the result without it, with either sign if that's a zero. Nothing else, and nothing missing."""
    index = {o["id"]: i for i, o in enumerate(table)}
    jobs, plan = [], []
    for i, o in enumerate(table):
        if not o["nsz"]:
            continue
        b = index[o["base"]]
        picks = PICKS if table[b]["chooses"] else [0]
        live = [c for c in o["cases"] if POISON not in c]
        zero = [c for c in live if has_zero(o, c)]
        rest = [c for c in live if not has_zero(o, c)]
        for c in zero + rand.sample(rest, min(50, len(rest))):
            flips = [list(c)]
            if o["nsz"] == "in":
                for k, (t, v) in enumerate(zip(o["operands"], c, strict=True)):
                    if t[0] == "f" and is_zero(t[1], v):
                        flips += [[*f[:k], f[k] ^ (1 << (fwidth(t[1]) - 1)), *f[k + 1 :]] for f in flips]
            want = [(b, p, f) for f in flips for p in picks]
            got = [(i, p, c) for p in NSZ_PICKS]
            plan.append((o, c, len(want), len(got), has_zero(o, c)))
            jobs += want + got
    out = run_model(table, lean, work, jobs, "nsz")
    checked, zeros, bad, pos = 0, 0, [], 0
    for o, c, nwant, ngot, zero in plan:
        want, got = set(out[pos : pos + nwant]), set(out[pos + nwant : pos + nwant + ngot])
        pos += nwant + ngot
        if o["nsz"] == "out":
            ty = o["result"][1]
            want |= {
                str(int(x) ^ (1 << (fwidth(ty) - 1))) for x in want if x != POISON and is_zero(ty, int(x))
            }
        checked += 1
        zeros += zero
        if want != got:
            bad.append((o["name"], c, sorted(got - want)[:4], sorted(want - got)[:4]))
    return checked, zeros, bad


def substituted(o, case):
    text = o["text"]
    for k, (t, v) in enumerate(zip(o["operands"], case, strict=True)):
        text = re.sub(rf"%{'b' if t[0] == 'f' else 'a'}{k}\b", str(v), text)
    return text


def fabs_nsz_negzero(o, case, fold):
    """Whether this is InstSimplify folding `fabs nsz -0.0` to `-0.0`, which it does where the constant
    folder doesn't fold `fabs`, as for `fp128`: `simplifyUnaryIntrinsic` returns the operand of `fabs nsz`
    that's never a NaN or below zero. That reads `nsz` as reaching the result's sign, where LangRef 23.1.3
    lets it flip only an operand's, and `fabs` of either zero is `0.0`. Alive2 agrees with LangRef, and
    tests/float has the case."""
    return o["id"].startswith("fabs nsz") and is_zero(o["operands"][0][1], case[0]) and fold == str(case[0])


def check_folder(table, results, work, rand):
    """The constant folder's result, on a sample of each operation's cases, judged as `judge` says. A fold to
    poison where the model has a value would make the model too defined. InstSimplify's `fabs nsz` of `-0.0`
    is counted apart, as `fabs_nsz_negzero` says."""
    src, decls, keys = [], set(), []
    for o in table:
        decls.update(o["decls"])
        cases = list(enumerate(o["cases"]))
        if len(cases) > 500:
            cases = [*sorted(rand.sample(cases[:-1], 500)), cases[-1]]
        for ci, c in cases:
            src.append(f"define {o['ret']} @{o['name']}__{ci}() {{\n  {substituted(o, c)}\n}}\n")
            keys.append((o, ci))
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(src))
    folded = sh(["opt", "-passes=instsimplify", "-S", path]).out
    found = {}
    for m in re.finditer(r"define i(\d+) @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", folded):
        width, fn, body = int(m.group(1)), m.group(2), m.group(3)
        lines = [line for line in body.splitlines() if line.strip()]
        r = re.fullmatch(r"\s*ret i\d+ (poison|-?\d+)", lines[-1]) if len(lines) == 1 else None
        if r:
            found[fn] = r.group(1) if r.group(1) == POISON else str(int(r.group(1)) & ((1 << width) - 1))
    counts, bad = {"agree": 0, "refined": 0, "unfolded": 0, "wrong": 0, "fabs nsz": 0}, []
    for o, ci in keys:
        fold = found.get(f"{o['name']}__{ci}")
        if fold is None:
            counts["unfolded"] += 1
            continue
        verdict = judge(o, o["cases"][ci], results[o["name"]][ci], fold)
        if verdict == "wrong" and fabs_nsz_negzero(o, o["cases"][ci], fold):
            verdict = "fabs nsz"
        counts[verdict] += 1
        if verdict == "wrong":
            bad.append((o["name"], o["cases"][ci], results[o["name"]][ci], fold))
    return counts, bad


C_DRIVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static u128 parse(const char *s) {
  u128 v = 0;
  while (*s >= '0' && *s <= '9') v = v * 10 + (u128)(*s++ - '0');
  return v;
}
static void print(u128 v) {
  char buf[64]; int n = 0;
  do { buf[n++] = (char)('0' + (int)(v % 10)); v /= 10; } while (v);
  while (n) putchar(buf[--n]);
  putchar('\n');
}
%DECLS%
int main(void) {
  char line[256];
%CALLS%
  return 0;
}
"""
CTYPE = {8: "uint8_t", 16: "uint16_t", 32: "uint32_t", 64: "uint64_t", 128: "u128"}


def x86_quiets(o, case):
    """Whether x86-64's backend, at the pin, gets this case wrong: it passes a `bfloat` through `float` and
    back, with `__truncsfbf2`, before `llvm.is.fpclass` classifies it, which quiets a signaling NaN. LangRef
    says the intrinsic "does not canonicalize its input value", and the constant folder and Alive2 agree with
    the model. AArch64 classifies the bits as they are."""
    if platform.machine() not in ("x86_64", "AMD64") or o["operands"] != [("f", "bfloat")]:
        return False
    m = FORMATS["bfloat"][1]
    return o["id"].startswith("is.fpclass") and is_nan("bfloat", case[0]) and not case[0] >> (m - 1) & 1


def check_native(table, results, work):
    """The processor's result on every case whose operands aren't poison, judged as `judge` says. Operations
    with an `fp128` or an `i128` in them are built apart, and only they may be skipped, on a host whose linker
    can't find a library for their arithmetic, and that's said."""
    counts, bad, skipped = {"agree": 0, "refined": 0, "wrong": 0, "quieted": 0}, [], []
    groups = {"fp128 and i128": [], "rest": []}
    for o in table:
        types = [*o["operands"], o["result"]]
        groups["fp128 and i128" if ("f", "fp128") in types or ("i", 128) in types else "rest"].append(o)
    for group, ops in groups.items():
        decls, calls, lines = [], [], []
        for o in ops:
            ret = "uint8_t" if o["ret"] == "i8" and o["result"][0] == "b" else CTYPE[int(o["ret"][1:])]
            decls.append(f"{ret} {o['name']}({', '.join(CTYPE[bits(t)] for t in o['operands'])});")
            live = [c for c in o["cases"] if POISON not in c]
            lines += live
            # Read in order into locals: C doesn't say in which order a call's arguments are evaluated.
            reads = " ".join(
                f'u128 a{k} = parse(strtok({"line" if k == 0 else "NULL"}, " "));'
                for k in range(len(o["operands"]))
            )
            args = ", ".join(f"({CTYPE[bits(t)]})a{k}" for k, t in enumerate(o["operands"]))
            calls.append(
                f"  for (int i = 0; i < {len(live)}; i++) {{ if (!fgets(line, sizeof line, stdin)) "
                f"return 1; {reads} print((u128){o['name']}({args})); }}"
            )
        d = os.path.join(work, f"native_{group.split()[0]}")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "main.c"), "w") as f:
            f.write(C_DRIVER.replace("%DECLS%", "\n".join(decls)).replace("%CALLS%", "\n".join(calls)))
        with open(os.path.join(d, "ops.ll"), "w") as f:
            f.write(
                "\n".join(sorted({x for o in ops for x in o["decls"]}))
                + "\n\n"
                + "\n".join(
                    f"define {o['ret']} @{o['name']}({o['params']}) {{\n  {o['text']}\n}}\n" for o in ops
                )
            )
        # The rest has to build everywhere, which shows the driver does. `fp128` and `i128` need library calls
        # a backend may not have, as AArch64's has none for `uitofp i128` to `bfloat`, or a host may not link.
        r = None
        failed_step = -1
        for step, argv in enumerate(
            (
                ["clang", "-O0", "-w", "-c", "-o", os.path.join(d, "main.c.o"), os.path.join(d, "main.c")],
                ["clang", "-O0", "-w", "-c", "-o", os.path.join(d, "ops.ll.o"), os.path.join(d, "ops.ll")],
                [
                    "clang",
                    "-o",
                    os.path.join(d, "run"),
                    os.path.join(d, "main.c.o"),
                    os.path.join(d, "ops.ll.o"),
                    "-lm",
                ],
            )
        ):
            r = proc.run(argv)
            if r.exit != 0:
                failed_step = step
                break
        assert r is not None  # the loop above always runs at least once
        if r.exit != 0:
            # Only the link step (2) failing on its own with a missing-library error is the "this host can't
            # build it" case this group allows. A compile error (step 0 or 1), a signal death (exit < 0), a
            # crash exit code (>= 128), or a resource limit is a real failure that mustn't silently drop every
            # fp128/i128 case from the oracle, even if its partial output mentions "undefined".
            link_missing_lib = (
                failed_step == 2 and r.limit is None and 0 < r.exit < 128 and "undefined" in r.output.lower()
            )
            if group == "rest" or not link_missing_lib:
                sys.exit(f"building the processor's check failed:\n{r.output[:2000]}")
            found = [
                line
                for line in r.output.splitlines()
                if "error" in line.lower() or "undefined" in line.lower()
            ]
            skipped.append((group, (found or ["?"])[0].strip()[:200]))
            continue
        out = sh(
            [os.path.join(d, "run")], stdin="".join(" ".join(map(str, c)) + "\n" for c in lines)
        ).out.split()
        pos = 0
        for o in ops:
            for ci, c in enumerate(o["cases"]):
                if POISON in c:
                    continue
                verdict = "quieted" if x86_quiets(o, c) else judge(o, c, results[o["name"]][ci], out[pos])
                pos += 1
                counts[verdict] += 1
                if verdict == "wrong":
                    bad.append((o["name"], c, results[o["name"]][ci], out[pos - 1]))
    return counts, bad, skipped


def check_alive(table, results, work, rand):
    """A sample of cases: the operation on constants against a function returning the model's result. Where
    that's a NaN, or the operation has `nsz`, only the model's result refining the operation is asked, since
    the operation may give others. Alive2 drops `nofpclass` from an intrinsic's argument, so it's asked about
    `nofpclass` on a return instead, which `FP.nofpclass` is too. It can't check flags it approximates, and
    stops at fast-math flags on `uitofp` and `sitofp`, which are counted."""
    pairs, names, decls, unread = [], [], set(), 0
    for o in table:
        if not o["alive"]:
            unread += 1
            continue
        cases = list(enumerate(o["cases"]))
        sample = [*rand.sample(cases[:-1], min(6, len(cases) - 1)), cases[-1]]
        # Under `nsz`, two of the cases where a zero's sign may flip.
        if o["nsz"]:
            zero = [x for x in cases[:-1] if has_zero(o, x[1])]
            sample[:0] = rand.sample(zero, min(2, len(zero)))
        for ci, c in sample:
            model = results[o["name"]][ci]
            if o["id"].startswith("nofpclass"):
                ty, w, k = o["result"][1], fwidth(o["result"][1]), o["id"].split()[1]
                value = (
                    f"%t = bitcast i{w} {model} to {ty}\n  ret {ty} %t"
                    if model != POISON
                    else f"ret {ty} poison"
                )
                src = (
                    f"define nofpclass({k}) {ty} @F() {{\n"
                    f"  %a = bitcast i{w} {c[0]} to {ty}\n  ret {ty} %a\n}}\n"
                )
                tgt = f"define {ty} @F() {{\n  {value}\n}}\n"
            else:
                src = f"define {o['ret']} @F() {{\n  {substituted(o, c)}\n}}\n"
                tgt = f"define {o['ret']} @F() {{\n  ret {o['ret']} {model}\n}}\n"
            nan = model != POISON and o["result"][0] == "f" and is_nan(o["result"][1], int(model))
            # Under `nsz` the operation may give either zero, so the model's is asked only one way too.
            one_way = nan or o["nsz"] is not None
            pairs.append((src, tgt))
            if not one_way:
                pairs.append((tgt, src))
            names.append((o["name"], c, 1 if one_way else 2))
            decls.update(o["decls"])
    outputs = alive.refinements("\n".join(sorted(decls)) + "\n", pairs, work)
    proved, failed, skipped, pos = 0, [], [], 0
    for name, c, n in names:
        got = outputs[pos : pos + n]
        pos += n
        verdicts = [alive.verdict(x) for x in got]
        if "incorrect" in verdicts:
            failed.append(((name, c), next(x for x in got if x)))
        elif "unknown" in verdicts:
            skipped.append(((name, c), next(x for x in got if x)))
        else:
            proved += 1
    return proved, failed, skipped, unread


def main():
    tool = os.path.abspath(sys.argv[1])
    use_alive = "--no-alive" not in sys.argv
    use_native = "--no-native" not in sys.argv
    if use_alive and not shutil.which("alive-tv"):
        sys.exit("FAIL  alive2: alive-tv is not on PATH. Pass --no-alive to run without it")
    work = tempfile.mkdtemp(prefix="fpcheck-")
    try:
        rand = random.Random(5)
        table, lean = build(tool, work)
        jobs = [(i, 0, c) for i, o in enumerate(table) for c in o["cases"]]
        out, results, pos = run_model(table, lean, work, jobs, "all"), {}, 0
        for o in table:
            results[o["name"]] = out[pos : pos + len(o["cases"])]
            pos += len(o["cases"])
        print(f"{len(table)} operation variants, {len(jobs)} cases on the model")
        failed = False
        checked, cbad = check_choices(table, lean, work, results)
        print(
            f"choices: {checked} cases where IEEE 754 gives a NaN, each run under {len(PICKS)} choices, "
            f"{len(cbad)} that give a NaN LangRef doesn't allow or miss one it does"
        )
        for b in cbad[:10]:
            print("  WRONG", b)
        failed |= bool(cbad) or not checked
        checked, zeros, zbad = check_nsz(table, lean, work, rand)
        print(
            f"nsz: {checked} cases, {zeros} of them with a zero, each run under {len(NSZ_PICKS)} choices, "
            f"{len(zbad)} that give a result flipping zeros' signs doesn't or miss one it does"
        )
        for b in zbad[:10]:
            print("  WRONG", b)
        failed |= bool(zbad) or not zeros
        counts, bad = check_folder(table, results, work, rand)
        print(
            f"constant folder: {counts['agree']} agree, {counts['refined']} where the model is poison, "
            f"{counts['unfolded']} not folded, {counts['wrong']} wrong"
        )
        for b in bad[:20]:
            print("  WRONG", b)
        if counts["fabs nsz"]:
            print(
                f"  constant folder: {counts['fabs nsz']} folds of fabs nsz -0.0 to -0.0, which LangRef's "
                "nsz doesn't allow and Alive2 refutes, not counted"
            )
        failed |= bool(bad) or not counts["agree"]
        if use_native:
            counts, nbad, skipped = check_native(table, results, work)
            print(
                f"processor: {counts['agree']} agree, {counts['refined']} where the model is poison, "
                f"{counts['wrong']} wrong"
            )
            if counts["quieted"]:
                print(
                    f"  processor: {counts['quieted']} signaling NaNs in bfloat not compared for "
                    "llvm.is.fpclass, which x86-64's backend quiets before classifying them"
                )
            for group, why in skipped:
                print(f"  processor: skipped {group}, which this host can't build: {why}")
            for b in nbad[:20]:
                print("  WRONG", b)
            failed |= bool(nbad) or not counts["agree"]
        else:
            print("processor: skipped by --no-native")
        if use_alive:
            proved, afail, askipped, unread = check_alive(table, results, work, rand)
            print(
                f"alive2: {proved} cases proved, {len(afail)} wrong, {len(askipped)} it couldn't check, and "
                f"{unread} variants not asked, with flags it approximates or that crash it"
            )
            for name, text in afail[:10]:
                print("  WRONG", name, "\n", text[:600])
            for name, text in askipped[:5]:
                print("  skipped", name, (text or "").strip().splitlines()[-1:] if text else "")
            failed |= bool(afail) or bool(askipped) or not proved
        else:
            print("alive2: skipped by --no-alive")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
