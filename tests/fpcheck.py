#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks every floating-point operation in IRLean/Float.lean, through the emitter, against LLVM, as
tests/opcheck.py does for integers. docs/float.md has the design.

Each operation is an IR function that takes and returns bits: its operands are integers, bitcast to the
format, and its result is bitcast back, or zero-extended to `i8` if it's an `i1`. The same function goes to
four places:

  - the model, through the emitter, run natively on every case;
  - LLVM's constant folder, `opt -passes=instsimplify`, with the operands as constants, poison among them;
  - the processor, through clang, for operands that aren't poison;
  - Alive2, for a sample: the function on constant operands against a function returning the model's
    result, both ways.

Every result is exact, since no operation here makes a choice: `fneg`, `fabs` and `copysign` keep a NaN's
payload, as LangRef says, and `fcmp` and `llvm.is.fpclass` give a bit. At `half`, every operand of the
operations of one operand is tried on the model and the processor, and the operations of two have every edge
value against every other, and random pairs.

usage: tests/fpcheck.py path/to/ir-lean [--no-alive] [--no-native]

Without `alive-tv` on PATH this fails, unless `--no-alive` says that's fine. Only `fp128` may be skipped on
the processor, where the host has no library for its arithmetic, and that's said. `--no-native` skips the
processor.
"""

import os
import random
import re
import shutil
import sys
import tempfile

import alive
from differential import NATIVE, lean_output

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
from irlean import proc  # noqa: E402

# Name, IR type, exponent bits, significand bits.
FORMATS = [
    ("half", "half", 5, 10),
    ("bfloat", "bfloat", 8, 7),
    ("float", "float", 8, 23),
    ("double", "double", 11, 52),
    ("fp128", "fp128", 15, 112),
]
FCMP = "false oeq ogt oge olt ole one ord ueq ugt uge ult ule une uno true".split()
# `llvm.is.fpclass` and `nofpclass` masks: each class alone, and some unions LLVM's tests use.
MASKS = [1 << k for k in range(10)] + [0x3, 0x3FC, 0x204, 0x090, 0x060, 0x3FF, 0]
POISON = "poison"


def variants(fmt):
    """Yields (id, operand count, result kind, body, declarations). `%a0`, `%a1` are the operands, as
    floats."""
    name, ty, _, _ = fmt
    out = []
    for flags in ["", "nnan", "ninf", "nnan ninf"]:
        out.append((f"fneg {flags}".strip(), 1, "fp", f"%r = fneg {flags} {ty} %a0".replace("  ", " "), []))
    suffix = {"half": "f16", "bfloat": "bf16", "float": "f32", "double": "f64", "fp128": "f128"}[name]
    fabs = f"declare {ty} @llvm.fabs.{suffix}({ty})"
    copysign = f"declare {ty} @llvm.copysign.{suffix}({ty}, {ty})"
    for flags in ["", "nnan", "ninf"]:
        out.append(
            (
                f"fabs {flags}".strip(),
                1,
                "fp",
                f"%r = call {flags} {ty} @llvm.fabs.{suffix}({ty} %a0)".replace("  ", " "),
                [fabs],
            )
        )
        out.append(
            (
                f"copysign {flags}".strip(),
                2,
                "fp",
                f"%r = call {flags} {ty} @llvm.copysign.{suffix}({ty} %a0, {ty} %a1)".replace("  ", " "),
                [copysign],
            )
        )
    for p in FCMP:
        out.append((f"fcmp {p}", 2, "i1", f"%r = fcmp {p} {ty} %a0, %a1", []))
    # LangRef says only `nnan`, `ninf` and `reassoc` mean anything on `fcmp`, so the others are allowed and
    # change nothing. Alive2 approximates `arcp`, `contract` and `afn` wherever they are, so it can't check
    # those.
    for flags in ["nnan", "ninf", "nsz", "arcp contract afn"]:
        out.append((f"fcmp {flags} olt", 2, "i1", f"%r = fcmp {flags} olt {ty} %a0, %a1", []))
        out.append((f"fcmp {flags} ueq", 2, "i1", f"%r = fcmp {flags} ueq {ty} %a0, %a1", []))
    fpclass = f"declare i1 @llvm.is.fpclass.{suffix}({ty}, i32)"
    for k in MASKS:
        out.append(
            (
                f"is.fpclass {k}",
                1,
                "i1",
                f"%r = call i1 @llvm.is.fpclass.{suffix}({ty} %a0, i32 {k})",
                [fpclass],
            )
        )
    out.append(("select", 2, "fp", f"%r = select i1 true, {ty} %a1, {ty} %a0", []))
    # `nofpclass` on a call's argument, to `copysign` of the operand and itself, which is the operand.
    for k in [*MASKS[:10], 0x3, 0x3FC]:
        out.append(
            (
                f"nofpclass {k}",
                1,
                "fp",
                f"%r = call {ty} @llvm.copysign.{suffix}({ty} nofpclass({k}) %a0, {ty} %a0)",
                [copysign],
            )
        )
    return out


def width(fmt):
    return 1 + fmt[2] + fmt[3]


def fn_name(ident, fmt):
    return re.sub(r"\W+", "_", f"{ident}_{fmt[0]}")


def wrap(fmt, arity, kind, body):
    """The operation as a function of bits."""
    w, ty = width(fmt), fmt[1]
    params = ", ".join(f"i{w} %b{i}" for i in range(arity))
    lines = [f"%a{i} = bitcast i{w} %b{i} to {ty}" for i in range(arity)] + [body]
    if kind == "fp":
        lines += [f"%o = bitcast {ty} %r to i{w}", f"ret i{w} %o"]
        ret = f"i{w}"
    else:
        lines += ["%o = zext i1 %r to i8", "ret i8 %o"]
        ret = "i8"
    return ret, params, "\n  ".join(lines)


def edges(fmt):
    """Zeros, the smallest and largest subnormals, normals around one, the largest finite values,
    infinities, and quiet and signaling NaNs with payloads, of both signs."""
    _, _, e, m = fmt
    w = 1 + e + m
    bias = (1 << (e - 1)) - 1
    top = (1 << e) - 1
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
        ((top - 1) << m) | ((1 << m) - 1),
        (top - 1) << m,
        top << m,
        (top << m) | (1 << (m - 1)),
        (top << m) | 1,
        (top << m) | (1 << (m - 1)) | 1,
        (top << m) | ((1 << m) - 1),
    ]
    return sorted({v | s for v in pos for s in (0, 1 << (w - 1))})


def cases_for(fmt, arity, rand, exhaustive):
    """Every operand of one operand at `half` when `exhaustive`, and otherwise edges and random values. Each
    list ends with some poison operands, which only the model, the constant folder and Alive2 see."""
    w = width(fmt)
    es = edges(fmt)
    if arity == 1:
        picked = (
            [[v] for v in range(1 << w)]
            if exhaustive
            else [[v] for v in es] + [[rand.getrandbits(w)] for _ in range(200)]
        )
        return [*picked, [POISON]]
    picked = [[a, b] for a in es for b in es] + [
        [rand.getrandbits(w), rand.getrandbits(w)] for _ in range(300)
    ]
    return [*picked, [POISON, es[3]], [es[3], POISON]]


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
    table, decls, funcs = [], set(), []
    for fmt in FORMATS:
        for ident, arity, kind, body, ds in variants(fmt):
            name = fn_name(ident, fmt)
            ret, params, text = wrap(fmt, arity, kind, body)
            decls.update(ds)
            funcs.append(f"define {ret} @{name}({params}) {{\n  {text}\n}}\n")
            cases = cases_for(fmt, arity, rand, exhaustive=fmt[0] == "half" and arity == 1)
            table.append(
                {
                    "name": name,
                    "id": ident,
                    "fmt": fmt,
                    "arity": arity,
                    "kind": kind,
                    "ret": ret,
                    "params": params,
                    "text": text,
                    "decls": ds,
                    "cases": cases,
                }
            )
    module = "\n".join(sorted(decls)) + "\n\n" + "\n".join(funcs)
    with open(os.path.join(work, "ops.ll"), "w") as f:
        f.write(module)
    lean = os.path.join(work, "Ops.lean")
    r = proc.run([tool, os.path.join(work, "ops.ll"), "-o", lean, "--namespace", "Ops"])
    if r.exit != 0:
        sys.exit(f"emitter left functions out:\n{r.err}")
    return table, module, lean


def eval_in_lean(table, lean, work):
    """Every case of every operation, on the model. Cases are in a file the driver reads, since there are
    many."""
    with open(os.path.join(work, "cases.txt"), "w") as f:
        for op in table:
            for c in op["cases"]:
                f.write(" ".join(str(v) for v in c) + "\n")
    src = [
        "import Ops",
        "open IRLean",
        "def show' {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok (some v)) => toString v.toNat",
        '  | some (.ok none) => "poison"',
        '  | some (.error (.undefined _)) => "ub"',
        '  | some (.error (.model _)) => "stop"',
        '  | none => "diverged"',
        "def lit (w : Nat) (s : String) : Val w :=",
        '  if s == "poison" then none else some (BitVec.ofNat w s.toNat!)',
    ]
    runners = []
    for i, op in enumerate(table):
        w = width(op["fmt"])
        args = " ".join(f"(lit {w} c[{k}]!)" for k in range(op["arity"]))
        src.append(f"def r{i} (c : Array String) : String := show' (Ops.{op['name']} {args})")
        runners.append((f"r{i}", len(op["cases"])))
    src.append(
        "def runners : Array ((Array String → String) × Nat) := #["
        + ", ".join(f"({r}, {n})" for r, n in runners)
        + "]"
    )
    src.append(f"""def main : IO Unit := do
  let lines ← IO.FS.lines "{os.path.join(work, "cases.txt")}"
  let out ← IO.getStdout
  let mut pos := 0
  for (r, n) in runners do
    for k in [0:n] do
      out.putStrLn (r (lines[pos + k]!.splitOn " ").toArray)
    pos := pos + n""")
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_ops():
        sh(["lean", "-R", work, "-o", os.path.join(work, "Ops.olean"), lean], env=env)

    out = lean_output(work, ["lean", *NATIVE, "--run", path], env, compile_ops).split()
    results, pos = {}, 0
    for op in table:
        n = len(op["cases"])
        results[op["name"]] = out[pos : pos + n]
        pos += n
    if pos != len(out):
        sys.exit("Lean printed the wrong number of results")
    return results


def substituted(op, case):
    text = op["text"]
    for k, v in enumerate(case):
        text = text.replace(f"%b{k}", str(v))
    return text


def check_folder(table, results, work, rand):
    """The model's value has to be the fold's. Where the model gives poison, any fold refines it. A fold to
    poison where the model has a value would make the model too defined. A sample of each operation's
    cases."""
    src, decls, keys = [], set(), []
    for op in table:
        decls.update(op["decls"])
        cases = list(enumerate(op["cases"]))
        if len(cases) > 600:
            cases = [*sorted(rand.sample(cases[:-1], 600)), cases[-1]]
        for ci, c in cases:
            src.append(f"define {op['ret']} @{op['name']}__{ci}() {{\n  {substituted(op, c)}\n}}\n")
            keys.append((op["name"], ci))
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(src))
    folded = sh(["opt", "-passes=instsimplify", "-S", path]).out
    found = {}
    for m in re.finditer(r"define i(\d+) @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", folded):
        bits, fn, body = int(m.group(1)), m.group(2), m.group(3)
        lines = [line for line in body.splitlines() if line.strip()]
        r = re.fullmatch(r"\s*ret i\d+ (poison|-?\d+)", lines[-1]) if len(lines) == 1 else None
        if r:
            found[fn] = r.group(1) if r.group(1) == POISON else str(int(r.group(1)) & ((1 << bits) - 1))
    agreed = refined = unfolded = 0
    bad = []
    for name, ci in keys:
        model = results[name][ci]
        fold = found.get(f"{name}__{ci}")
        if fold is None:
            unfolded += 1
        elif model == POISON:
            refined += 1
        elif fold != model:
            bad.append((name, ci, model, fold))
        else:
            agreed += 1
    return agreed, refined, unfolded, bad


C_DRIVER = r"""
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
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


def check_native(table, results, work):
    """The model's value has to be the processor's, on every case whose operands aren't poison, unless the
    model's is poison, which the processor can't show. A format the processor can't run, which clang or the
    linker refuses, is skipped and said so."""
    ctype = {16: "uint16_t", 32: "uint32_t", 64: "uint64_t", 128: "u128"}
    agreed, poison, bad, skipped = 0, 0, [], []
    for fmt in FORMATS:
        ops = [op for op in table if op["fmt"] == fmt]
        decls, calls, cases = [], [], []
        for op in ops:
            w = width(fmt)
            ret = "uint8_t" if op["ret"] == "i8" else ctype[w]
            args = ", ".join(ctype[w] for _ in range(op["arity"]))
            decls.append(f"{ret} {op['name']}({args});")
            live = [c for c in op["cases"] if POISON not in c]
            cases += live
            # Read in order into locals: C doesn't say in which order a call's arguments are evaluated.
            reads = " ".join(
                f'u128 a{k} = parse(strtok({"line" if k == 0 else "NULL"}, " "));' for k in range(op["arity"])
            )
            call_args = ", ".join(f"({ctype[w]})a{k}" for k in range(op["arity"]))
            calls.append(
                f"  for (int i = 0; i < {len(live)}; i++) {{ if (!fgets(line, sizeof line, stdin)) return 1;"
                f" {reads} print((u128){op['name']}({call_args})); }}"
            )
        source = C_DRIVER.replace("%DECLS%", "\n".join(decls)).replace("%CALLS%", "\n".join(calls))
        d = os.path.join(work, f"native_{fmt[0]}")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "main.c"), "w") as f:
            f.write(source)
        module = (
            "\n".join(sorted({x for op in ops for x in op["decls"]}))
            + "\n\n"
            + "\n".join(
                f"define {op['ret']} @{op['name']}({op['params']}) {{\n  {op['text']}\n}}\n" for op in ops
            )
        )
        with open(os.path.join(d, "ops.ll"), "w") as f:
            f.write(module)
        # The driver and the functions have to compile, everywhere. Only linking `fp128` may fail, on a host
        # without a library for its arithmetic, and that's said.
        for src in ("main.c", "ops.ll"):
            sh(["clang", "-O0", "-w", "-c", "-o", os.path.join(d, src + ".o"), os.path.join(d, src)])
        r = proc.run(
            ["clang", "-o", os.path.join(d, "run"), os.path.join(d, "main.c.o"), os.path.join(d, "ops.ll.o")]
        )
        if r.exit != 0:
            if fmt[0] != "fp128":
                sys.exit(f"linking the {fmt[0]} check failed:\n{r.output[:2000]}")
            errors = [line for line in r.output.splitlines() if "undefined" in line.lower()] or ["?"]
            skipped.append((fmt[0], errors[0].strip()[:200]))
            continue
        out = sh(
            [os.path.join(d, "run")], stdin="".join(" ".join(map(str, c)) + "\n" for c in cases)
        ).out.split()
        pos = 0
        for op in ops:
            for ci, c in enumerate(op["cases"]):
                if POISON in c:
                    continue
                model, got = results[op["name"]][ci], out[pos]
                pos += 1
                if model == POISON:
                    poison += 1
                elif model == got:
                    agreed += 1
                else:
                    bad.append((op["name"], c, model, got))
    return agreed, poison, bad, skipped


def check_alive(table, results, work, rand):
    """A sample of cases: the operation on constants, against returning the model's result, in both
    directions. Alive2 drops `nofpclass` from an intrinsic's argument, so it's asked about `nofpclass` on a
    return instead, which `FP.nofpclass` is too. It can't check flags it approximates, which are counted."""
    pairs, names, decls, unread = [], [], set(), 0
    for op in table:
        if "arcp" in op["id"]:
            unread += 1
            continue
        cases = list(enumerate(op["cases"]))
        sample = [*rand.sample(cases[:-1], min(6, len(cases) - 1)), cases[-1]]
        for ci, c in sample:
            model = results[op["name"]][ci]
            if op["id"].startswith("nofpclass"):
                ty, w, k = op["fmt"][1], width(op["fmt"]), op["id"].split()[1]
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
                src = f"define {op['ret']} @F() {{\n  {substituted(op, c)}\n}}\n"
                tgt = f"define {op['ret']} @F() {{\n  ret {op['ret']} {model}\n}}\n"
            pairs += [(src, tgt), (tgt, src)]
            names.append((op["name"], c))
            decls.update(op["decls"])
    outputs = alive.refinements("\n".join(sorted(decls)) + "\n", pairs, work)
    proved, failed, skipped = 0, [], []
    for k, name in enumerate(names):
        verdicts = [alive.verdict(outputs[2 * k]), alive.verdict(outputs[2 * k + 1])]
        if "incorrect" in verdicts:
            failed.append((name, outputs[2 * k] or outputs[2 * k + 1]))
        elif "unknown" in verdicts:
            skipped.append((name, outputs[2 * k] or outputs[2 * k + 1]))
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
        table, _, lean = build(tool, work)
        results = eval_in_lean(table, lean, work)
        print(f"{len(table)} operation variants, {sum(len(op['cases']) for op in table)} cases on the model")
        agreed, refined, unfolded, bad = check_folder(table, results, work, rand)
        print(
            f"constant folder: {agreed} agree, {refined} where the model is poison, {unfolded} not folded, "
            f"{len(bad)} wrong"
        )
        for b in bad[:20]:
            print("  WRONG", b)
        failed = bool(bad) or not agreed
        if use_native:
            agreed, poison, nbad, skipped = check_native(table, results, work)
            print(f"processor: {agreed} agree, {poison} where the model is poison, {len(nbad)} wrong")
            for fmt, why in skipped:
                print(f"  processor: skipped {fmt}, which this host can't build: {why}")
            for b in nbad[:20]:
                print("  WRONG", b)
            failed = failed or bool(nbad) or not agreed
        else:
            print("processor: skipped by --no-native")
        if use_alive:
            proved, afail, askipped, unread = check_alive(table, results, work, rand)
            print(
                f"alive2: {proved} cases proved in both directions, {len(afail)} wrong, {len(askipped)} it "
                f"couldn't check, and {unread} variants with flags it approximates not asked"
            )
            for name, out in afail[:10]:
                print("  WRONG", name, "\n", out[:600])
            for name, out in askipped[:5]:
                print("  skipped", name, (out or "").strip().splitlines()[-1:] if out else "")
            failed = failed or bool(afail) or bool(askipped) or not proved
        else:
            print("alive2: skipped by --no-alive")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
