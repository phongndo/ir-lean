#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks every x86 intrinsic the model has against the processor, through the emitter, at every form: each
width, and each immediate tests/x86ops.py lists.

One file of inputs feeds both sides: random lanes, lanes at the extremes, and every operand a splat of an
extreme, each against each. Lean runs the emitted function on each, and native code runs the same call, in a
function compiled without optimization, so the instruction itself computes it. Every lane has to agree.

It can fail, and it has to: tests/x86/Wrong.lean has a wrong version of each definition, and for each
intrinsic the processor has to disagree with it on some input, or the inputs couldn't tell them apart. And
every x86 intrinsic the classification calls modeled has to be one of the operations here.

The processor can't show poison, which tests/x86check.py and tests/vecopcheck.py check. Skipped, with exit
code 77, on a processor without an instruction set an operation needs.

usage: tests/x86native.py path/to/ir-lean
"""

import json
import os
import random
import shutil
import sys
import tempfile

import x86ops
from differential import NATIVE, lean_output
from opcheck import lean_env, sh

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(ROOT, "tools"))
from irlean import hashing, proc  # noqa: E402

TRIPLE = "x86_64-unknown-linux-gnu"
# Without optimization, so each call is the instruction, and nothing folds it.
ATTRIBUTES = 'noinline optnone "target-features"="' + ",".join(f"+{f}" for f in x86ops.FEATURES) + '"'
DRIVER = """
#include <stdio.h>
#include <stdlib.h>
struct op { void (*run)(const unsigned char *, unsigned char *); int in, out, cases; };
extern const struct op ops[];
extern const int count;
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  if (argc != 2 || !f) return 2;
  static unsigned char in[1024], out[64];
  for (int k = 0; k < count; k++)
    for (int c = 0; c < ops[k].cases; c++) {
      if (fread(in, 1, ops[k].in, f) != (size_t)ops[k].in) return 2;
      ops[k].run(in, out);
      for (int i = 0; i < ops[k].out; i++) printf("%02x", out[i]);
      putchar('\\n');
    }
  return 0;
}
"""


def size(shape):
    return max(shape[0], 1) * shape[1] // 8


def encode(op, case):
    """A case's operands as the bytes they have in memory, lanes lowest first."""
    return b"".join(
        x.to_bytes(w // 8, "little") for (_, w), lanes in zip(op.args, case, strict=True) for x in lanes
    )


def lean_results(tool, ops, counts, inputs, work):
    """What the model gives for each case, and what the wrong versions give: for each operation, a list of
    (lanes, wrong lanes), each a list of numbers, or what Lean printed if it isn't one."""
    ll = os.path.join(work, "ops.ll")
    with open(ll, "w") as f:
        f.write("\n".join(sorted({op.declaration for op in ops})) + "\n\n")
        f.write("\n".join(op.definition for op in ops))
    r = proc.run([tool, ll, "-o", os.path.join(work, "Ops.lean"), "--namespace", "Ops"])
    if r.exit != 0:
        sys.exit(f"the emitter left operations out:\n{r.err}")
    with open(os.path.join(work, "Ops.lean")) as f:
        emitted = f.read()
    with open(os.path.join(work, "OpsWrong.lean"), "w") as f:
        f.write(x86ops.wrong_module(emitted))
    shutil.copyfile(x86ops.WRONG, os.path.join(work, "X86Wrong.lean"))
    src = [
        # The inputs aren't a .lean file, and what Lean printed is kept by the .lean files it read.
        f"-- inputs {hashing.sha256_file(inputs)}",
        "import Ops",
        "import OpsWrong",
        "open IRLean",
        "def le (b : ByteArray) (o n : Nat) : Nat :=",
        "  (List.range n).foldr (fun i acc => acc * 256 + (b.get! (o + i)).toNat) 0",
        "def lanes (b : ByteArray) (o n w : Nat) : Vec n w :=",
        "  Vector.ofFn fun i => some (BitVec.ofNat w (le b (o + i.val * (w / 8)) (w / 8)))",
        "def val (b : ByteArray) (o w : Nat) : Val w := some (BitVec.ofNat w (le b o (w / 8)))",
        "def showVal {w : Nat} : Val w → String",
        "  | some v => toString v.toNat",
        '  | none => "poison"',
        "class Shows (α : Type) where shows : α → String",
        "instance : Shows (Outcome (Val w)) where",
        "  shows",
        "    | some (.ok v) => showVal v",
        '    | _ => "stopped"',
        "instance : Shows (Outcome (Vec n w)) where",
        "  shows",
        '    | some (.ok v) => " ".intercalate (v.toList.map showVal)',
        '    | _ => "stopped"',
        # The emitter gives a function that calls VZEROUPPER a memory, which it doesn't touch.
        "instance : Shows (Mem → Outcome (Vec n w × Mem)) where",
        "  shows f := Shows.shows (andThen (f Ops.initial) fun r => Outcome.ok r.1)",
    ]
    rows = []
    for k, (op, n) in enumerate(zip(ops, counts, strict=True)):
        operands, at = [], 0
        for shape in op.args:
            lanes, w = shape
            operands.append(f"(val b (o + {at}) {w})" if lanes == 0 else f"(lanes b (o + {at}) {lanes} {w})")
            at += size(shape)
        call = f"{op.name} {' '.join(operands)}"
        src.append(
            f"def r{k} (b : ByteArray) (o : Nat) : String × String :=\n"
            f"  (Shows.shows (Ops.{call}), Shows.shows (OpsWrong.{call}))"
        )
        rows.append(f"({at}, {n}, r{k})")
    src += [
        "def table : Array (Nat × Nat × (ByteArray → Nat → String × String)) := #[",
        "  " + ",\n  ".join(rows) + "]",
        "def main (args : List String) : IO Unit := do",
        "  let b ← IO.FS.readBinFile args.head!",
        "  let mut o := 0",
        "  for (size, cases, run) in table do",
        "    for _ in [0:cases] do",
        "      let (model, wrong) := run b o",
        "      IO.println model",
        "      IO.println wrong",
        "      o := o + size",
    ]
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    env = lean_env(work)

    def compile_modules():
        for module in ("Ops", "X86Wrong", "OpsWrong"):
            out, source = os.path.join(work, f"{module}.olean"), os.path.join(work, f"{module}.lean")
            sh(["lean", "-R", work, "-o", out, source], env=env)

    printed = lean_output(work, ["lean", *NATIVE, "--run", path, inputs], env, compile_modules).splitlines()
    if len(printed) != 2 * sum(counts):
        sys.exit("Lean printed the wrong number of results")

    def read(line):
        return [int(x) for x in line.split()] if line.replace(" ", "").isdigit() else line

    results, at = [], 0
    for n in counts:
        results.append([(read(printed[at + 2 * c]), read(printed[at + 2 * c + 1])) for c in range(n)])
        at += 2 * n
    return results


def native_results(ops, counts, inputs, work):
    """What the processor gives for each case: for each operation, a list of lanes."""
    ll, c, exe = (os.path.join(work, name) for name in ("native.ll", "driver.c", "native"))
    rows = []
    # The first is every operation's but the optimized ones'.
    optimized = sorted({op.optimized for op in ops if op.optimized})
    groups = [ATTRIBUTES, *[f'noinline "target-features"="{features}"' for features in optimized]]
    with open(ll, "w") as f:
        f.write(f'target triple = "{TRIPLE}"\n')
        f.write("\n".join(sorted({op.declaration for op in ops})) + "\n")
        for op, n in zip(ops, counts, strict=True):
            group = optimized.index(op.optimized) + 1 if op.optimized else 0
            f.write(f"\ndefine void @run_{op.name}(ptr %in, ptr %out) #{group} {{\n")
            at = 0
            for i, shape in enumerate(op.args):
                f.write(f"  %p{i} = getelementptr i8, ptr %in, i64 {at}\n")
                f.write(f"  %a{i} = load {x86ops.ty(shape)}, ptr %p{i}, align 1\n")
                at += size(shape)
            f.write(f"  {op.lines}\n  store {x86ops.ty(op.ret)} %r, ptr %out, align 1\n  ret void\n}}\n")
            rows.append(f"{{run_{op.name}, {at}, {size(op.ret)}, {n}}}")
        f.write("\n" + "".join(f"attributes #{n} = {{ {g} }}\n" for n, g in enumerate(groups)))
    with open(c, "w") as f:
        f.write(DRIVER)
        for op in ops:
            f.write(f"void run_{op.name}(const unsigned char *, unsigned char *);\n")
        f.write("const struct op ops[] = {\n  " + ",\n  ".join(rows) + "};\n")
        f.write(f"const int count = {len(ops)};\n")
    sh(["clang", "-O1", "-Wno-override-module", ll, c, "-o", exe])
    printed = sh([exe, inputs], timeout=600).out.split()
    if len(printed) != sum(counts):
        sys.exit("native code printed the wrong number of results")
    results, at = [], 0
    for op, n in zip(ops, counts, strict=True):
        w = op.ret[1] // 8
        rows = [bytes.fromhex(line) for line in printed[at : at + n]]
        results.append(
            [[int.from_bytes(row[i : i + w], "little") for i in range(0, len(row), w)] for row in rows]
        )
        at += n
    return results


def modeled():
    """Every x86 intrinsic the classification calls modeled, but those LLVM's IR reader upgrades to something
    else before the emitter sees them."""
    with open(os.path.join(ROOT, "tests", "llvm_scope", "ir-features.json")) as f:
        items = json.load(f)["items"]
    return {
        i["name"]
        for i in items
        if i["kind"] == "intrinsic"
        and i["class"] == "modeled"
        and i["name"].startswith("llvm.x86.")
        and i["reason"] != "upgraded"
    }


def main():
    tool = os.path.abspath(sys.argv[1])
    ops = x86ops.OPS
    failed = False
    unchecked, extra = modeled() - x86ops.covered(ops), x86ops.covered(ops) - modeled()
    for name in sorted(unchecked):
        print(f"  FAIL {name} is modeled, and no operation here checks it")
        failed = True
    for name in sorted(extra):
        print(f"  FAIL {name} is checked here, and the classification doesn't call it modeled")
        failed = True
    with open("/proc/cpuinfo") as f:
        flags = set(f.read().split())
    if missing := sorted(flag for flag in x86ops.FEATURES.values() if flag not in flags):
        print(f"skip: this processor lacks {', '.join(missing)}")
        sys.exit(1 if failed else 77)
    rand = random.Random(17)
    cases = [x86ops.value_cases(op, rand) for op in ops]
    counts = [len(cs) for cs in cases]
    work = tempfile.mkdtemp(prefix="x86native-")
    try:
        inputs = os.path.join(work, "inputs.bin")
        with open(inputs, "wb") as f:
            for op, cs in zip(ops, cases, strict=True):
                for case in cs:
                    f.write(encode(op, case))
        lean = lean_results(tool, ops, counts, inputs, work)
        native = native_results(ops, counts, inputs, work)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    lanes = 0
    mismatches = []
    # Each intrinsic's wrong version, and whether the processor disagreed with it.
    refuted = dict.fromkeys(x86ops.covered([op for op in ops if op.mutant]), False)
    for op, cs, ls, ns in zip(ops, cases, lean, native, strict=True):
        for case, (model, wrong), got in zip(cs, ls, ns, strict=True):
            if model != got:
                mismatches.append((op.name, case, f"lean={model}", f"native={got}"))
            lanes += len(got)
            if op.mutant:
                refuted[op.intrinsic] |= wrong != got
    print(
        f"{len(x86ops.covered(ops))} intrinsics as {len(ops)} operations: {lanes} lanes of {sum(counts)} "
        f"results compared with the processor, {len(mismatches)} mismatches"
    )
    for m in mismatches[:20]:
        print("  MISMATCH", str(m)[:600])
    agree = sorted(name for name, r in refuted.items() if not r)
    print(
        f"a wrong version of each definition: the processor refutes it for {len(refuted) - len(agree)} of "
        f"{len(refuted)} intrinsics"
    )
    for name in agree:
        print(f"  FAIL no input tells {name} from its wrong version")
    failed = failed or bool(mismatches or agree) or not lanes
    print("FAIL" if failed else "ok")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
