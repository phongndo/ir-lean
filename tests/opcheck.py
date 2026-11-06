#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks every integer operation in LLVMLean, through the emitter, against LLVM itself.

Two oracles, because neither is enough alone:
  - LLVM's constant folder, for values at many widths. It usually ignores poison flags, folding
    `add nuw i8 255, 1` to 0 (a legal refinement), so it can't check them.
  - Alive2, for exact poison and UB behavior. For small widths, the Lean results become a lookup
    table in IR, and Alive2 must prove the table and the instruction refine each other.

usage: tests/opcheck.py path/to/llvm-lean [--no-alive]
"""

import concurrent.futures
import itertools
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WRAP = ["", "nuw", "nsw", "nuw nsw"]
PREDS = "eq ne ugt uge ult ule sgt sge slt sle".split()
# Stands for a poison operand in a test case. It's larger than any value tested.
POISON = 1 << 200


def binary(name, flags, w):
    return [
        (f"{name} {f}".strip(), [w, w], w, f"%r = {name} {f} i{w} %a0, %a1\n  ret i{w} %r") for f in flags
    ]


def intrinsic(name, args, ret, extra="", suffix=None):
    """`args` are parameter widths. `extra` is appended after the parameters, like `i1 true`."""
    names = ", ".join(f"i{w} %a{i}" for i, w in enumerate(args))
    sep = ", " if extra else ""
    suffix = suffix if suffix else f"i{args[0]}"
    decl_args = ", ".join([f"i{w}" for w in args] + ([extra.split()[0]] if extra else []))
    decl = f"declare i{ret} @llvm.{name}.{suffix}({decl_args})"
    body = f"%r = call i{ret} @llvm.{name}.{suffix}({names}{sep}{extra})\n  ret i{ret} %r"
    return decl, body


def variants(w):
    """Yields (id, parameter widths, result width, body, declarations)."""
    out = []
    for name, flags in [
        ("add", WRAP),
        ("sub", WRAP),
        ("mul", WRAP),
        ("shl", WRAP),
        ("udiv", ["", "exact"]),
        ("sdiv", ["", "exact"]),
        ("urem", [""]),
        ("srem", [""]),
        ("lshr", ["", "exact"]),
        ("ashr", ["", "exact"]),
        ("and", [""]),
        ("or", ["", "disjoint"]),
        ("xor", [""]),
    ]:
        out += [(i, a, r, b, []) for i, a, r, b in binary(name, flags, w)]
    for p in PREDS:
        for f in ["", "samesign"]:
            out.append(
                (
                    f"icmp {f} {p}".replace("  ", " "),
                    [w, w],
                    1,
                    f"%r = icmp {f} {p} i{w} %a0, %a1\n  ret i1 %r",
                    [],
                )
            )
    out.append(("select", [1, w, w], w, f"%r = select i1 %a0, i{w} %a1, i{w} %a2\n  ret i{w} %r", []))
    out.append(("freeze", [w], w, f"%r = freeze i{w} %a0\n  ret i{w} %r", []))
    wider, narrower = w * 2, max(1, w // 2)
    for f in ["", "nneg"]:
        out.append(
            (f"zext {f}".strip(), [w], wider, f"%r = zext {f} i{w} %a0 to i{wider}\n  ret i{wider} %r", [])
        )
    out.append(("sext", [w], wider, f"%r = sext i{w} %a0 to i{wider}\n  ret i{wider} %r", []))
    if narrower < w:
        for f in WRAP:
            out.append(
                (
                    f"trunc {f}".strip(),
                    [w],
                    narrower,
                    f"%r = trunc {f} i{w} %a0 to i{narrower}\n  ret i{narrower} %r",
                    [],
                )
            )
    for n in "umin umax smin smax uadd.sat usub.sat sadd.sat ssub.sat".split():
        d, b = intrinsic(n, [w, w], w)
        out.append((n, [w, w], w, b, [d]))
    for n in "ctpop bitreverse".split():
        d, b = intrinsic(n, [w], w)
        out.append((n, [w], w, b, [d]))
    if w % 16 == 0:
        d, b = intrinsic("bswap", [w], w)
        out.append(("bswap", [w], w, b, [d]))
    for n in "ctlz cttz abs".split():
        for flag in ["false", "true"]:
            d, b = intrinsic(n, [w], w, f"i1 {flag}")
            out.append((f"{n} {flag}", [w], w, b, [d]))
    for n in "fshl fshr".split():
        d, b = intrinsic(n, [w, w, w], w)
        out.append((n, [w, w, w], w, b, [d]))
    for n in "uadd sadd usub ssub umul smul".split():
        name = f"{n}.with.overflow"
        decl = f"declare {{i{w}, i1}} @llvm.{name}.i{w}(i{w}, i{w})"
        for field, ret in [(0, w), (1, 1)]:
            body = (
                f"%p = call {{i{w}, i1}} @llvm.{name}.i{w}(i{w} %a0, i{w} %a1)\n"
                f"  %r = extractvalue {{i{w}, i1}} %p, {field}\n  ret i{ret} %r"
            )
            out.append((f"{name} {field}", [w, w], ret, body, [decl]))
    if w >= 2:
        for n in "ucmp scmp".split():
            d, b = intrinsic(n, [w, w], 8, suffix=f"i8.i{w}")
            out.append((n, [w, w], 8, b, [d]))
    return out


def fn_name(ident, w):
    return re.sub(r"\W+", "_", f"{ident}_w{w}")


def interesting(w):
    m = (1 << w) - 1
    vals = {
        0,
        1,
        2,
        3,
        m,
        m - 1,
        1 << (w - 1),
        (1 << (w - 1)) - 1,
        ((1 << (w - 1)) + 1) & m,
        w & m,
        (w - 1) & m,
    }
    return sorted(v & m for v in vals)


def cases_for(widths, rand):
    """Every input if there are few, otherwise edge cases, random values, and poison operands."""
    if sum(widths) <= 10:
        return [list(c) for c in itertools.product(*[range(1 << w) for w in widths])]
    picked = []
    for _ in range(96):
        picked.append(
            [rand.choice(interesting(w)) if rand.random() < 0.5 else rand.getrandbits(w) for w in widths]
        )
    for position in range(len(widths)):
        for _ in range(4):
            case = [rand.choice(interesting(w)) for w in widths]
            case[position] = POISON
            picked.append(case)
    return picked


def sh(args, **kw):
    r = subprocess.run(args, text=True, capture_output=True, check=False, **kw)
    if r.returncode != 0:
        sys.exit(f"{args[0]} failed:\n{(r.stdout + r.stderr)[:3000]}")
    return r


def lean_env(work):
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([os.path.join(ROOT, ".lake", "build", "lib", "lean"), work])
    return env


def build_table(tool, work):
    rand = random.Random(7)
    widths = [1, 2, 3, 4, 8, 16, 32, 64, 128]
    decls, funcs, table, shapes = set(), [], [], {}
    for w in widths:
        for ident, args, ret, body, ds in variants(w):
            name = fn_name(ident, w)
            decls.update(ds)
            params = ", ".join(f"i{a} %a{i}" for i, a in enumerate(args))
            funcs.append(f"define i{ret} @{name}({params}) {{\n  {body}\n}}\n")
            shape = tuple(args)
            shapes.setdefault(shape, cases_for(shape, rand))
            table.append((name, ident, w, shape, ret, body, ds))
    ops = os.path.join(work, "ops.ll")
    with open(ops, "w") as f:
        f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(funcs))
    lean = os.path.join(work, "Ops.lean")
    r = subprocess.run(
        [tool, ops, "-o", lean, "--namespace", "Ops"], text=True, capture_output=True, check=False
    )
    if r.returncode != 0:
        sys.exit(f"emitter left functions out:\n{r.stderr}")
    return table, shapes, lean


def eval_in_lean(table, shapes, lean, work):
    env = lean_env(work)
    sh(["lean", "-R", work, "-o", os.path.join(work, "Ops.olean"), lean], env=env)
    shape_names = {s: "shape_" + "_".join(map(str, s)) for s in shapes}
    src = [
        "import Ops",
        "open LLVMLean",
        "set_option maxRecDepth 1000000",
        "def show' {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok (some v)) => toString v.toNat",
        '  | some (.ok none) => "poison"',
        '  | some (.error _) => "ub"',
        '  | none => "diverged"',
    ]
    for s, n in shape_names.items():
        src.append(f"def {n} : List (List Nat) := {shapes[s]}")
    src.append(f"def lit (w n : Nat) : Val w := if n == {POISON} then none else some (BitVec.ofNat w n)")
    runners = []
    for i, (name, _, _, shape, _, _, _) in enumerate(table):
        args = " ".join(f"(lit {w} c[{k}]!)" for k, w in enumerate(shape))
        src.append(
            f"def r{i} : IO Unit := for c in {shape_names[shape]} do IO.println (show' (Ops.{name} {args}))"
        )
        runners.append(f"r{i}")
    src.append("def main : IO Unit := do\n  for r in [" + ", ".join(runners) + "] do r")
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    out = sh(["lean", "--run", path], env=env).stdout.split()
    results, pos = {}, 0
    for name, _, _, shape, _, _, _ in table:
        n = len(shapes[shape])
        results[name] = out[pos : pos + n]
        pos += n
    if pos != len(out):
        sys.exit("Lean printed the wrong number of results")
    return results


def check_folder(table, shapes, results, work):
    """A value from Lean must equal the fold. Lean's poison or UB may fold to anything, since that
    only refines. A fold to poison where Lean has a value would make Lean too defined."""
    src, decls, keys = [], set(), []
    for name, _, _, shape, ret, body, ds in table:
        decls.update(ds)
        for ci, c in enumerate(shapes[shape]):
            text = body
            for k, (w, v) in enumerate(zip(shape, c, strict=True)):
                constant = "poison" if v == POISON else str(v) if w > 1 else ("true" if v else "false")
                text = text.replace(f"%a{k}", constant)
            fn = f"{name}__{ci}"
            src.append(f"define i{ret} @{fn}() {{\n  {text}\n}}\n")
            keys.append((name, ci))
    path = os.path.join(work, "fold.ll")
    with open(path, "w") as f:
        f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(src))
    folded = sh(["opt", "-passes=instsimplify", "-S", path]).stdout
    found = {}
    for m in re.finditer(r"define i(\d+) @(\w+)\(\) [^{]*\{\n((?:.*\n)*?)\}", folded):
        ret_w, fn, body = int(m.group(1)), m.group(2), m.group(3)
        lines = [line for line in body.splitlines() if line.strip()]
        r = re.fullmatch(r"\s*ret i\d+ (poison|true|false|-?\d+)", lines[-1]) if len(lines) == 1 else None
        if r:
            v = r.group(1)
            found[fn] = (
                v
                if v == "poison"
                else {"true": 1, "false": 0}.get(v, int(v) if v not in ("true", "false") else 0)
                & ((1 << ret_w) - 1)
            )
    agreed = refined = unfolded = 0
    bad = []
    for name, ci in keys:
        lean = results[name][ci]
        fold = found.get(f"{name}__{ci}")
        if fold is None:
            unfolded += 1
        elif lean in ("poison", "ub"):
            refined += 1
        elif fold == "poison" or int(lean) != fold:
            bad.append((name, ci, lean, fold))
        else:
            agreed += 1
    return agreed, refined, unfolded, bad


def alive_case(tool_args):
    name, shape, ret, body, ds, cases, res, work = tool_args
    params = ", ".join(f"i{a} noundef %a{i}" for i, a in enumerate(shape))
    bits = sum(shape) + 1
    idx = [f"  %x0 = zext i{shape[0]} %a0 to i{bits}", ""][0:1]
    cur, shift = "%x0", shape[0]
    for k, w in enumerate(shape[1:], 1):
        idx.append(f"  %x{k} = zext i{w} %a{k} to i{bits}")
        idx.append(f"  %s{k} = shl i{bits} %x{k}, {shift}")
        idx.append(f"  %o{k} = or i{bits} {cur}, %s{k}")
        cur, shift = f"%o{k}", shift + w
    arms, blocks = [], []
    for ci, (c, r) in enumerate(zip(cases, res, strict=True)):
        key, sh_ = 0, 0
        for w, v in zip(shape, c, strict=True):
            key |= v << sh_
            sh_ += w
        arms.append(f"i{bits} {key}, label %c{ci}")
        if r == "ub":
            blocks.append(f"c{ci}:\n  unreachable")
        else:
            blocks.append(f"c{ci}:\n  ret i{ret} {'poison' if r == 'poison' else r}")
    table = (
        f"define i{ret} @F({params}) {{\n"
        + "\n".join(idx)
        + f"\n  switch i{bits} {cur}, label %d [\n    "
        + "\n    ".join(arms)
        + "\n  ]\nd:\n  unreachable\n"
        + "\n".join(blocks)
        + "\n}\n"
    )
    src = f"define i{ret} @F({params}) {{\n  {body}\n}}\n"
    verdicts = []
    for direction, (a, b) in (
        ("instruction refines table", (src, table)),
        ("table refines instruction", (table, src)),
    ):
        with tempfile.TemporaryDirectory(dir=work) as d:
            pa, pb = os.path.join(d, "a.ll"), os.path.join(d, "b.ll")
            decl = "\n".join(ds) + "\n"
            with open(pa, "w") as f:
                f.write(decl + a)
            with open(pb, "w") as f:
                f.write(decl + b)
            r = subprocess.run(
                ["alive-tv", "--disable-undef-input", pa, pb],
                text=True,
                capture_output=True,
                timeout=300,
                check=False,
            )
            o = r.stdout + r.stderr
            if "1 correct transformations" in o and "0 incorrect" in o:
                verdicts.append(None)
            elif (
                "ERROR:" in o
                and "doesn't verify" not in o
                and "incorrect" not in o.split("Summary")[0].lower().replace("0 incorrect", "")
            ):
                verdicts.append(("skip", o[:400]))
            else:
                verdicts.append(("fail", direction, o[:800]))
    return name, verdicts


def check_alive(table, shapes, results, work):
    jobs = []
    for name, _, w, shape, ret, body, ds in table:
        cases = shapes[shape]
        if (
            sum(shape) > 8
            or len(cases) != 1 << sum(shape)
            or (w not in (1, 2, 4) and not (w == 3 and len(shape) == 3))
        ):
            continue
        res = results[name]
        if "diverged" in res:
            continue
        jobs.append((name, shape, ret, body, ds, cases, res, work))
    proved, failed, skipped = 0, [], []
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        for name, verdicts in pool.map(alive_case, jobs):
            kinds = [v[0] for v in verdicts if v]
            if "fail" in kinds:
                failed.append((name, next(v for v in verdicts if v and v[0] == "fail")))
            elif "skip" in kinds:
                skipped.append((name, next(v for v in verdicts if v)[1]))
            else:
                proved += 1
    return proved, failed, skipped


def main():
    tool = os.path.abspath(sys.argv[1])
    use_alive = "--no-alive" not in sys.argv
    work = tempfile.mkdtemp(prefix="opcheck-")
    try:
        table, shapes, lean = build_table(tool, work)
        results = eval_in_lean(table, shapes, lean, work)
        total = sum(len(shapes[t[3]]) for t in table)
        print(f"{len(table)} operation variants, {total} cases")
        agreed, refined, unfolded, bad = check_folder(table, shapes, results, work)
        print(
            f"constant folder: {agreed} agree, {refined} where Lean is poison or UB and LLVM refines it, "
            f"{unfolded} not folded, {len(bad)} wrong"
        )
        for b in bad[:25]:
            print("  WRONG", b)
        failed = bool(bad)
        if use_alive and shutil.which("alive-tv"):
            proved, afail, skipped = check_alive(table, shapes, results, work)
            print(
                f"alive2: {proved} variants proved exact in both directions, {len(afail)} wrong, "
                f"{len(skipped)} it couldn't check"
            )
            for name, v in afail[:15]:
                print("  WRONG", name, v[1], "\n", v[2])
            for name, why in skipped[:8]:
                print("  skipped", name, why.strip().splitlines()[-1][:160] if why.strip() else "")
            failed = failed or bool(afail)
        elif use_alive:
            print("alive2: alive-tv is not on PATH, so poison flags were not checked")
        sys.exit(1 if failed else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
