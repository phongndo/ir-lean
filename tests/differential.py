#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Runs emitted Lean and the natively compiled function on the same inputs, and compares results.

Where Lean says poison or UB, native code may do anything, so those inputs are skipped. Lean runs
first, so inputs that would crash native code never reach it.

usage: tests/differential.py path/to/llvm-lean file.c|file.ll [...] [--runs N] [--bound FUNCTION=MAX]
                             [--split] [--only PREFIX] [--strict] [--slow PREFIX=N]
                             [--expect-ub | --expect-stop]

`--bound` keeps a function's inputs small, for functions that would otherwise run for too long or
overflow the stack. `--split` builds one Lean module per function, which large inputs need. It builds
LEAN_JOBS at a time, and keeps them in LEAN_CACHE so another run doesn't repeat that work. `--only`
tests just the functions whose names start with PREFIX. `--strict` fails on any skipped input, for
code that shouldn't hit poison or UB, where a bug in the semantics would otherwise only skip it. `--slow`
runs functions whose names start with PREFIX only N times. `--expect-ub` fails unless every function
translates and every call stops on undefined behavior, and `--expect-stop` does the same for the model
stopping without an answer, which isn't undefined behavior.
"""

import concurrent.futures
import glob
import hashlib
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_WIDTH = 64
# A runaway check fails with Lean's own error instead of taking the machine's memory.
LEAN_MAX_MB = os.environ.get("LEAN_MAX_MB", "6000")
# Modules at a time. What limits this is memory: `inflate` alone peaks near 4 GB.
LEAN_JOBS = int(os.environ.get("LEAN_JOBS", "4"))
LEAN_CACHE = os.environ.get("LEAN_CACHE", os.path.join(ROOT, "build", "lean-cache"))


class Stats:
    def __init__(self):
        self.functions = self.compared = self.skipped = 0
        self.mismatches = []
        self.unsupported = {}
        self.skip_reasons = {}


def sh(args, **kw):
    r = subprocess.run(args, text=True, capture_output=True, check=False, **kw)
    if r.returncode != 0:
        sys.exit(f"{args[0]} failed:\n{(r.stdout + r.stderr)[:3000]}")
    return r


def lean_env(work):
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([os.path.join(ROOT, ".lake", "build", "lib", "lean"), work])
    return env


def report(tool, ll, only=""):
    """Returns ([(llvm name, lean name, parameter widths, result width, uses memory)], unsupported
    reasons)."""
    out = sh([tool, ll, "--report"]).stdout.splitlines()
    runnable, reasons = [], {}
    for line in out:
        fields = line.split("\t")
        if fields[0] == "unsupported":
            reasons[fields[1]] = fields[2]
        elif fields[0] == "ok" and fields[1].startswith(only):
            m = re.fullmatch(r"\((.*)\)->(\w+)", fields[3])
            assert m, fields[3]
            params = [p for p in m.group(1).split(",") if p]
            if all(re.fullmatch(r"i\d+", t) for t in [*params, m.group(2)]):
                widths = [int(t[1:]) for t in params]
                ret = int(m.group(2)[1:])
                if ret <= MAX_WIDTH and all(w <= MAX_WIDTH for w in widths):
                    runnable.append((fields[1], fields[2], widths, ret, fields[6] == "memory"))
    return runnable, reasons


def edge_values(w):
    m = (1 << w) - 1
    return [0, 1, 2, 3, m, m - 1, 1 << (w - 1), (1 << (w - 1)) - 1]


def inputs_for(widths, runs, rand):
    picked = []
    for _ in range(runs):
        picked.append(
            [rand.choice(edge_values(w)) if rand.random() < 0.4 else rand.getrandbits(w) for w in widths]
        )
    return picked


def build_lean(tool, ll, work, split):
    """Translates `ll` to the Lean module M and compiles it."""
    env = lean_env(work)
    lean = os.path.join(work, "M.lean")
    args = [tool, ll, "--namespace", "M"] + (["--split", work] if split else ["-o", lean])
    r = subprocess.run(args, text=True, capture_output=True, check=False)
    if r.returncode not in (0, 3):
        sys.exit(f"llvm-lean failed:\n{r.stderr}")
    if split:
        build_modules(work, env)
    sh(["lean", "-M", LEAN_MAX_MB, "-R", work, "-o", os.path.join(work, "M.olean"), lean], env=env)


def build_modules(work, env):
    """Compiles what `--split` wrote, each module after what it imports. A module's cache entry is named
    after its text, what it imports and the library, so a change to any of them misses the cache."""
    with open(os.path.join(work, "M.lean")) as f:
        modules = [line.split()[1].removeprefix("M.") for line in f if line.startswith("import ")]
    library = hashlib.sha256(sh(["lean", "--version"]).stdout.encode())
    lib_dir = os.path.join(ROOT, ".lake", "build", "lib", "lean")
    for path in sorted(
        glob.glob(os.path.join(lib_dir, "LLVMLean*")) + glob.glob(os.path.join(lib_dir, "LLVMLean", "*"))
    ):
        if path.endswith(".olean"):
            with open(path, "rb") as f:
                library.update(f.read())
    keys, waiting = {}, {}
    for module in modules:
        with open(os.path.join(work, "M", module + ".lean")) as f:
            text = f.read()
        imports = re.findall(r"^import M\.(\w+)$", text, flags=re.M)
        waiting[module] = set(imports)
        key = hashlib.sha256(library.digest() + text.encode() + "".join(keys[i] for i in imports).encode())
        keys[module] = key.hexdigest()

    def build(module):
        target = os.path.join(work, "M", module + ".olean")
        cached = os.path.join(LEAN_CACHE, f"{module}.{keys[module]}.olean")
        if os.path.exists(cached):
            shutil.copyfile(cached, target)
            return
        sh(
            ["lean", "-M", LEAN_MAX_MB, "-R", work, "-o", target, os.path.join(work, "M", module + ".lean")],
            env=env,
        )
        os.makedirs(LEAN_CACHE, exist_ok=True)
        for old in glob.glob(os.path.join(glob.escape(LEAN_CACHE), glob.escape(module) + ".*.olean")):
            os.remove(old)
        partial = f"{cached}.{os.getpid()}"
        shutil.copyfile(target, partial)
        os.replace(partial, cached)

    with concurrent.futures.ThreadPoolExecutor(LEAN_JOBS) as pool:
        running = {}
        while waiting or running:
            for module in [m for m, needs in waiting.items() if not needs]:
                running[pool.submit(build, module)] = module
                del waiting[module]
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                finished = running.pop(future)
                future.result()
                for needs in waiting.values():
                    needs.discard(finished)


def run_lean(functions, cases, work):
    env = lean_env(work)
    src = [
        "import M",
        "open LLVMLean",
        "set_option maxRecDepth 1000000",
        # Lean prints warnings with the results, and a function with no parameters doesn't use `c`.
        "set_option linter.unusedVariables false",
        "def show' {w : Nat} : Outcome (Val w) → String",
        "  | some (.ok (some v)) => toString v.toNat",
        '  | some (.ok none) => "poison"',
        '  | some (.error (.undefined e)) => "ub:" ++ reprStr e',
        '  | some (.error (.model e)) => "stop:" ++ reprStr e',
        '  | none => "diverged"',
        "def showMem {w : Nat} (x : Outcome (Val w × Mem)) : String :=",
        "  show' (andThen x fun r => Outcome.ok r.1)",
    ]
    runners = []
    for i, (_, name, widths, _, memory) in enumerate(functions):
        args = " ".join(f"(some (BitVec.ofNat {w} c[{k}]!))" for k, w in enumerate(widths))
        call = f"showMem (M.{name} {args} M.initial)" if memory else f"show' (M.{name} {args})"
        src.append(f"def r{i} : IO Unit := for c in ({cases[i]} : List (List Nat)) do IO.println ({call})")
        runners.append(f"r{i}")
    src.append("def main : IO Unit := do\n  for r in [" + ", ".join(runners) + "] do r")
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    out = sh(["lean", "-M", LEAN_MAX_MB, "--run", path], env=env).stdout.split()
    return out


def abi_attributes(ll):
    """`signext` and `zeroext` on parameters are part of the call, so the driver must repeat them."""
    attrs = {}
    with open(ll) as f:
        for line in f:
            m = re.match(r"define\b.*?@(?:\"([^\"]+)\"|([\w.$-]+))\((.*)\)", line)
            if m:
                name = m.group(1) or m.group(2)
                found = re.findall(r"i\d+ ((?:[\w]+(?:\([^)]*\))? )*)%", m.group(3))
                attrs[name] = [" ".join(a for a in p.split() if a in ("signext", "zeroext")) for p in found]
    return attrs


def run_native(functions, cases, keep, ll, work):
    attrs = abi_attributes(ll)
    decls = ['@fmt = private constant [6 x i8] c"%llu\\0A\\00"', "declare i32 @printf(ptr, ...)"]
    calls, n = [], 0
    for i, (name, _, widths, ret, _) in enumerate(functions):
        fn_attrs = attrs.get(name, [""] * len(widths))
        params = ", ".join(f"i{w} {a}".strip() for w, a in zip(widths, fn_attrs, strict=True))
        decls.append(f'declare i{ret} @"{name}"({params})')
        for c, wanted in zip(cases[i], keep[i], strict=True):
            if not wanted:
                continue
            args = ", ".join(
                f"i{w} {a} {v}".replace("  ", " ") for w, a, v in zip(widths, fn_attrs, c, strict=True)
            )
            calls.append(f'  %r{n} = call i{ret} @"{name}"({args})')
            if ret < 64:
                calls.append(f"  %z{n} = zext i{ret} %r{n} to i64")
                value = f"%z{n}"
            else:
                value = f"%r{n}"
            calls.append(f"  call i32 (ptr, ...) @printf(ptr @fmt, i64 {value})")
            n += 1
    driver = os.path.join(work, "driver.ll")
    with open(driver, "w") as f:
        f.write("\n".join(decls) + "\n\ndefine i32 @main() {\n" + "\n".join(calls) + "\n  ret i32 0\n}\n")
    # Functions the optimizer could otherwise hide or merge must stay callable from the driver.
    with open(ll) as f:
        text = re.sub(r"^define (internal|private) ", "define ", f.read(), flags=re.M)
    visible = os.path.join(work, "visible.ll")
    with open(visible, "w") as f:
        f.write(text)
    exe = os.path.join(work, "native")
    sh(["clang", "-O1", "-Wno-override-module", visible, driver, "-o", exe])
    return sh([exe], timeout=300).stdout.split()


def has_no_result(x):
    return x == "poison" or x == "diverged" or x.startswith(("ub:", "stop:"))


def compare_ll(tool, ll, runs, rand, stats, bounds=None, split=False, only="", slow=None):
    bounds = bounds or {}
    with tempfile.TemporaryDirectory(prefix="diff-") as work:
        functions, reasons = report(tool, ll, only)
        stats.unsupported.update(reasons)
        if not functions:
            return
        build_lean(tool, ll, work, split)
        cases = [inputs_for(f[2], runs, rand) for f in functions]
        for i, (name, *_) in enumerate(functions):
            if name in bounds:
                cases[i] = [[v % (bounds[name] + 1) for v in c] for c in cases[i]]
            if slow and name.startswith(slow[0]):
                cases[i] = cases[i][: slow[1]]
        kept = [(f, c) for f, c in zip(functions, cases, strict=True) if c]
        functions, cases = [f for f, _ in kept], [c for _, c in kept]
        stats.functions += len(functions)
        lean_out = run_lean(functions, cases, work)
        keep, values, pos = [], [], 0
        for i in range(len(functions)):
            row = lean_out[pos : pos + len(cases[i])]
            pos += len(cases[i])
            keep.append([not has_no_result(x) for x in row])
            values.append(row)
            stats.skipped += sum(not k for k in keep[-1])
            for x in row:
                if has_no_result(x):
                    kind = x.replace("ub:LLVMLean.UB.", "undefined: ")
                    kind = kind.replace("stop:LLVMLean.ModelStop.", "model stop: ")
                    why = f"{kind} in @{functions[i][0]}"
                    stats.skip_reasons[why] = stats.skip_reasons.get(why, 0) + 1
        native = iter(run_native(functions, cases, keep, ll, work))
        for i, (name, *_) in enumerate(functions):
            for c, k, v in zip(cases[i], keep[i], values[i], strict=True):
                if not k:
                    continue
                stats.compared += 1
                got = next(native)
                if got != v:
                    stats.mismatches.append((name, c, f"lean={v}", f"native={got}"))


def compile_input(path, work):
    if path.endswith(".ll"):
        return path
    out = os.path.join(work, os.path.basename(path) + ".ll")
    sh(
        [
            "clang",
            "-O2",
            "-fno-strict-aliasing",
            "-S",
            "-emit-llvm",
            "-fno-discard-value-names",
            path,
            "-o",
            out,
        ]
    )
    return out


def summarize(stats, strict=False):
    print(
        f"{stats.functions} functions: {stats.compared} results compared with native, "
        f"{stats.skipped} skipped (poison or UB), {len(stats.mismatches)} mismatches"
    )
    if stats.skip_reasons:
        print("skipped because of: " + ", ".join(f"{k} {v}" for k, v in sorted(stats.skip_reasons.items())))
    for m in stats.mismatches[:20]:
        print("  MISMATCH", m)
    if stats.unsupported:
        print(f"{len(stats.unsupported)} left out:")
        for name, why in list(stats.unsupported.items())[:12]:
            print(f"  @{name}: {why[:120]}")
    return 1 if stats.mismatches or not stats.compared or (strict and stats.skipped) else 0


def all_stopped(stats, kind):
    """Whether every call stopped for this kind of reason, and not with a value, poison or divergence, or
    for the other kind of reason."""
    print(f"{stats.functions} functions: {stats.skipped} calls stopped, {stats.compared} returned a value")
    print("because of: " + ", ".join(f"{k} {v}" for k, v in sorted(stats.skip_reasons.items())))
    for name, why in stats.unsupported.items():
        print(f"  left out @{name}: {why[:120]}")
    other = [k for k in stats.skip_reasons if not k.startswith(kind + ":")]
    if other:
        print(f"not {kind}: " + ", ".join(sorted(other)))
    return bool(stats.skipped) and not (stats.compared or stats.unsupported or other)


def main():
    args = sys.argv[1:]
    runs = 200
    if "--runs" in args:
        i = args.index("--runs")
        runs = int(args[i + 1])
        del args[i : i + 2]
    bounds = {}
    while "--bound" in args:
        i = args.index("--bound")
        name, limit = args[i + 1].split("=")
        bounds[name] = int(limit)
        del args[i : i + 2]
    split = "--split" in args
    if split:
        args.remove("--split")
    only = ""
    if "--only" in args:
        i = args.index("--only")
        only = args[i + 1]
        del args[i : i + 2]
    strict = "--strict" in args
    if strict:
        args.remove("--strict")
    slow = None
    if "--slow" in args:
        i = args.index("--slow")
        prefix, count = args[i + 1].split("=")
        slow = (prefix, int(count))
        del args[i : i + 2]
    expect = None
    for flag, kind in (("--expect-ub", "undefined"), ("--expect-stop", "model stop")):
        if flag in args:
            args.remove(flag)
            expect = kind
    tool, files = os.path.abspath(args[0]), args[1:]
    rand, stats = random.Random(11), Stats()
    work = tempfile.mkdtemp(prefix="diffinput-")
    untested = []
    try:
        for path in files:
            before = stats.skipped if expect else stats.compared
            compare_ll(tool, compile_input(path, work), runs, rand, stats, bounds, split, only, slow)
            if (stats.skipped if expect else stats.compared) == before:
                untested.append(path)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    code = (0 if all_stopped(stats, expect) else 1) if expect else summarize(stats, strict)
    if untested:
        print("nothing tested in: " + ", ".join(untested))
        code = 1
    sys.exit(code)


if __name__ == "__main__":
    main()
