#!/usr/bin/env python3
"""Compile the pinned libsodium Argon2 rewrite and replay its whole-function proofs."""

import os
import re
import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "bench/kernels"))
sys.path.insert(0, str(ROOT / "tools"))
import demand  # noqa: E402
import kernels  # noqa: E402
from irlean import proc  # noqa: E402

AXIOMS = "propext, Classical.choice, Quot.sound"
FUNCTIONS = {"FillBlockWithXor": "fill_block_with_xor", "FillSegment": "argon2_fill_segment_avx512f"}
ROTATE = "<i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}>"
# Each control names a shuffle, its changed mask and the expected proof errors.
MUTANTS = {
    "fill_block_with_xor, first loop, in the region: row A rotated the other way at %204": (
        "fill_block_with_xor",
        204,
        ROTATE.format(3, 0, 1, 2, 7, 4, 5, 6),
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        {"FillBlockWithXor": "cut_store: the target doesn't store what its slice returns"},
    ),
    "fill_block_with_xor, first loop, before the region: two lanes swapped at %120": (
        "fill_block_with_xor",
        120,
        ROTATE.format(0, 1, 2, 3, 8, 9, 10, 11),
        ROTATE.format(1, 0, 2, 3, 8, 9, 10, 11),
        {"FillBlockWithXor": "sim_at: the two sides differ before the cut"},
    ),
    "argon2_fill_segment_avx512f, first loop, in the region: row A rotated the other way at %354": (
        "argon2_fill_segment_avx512f",
        354,
        ROTATE.format(3, 0, 1, 2, 7, 4, 5, 6),
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        {
            "FillBlockWithXor": None,
            "FillSegment": "cut_store: the target doesn't store what its slice returns",
        },
    ),
    "argon2_fill_segment_avx512f, second loop, in the region: two lanes of an output swapped at %599": (
        "argon2_fill_segment_avx512f",
        599,
        ROTATE.format(0, 1, 4, 5, 8, 9, 12, 13),
        ROTATE.format(1, 0, 4, 5, 8, 9, 12, 13),
        {
            "FillBlockWithXor": None,
            "FillSegment": "cut_store: the target doesn't store what its slice returns",
        },
    ),
}


def check(argv: list[str], work: Path, env: dict[str, str]) -> str:
    ran = proc.run(argv, cwd=work, env=env, timeout=900)
    if not ran.ok:
        raise RuntimeError(f"{argv[0]} exited {ran.exit}, {ran.limit}\n{ran.output[-3000:]}")
    return ran.out


def compile_inputs(work: Path, slices: Path) -> None:
    manifest = kernels.load()
    if errors := kernels.validate(manifest):
        raise ValueError(errors)
    if demand.pinned_clang() is None:
        raise ValueError("the proof needs the corpus's pinned clang")
    project = manifest["project"]["libsodium"]
    (unit,) = [u for u in project["unit"] if set(FUNCTIONS.values()) == set(u["kernels"])]
    src = kernels.source("libsodium", project)
    if src is None:
        raise RuntimeError("missing pinned libsodium source")
    build = demand.configure("libsodium", project, src, work)
    source = src / unit["source"]
    header = source.with_name("blamka-round-avx512f.h")
    shutil.copyfile(source, work / source.name)
    shutil.copyfile(header, work / header.name)
    for side in ("src", "tgt"):
        if side == "tgt":
            check(
                ["patch", "--fuzz=0", "-p5", "-i", str(HERE / "rotate-a.patch")], work, demand.environment()
            )
        ir = work / f"{side}.ll"
        argv = demand.command(manifest["corpus"], project, unit, {"src": str(src), "build": str(build)}, ir)
        # Compile both versions at the same path. The original directory supplies the unchanged local headers.
        if argv[-1] != str(source):
            raise ValueError("the corpus compile command changed its source")
        check([*argv[:-1], "-I", str(source.parent), source.name], work, demand.environment())
        check([str(slices), str(ir), side, str(work)], work, demand.environment())


def slice_theorems(n: int) -> str:
    params = " ".join(f"x{i}" for i in range(8))
    lines = ["import Rotate", f"import R{n}Src", f"import R{n}Tgt", "open IRLean Argon2Rotate"]
    for k in range(8):
        name = f"r{n}_o{k}"
        lines += [
            f"theorem {name}_same ({params} : Vec 8 64) :",
            f"    R{n}Tgt.{name}_tgt {params} = R{n}Src.{name}_src {params} := by",
            f"  rotate_slice R{n}Tgt.{name}_tgt R{n}Src.{name}_src "
            f"R{n}Tgt.{name}_tgt.step R{n}Src.{name}_src.step",
            f"#print axioms {name}_same",
        ]
    return "\n".join(lines) + "\n"


def lean(module: str) -> list[str]:
    return ["lean", "-M", "8000", "-DwarningAsError=true", "-o", f"{module}.olean", f"{module}.lean"]


def translate(tool: Path, work: Path, env: dict[str, str], ir: Path, module: str) -> None:
    check([str(tool), str(ir), "--no-code", "--namespace", module, "-o", f"{module}.lean"], work, env)
    check(lean(module), work, env)


def audit(output: str, names: set[str]) -> None:
    found = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", output)
    if sorted(found) != sorted((n, AXIOMS) for n in names):
        raise ValueError(f"unexpected theorem audit: {found}")


def plant(source: str, function: str, slot: int, old: str, new: str) -> str:
    instruction = rf"^  %{slot} = shufflevector [^\n]*?"
    pattern = rf"(^define [^\n]* @{function}\([^\n]*\n[^}}]*?{instruction}){re.escape(old)}"
    result, count = re.subn(pattern, lambda m: m[1] + new, source, flags=re.MULTILINE)
    if count != 1:
        raise ValueError(f"expected one shuffle mask at {function} %{slot}")
    return result


def prove(work: Path, tool: Path, slices: Path, lib: Path) -> None:
    compile_inputs(work, slices)
    env = {
        **os.environ,
        "ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip(),
        "LEAN_PATH": os.pathsep.join(map(str, (work, lib))),
    }
    for side, module in (("src", "Base"), ("tgt", "Cand")):
        translate(tool, work, env, work / f"{side}.ll", module)
    for module in ("Whole", "Rotate"):
        shutil.copyfile(HERE / f"{module}.lean", work / f"{module}.lean")
        check(lean(module), work, env)
    for n in range(4):
        for side in ("src", "tgt"):
            translate(tool, work, env, work / f"r{n}.{side}.ll", f"R{n}{side.title()}")
        (work / f"T{n}.lean").write_text(slice_theorems(n))
        audit(check(lean(f"T{n}"), work, env), {f"r{n}_o{k}_same" for k in range(8)})
    for module, fn in FUNCTIONS.items():
        shutil.copyfile(HERE / f"{module}.lean", work / f"{module}.lean")
        audit(check(lean(module), work, env), {f"{module}.{fn}", f"{module}.{fn}_same"})
        check(["leanchecker", module], work, env)
        print(f"ok    {fn}: whole-function proof replayed", flush=True)
    source = (work / "tgt.ll").read_text()
    for k, (name, (fn, slot, old, new, expect)) in enumerate(MUTANTS.items()):
        where = work / f"mutant{k}"
        where.mkdir()
        (where / "wrong.ll").write_text(plant(source, fn, slot, old, new))
        wrong_env = {**env, "LEAN_PATH": f"{where}:{env['LEAN_PATH']}"}
        translate(tool, where, wrong_env, where / "wrong.ll", "Cand")
        for module, expected in expect.items():
            shutil.copyfile(work / f"{module}.lean", where / f"{module}.lean")
            ran = proc.run(lean(module), cwd=where, timeout=900, env=wrong_env)
            errors = re.findall(r"error: (.*)", ran.output)
            if expected is None:
                if not ran.ok:
                    raise RuntimeError(ran.output)
            elif ran.exit != 1 or ran.limit or not errors or any(expected not in e for e in errors):
                raise RuntimeError(f"{name}: unexpected result {ran.exit}, {ran.limit}\n{ran.output}")
        print(f"ok    {name}", flush=True)


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit("usage: prove.py IR_LEAN ARGON2_SLICES LEAN_LIB")
    with tempfile.TemporaryDirectory(prefix="argon2-proof-") as tmp:
        prove(Path(tmp), *(Path(p).resolve() for p in sys.argv[1:]))
