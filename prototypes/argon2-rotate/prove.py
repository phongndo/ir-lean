#!/usr/bin/env python3
"""Checks, for each slice pair regions.py cut, a Lean theorem that the candidate's slice gives what clang's
does, for every input: docs/argon2.md. A prototype, outside CI.

For each region it translates both slice files with build/ir-lean, writes one theorem for each output, proved
by Rotate.lean's `rotate_slice`, compiles it with warnings as errors, and prints the axioms each rests on.
Then it plants wrong rewrites in the first region's target, and each has to stop a theorem with an error.

usage: prove.py REGIONS_DIR
Needs `lake build` and build/ir-lean, and runs in `nix develop`.
"""

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
TOOL = ROOT / "build" / "ir-lean"
# A wrong rewrite of region 0's target: what it replaces, in every function of the slice file, and with what.
ROTATE = "<8 x i64> poison, <8 x i32> <i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}>"
MUTANTS = {
    "row A rotated the other way": (
        ROTATE.format(3, 0, 1, 2, 7, 4, 5, 6),
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        2,
    ),
    "two lanes of one row swapped": (
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        ROTATE.format(1, 2, 3, 0, 5, 6, 4, 7),
        2,
    ),
}


def sh(*args: object, cwd: Path, env: dict[str, str]) -> tuple[int, str]:
    r = subprocess.run([str(a) for a in args], capture_output=True, text=True, cwd=cwd, env=env, check=False)
    return r.returncode, r.stdout + r.stderr


def translate(ll: Path, module: str, work: Path, env: dict[str, str]) -> None:
    for command in (
        (TOOL, ll, "-o", f"{module}.lean", "--namespace", module),
        ("lean", "-o", f"{module}.olean", f"{module}.lean"),
    ):
        code, said = sh(*command, cwd=work, env=env)
        if code != 0:
            sys.exit(f"{' '.join(map(str, command))}\n{said[-2000:]}")


def theorems(region: dict[str, Any], n: int) -> str:
    params = " ".join("v" + p[1:] for p in region["params"])
    lines = ["import Rotate", f"import R{n}Src", f"import R{n}Tgt", "", "open IRLean Argon2Rotate", ""]
    outputs = region["outputs"]
    for k, o in enumerate(outputs):
        name = f"r{n}_o{k}"
        lines += [
            f"/-- {o} of region {n}: with row A rotated, it's what rotating row B gives. -/",
            f"theorem {name}_same ({params} : Vec 8 64) :",
            f"    R{n}Tgt.{name}_tgt {params} = R{n}Src.{name}_src {params} := by",
            f"  rotate_slice R{n}Tgt.{name}_tgt R{n}Src.{name}_src "
            f"R{n}Tgt.{name}_tgt.step R{n}Src.{name}_src.step",
            "",
        ]
    return "\n".join(lines + [f"#print axioms r{n}_o{k}_same" for k in range(len(outputs))]) + "\n"


def main(where: Path) -> int:
    lean_path = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, cwd=ROOT, check=True
    )
    work = where / "lean"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir()
    env = {**os.environ, "LEAN_PATH": f"{work}:{lean_path.stdout.strip()}"}
    shutil.copy(HERE / "Rotate.lean", work)
    code, said = sh("lean", "-DwarningAsError=true", "-o", "Rotate.olean", "Rotate.lean", cwd=work, env=env)
    if code != 0:
        sys.exit(said)
    regions = json.loads((where / "regions.json").read_text())
    failed = False
    for region in regions:
        n = region["region"]
        translate(where / f"r{n}.src.ll", f"R{n}Src", work, env)
        translate(where / f"r{n}.tgt.ll", f"R{n}Tgt", work, env)
        (work / f"T{n}.lean").write_text(theorems(region, n))
        code, said = sh(
            "lean",
            "-DwarningAsError=true",
            "-M",
            "12000",
            "-o",
            f"T{n}.olean",
            f"T{n}.lean",
            cwd=work,
            env=env,
        )
        axioms = sorted(set(re.findall(r"depends on axioms: \[(.*?)\]", said)))
        count = len(region["outputs"])
        if (
            code != 0
            or said.count("depends on axioms") != count
            or axioms != ["propext, Classical.choice, Quot.sound"]
        ):
            failed = True
            print(f"FAIL  region {n}: exit {code}, axioms {axioms}\n{said[:1500]}")
        else:
            print(
                f"ok    region {n}, lines {region['lines'][0]} to {region['lines'][1]}: "
                f"{count} theorems, on {axioms[0]}"
            )
    target = (where / "r0.tgt.ll").read_text()
    for name, (old, new, each) in MUTANTS.items():
        functions = target.count("define ")
        if target.count(old) != each * functions:
            sys.exit(
                f"mutant {name}: its line is in the target {target.count(old)} times, not {each * functions}"
            )
        mutant = work / "mutant"
        shutil.rmtree(mutant, ignore_errors=True)
        mutant.mkdir()
        for file in ("Rotate.olean", "R0Src.olean"):
            shutil.copy(work / file, mutant)
        (mutant / "r0.tgt.ll").write_text(
            target.replace(old, new, 1) if each == 0 else target.replace(old, new)
        )
        translate(mutant / "r0.tgt.ll", "R0Tgt", mutant, {**env, "LEAN_PATH": f"{mutant}:{env['LEAN_PATH']}"})
        code, said = sh(
            "lean",
            "-M",
            "12000",
            work / "T0.lean",
            cwd=mutant,
            env={**env, "LEAN_PATH": f"{mutant}:{env['LEAN_PATH']}"},
        )
        errors = len(re.findall(r"error: unsolved goals", said))
        limits = re.findall(r"maximum recursion depth|deterministic timeout|out of memory", said)
        if code == 0 or not errors or limits:
            failed = True
            print(f"FAIL  mutant, {name}: exit {code}, {errors} theorems stopped, limits {limits}")
        else:
            print(f"ok    mutant, {name}: {errors} theorems stop with an error of their own")
    return 1 if failed else 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    sys.exit(main(Path(sys.argv[1]).resolve()))
