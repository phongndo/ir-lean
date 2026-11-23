#!/usr/bin/env python3
"""Checks, from the two IR files, that the Argon2 round's rewrite refines clang's as whole functions: README.md.
A prototype, outside CI.

It translates both files with ir-lean, the baseline as `Base` and the candidate as `Cand`, and the regions' slices,
proves the slices equal as `prototypes/argon2-rotate/prove.py` does, writes each function's proof with gen.py and
compiles it with warnings as errors, prints the axioms the theorems rest on, and replays the two modules with
leanchecker. Then it plants wrong candidates, one shuffle mask each, and the same proof files have to stop on each
with an error of their own, where it says.

Each Lean process runs under `timeout 900` and `-M 8000`, one at a time, and its time and peak memory are printed.
It writes only to a temporary directory.

usage: prove.py PILOT_DIR IR_LEAN LEAN_LIB [--write]
PILOT_DIR holds candidate.base.pic.ll, candidate.pic.ll and regions/ (regions.json, rN.src.ll, rN.tgt.ll), IR_LEAN
is the emitter, and LEAN_LIB the built library, `.lake/build/lib/lean`. With --write, the two proofs gen.py wrote are
left next to this file, to read. Runs in `nix develop`.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
AXIOMS = "propext, Classical.choice, Quot.sound"
LIMIT = re.compile(
    r"maximum number of heartbeats|deterministic\)? timeout|maximum recursion depth|deep recursion|stack overflow|"
    r"excessive memory|out of memory|maximum number of steps"
)
# The functions, callees first: the function, its module, and the callees' proofs it uses.
FUNCTIONS = [
    ("fill_block_with_xor", "FillBlockWithXor", []),
    (
        "argon2_fill_segment_avx512f",
        "FillSegment",
        ["fill_block_with_xor=FillBlockWithXor.fill_block_with_xor_same:FillBlockWithXor"],
    ),
]
ROTATE = "<i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}, i32 {}>"
# Wrong candidates: the line of candidate.pic.ll, what's on it, what replaces it, and for each proof module whether
# it still checks or the error it has to stop with.
MUTANTS = {
    "fill_block_with_xor, first loop, in the region: row A rotated the other way at %204": (
        1118,
        ROTATE.format(3, 0, 1, 2, 7, 4, 5, 6),
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        {"FillBlockWithXor": "cut_store: the target doesn't store what its slice returns"},
    ),
    "fill_block_with_xor, first loop, before the region: two lanes swapped at %120": (
        1034,
        ROTATE.format(0, 1, 2, 3, 8, 9, 10, 11),
        ROTATE.format(1, 0, 2, 3, 8, 9, 10, 11),
        {"FillBlockWithXor": "sim_at: the two sides differ before the cut"},
    ),
    "argon2_fill_segment_avx512f, first loop, in the region: row A rotated the other way at %354": (
        465,
        ROTATE.format(3, 0, 1, 2, 7, 4, 5, 6),
        ROTATE.format(1, 2, 3, 0, 5, 6, 7, 4),
        {"FillBlockWithXor": None, "FillSegment": "cut_store: the target doesn't store what its slice returns"},
    ),
    "argon2_fill_segment_avx512f, second loop, in the region: two lanes of an output swapped at %599": (
        726,
        ROTATE.format(0, 1, 4, 5, 8, 9, 12, 13),
        ROTATE.format(1, 0, 4, 5, 8, 9, 12, 13),
        {"FillBlockWithXor": None, "FillSegment": "cut_store: the target doesn't store what its slice returns"},
    ),
}

failed = False


def say(ok: bool, what: str, detail: str = "") -> None:
    global failed
    failed = failed or not ok
    print(f"{'ok   ' if ok else 'FAIL '} {what}")
    if detail and not ok:
        print(detail[:3000])


def run(*args: object, env: dict[str, str]) -> tuple[int, str, str]:
    """Runs a command from the repository's root, under `time`. Returns its exit code, what it said, and its time and
    peak memory."""
    with tempfile.NamedTemporaryFile("r") as used:
        r = subprocess.run(
            ["/usr/bin/env", "time", "-f", "%e s, %M kB", "-o", used.name, *[str(a) for a in args]],
            capture_output=True,
            text=True,
            cwd=ROOT,
            env=env,
            check=False,
        )
        lines = used.read().strip().splitlines()
    return r.returncode, r.stdout + r.stderr, lines[-1] if lines else "?"


def lean(file: Path, env: dict[str, str], *options: str, olean: bool = True) -> tuple[int, str, str]:
    out = ["-o", file.with_suffix(".olean")] if olean else []
    return run("timeout", "900", "lean", "-M", "8000", "-R", file.parent, *options, *out, file, env=env)


def translate(tool: Path, ll: Path, module: str, where: Path, env: dict[str, str], *options: str) -> None:
    code, said, _ = run(tool, ll, "-o", where / f"{module}.lean", "--namespace", module, *options, env=env)
    if code != 0:
        sys.exit(f"ir-lean {ll}: exit {code}\n{said[-2000:]}")
    code, said, used = lean(where / f"{module}.lean", env)
    if code != 0:
        sys.exit(f"lean {module}.lean: exit {code}\n{said[-2000:]}")
    print(f"      {module}: translated and compiled, {used}")


def slice_theorems(region: dict, n: int) -> str:
    """The slices' theorems, as prototypes/argon2-rotate/prove.py states them."""
    params = " ".join("v" + p[1:] for p in region["params"])
    lines = ["import Rotate", f"import R{n}Src", f"import R{n}Tgt", "", "open IRLean Argon2Rotate", ""]
    outputs = region["outputs"]
    for k, o in enumerate(outputs):
        name = f"r{n}_o{k}"
        lines += [
            f"/-- {o} of region {n}: with row A rotated, it's what rotating row B gives. -/",
            f"theorem {name}_same ({params} : Vec 8 64) :",
            f"    R{n}Tgt.{name}_tgt {params} = R{n}Src.{name}_src {params} := by",
            f"  rotate_slice R{n}Tgt.{name}_tgt R{n}Src.{name}_src R{n}Tgt.{name}_tgt.step R{n}Src.{name}_src.step",
            "",
        ]
    return "\n".join(lines + [f"#print axioms r{n}_o{k}_same" for k in range(len(outputs))]) + "\n"


def generate(work: Path, pilot: Path, fn: str, module: str, callees: list[str]) -> str:
    """The function's proof, from the baseline and the regions' index. The candidate isn't read."""
    r = subprocess.run(
        [
            sys.executable,
            HERE / "gen.py",
            work / "Base.lean",
            pilot / "candidate.base.pic.ll",
            pilot / "regions" / "regions.json",
            fn,
            module,
            HERE / f"{fn}.main.lean",
            *callees,
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if r.returncode != 0:
        sys.exit(f"gen.py {fn}: {r.stderr[-2000:]}")
    return r.stdout


def main(pilot: Path, tool: Path, lib: Path, write: bool) -> int:
    work = Path(tempfile.mkdtemp(prefix="argon2-whole-"))
    env = {**os.environ, "LEAN_PATH": f"{work}:{lib}"}
    try:
        print(f"work: {work}")
        translate(tool, pilot / "candidate.base.pic.ll", "Base", work, env, "--no-code")
        translate(tool, pilot / "candidate.pic.ll", "Cand", work, env, "--no-code")
        for name in ("Rotate.lean", "Whole.lean"):
            shutil.copy(HERE / name, work)
            code, said, used = lean(work / name, env, "-DwarningAsError=true")
            say(code == 0, f"{name}: compiles with warnings as errors, {used}", said)
        regions = json.loads((pilot / "regions" / "regions.json").read_text())
        for region in regions:
            n = region["region"]
            translate(tool, pilot / "regions" / f"r{n}.src.ll", f"R{n}Src", work, env)
            translate(tool, pilot / "regions" / f"r{n}.tgt.ll", f"R{n}Tgt", work, env)
            (work / f"T{n}.lean").write_text(slice_theorems(region, n))
            code, said, used = lean(work / f"T{n}.lean", env, "-DwarningAsError=true")
            axioms = set(re.findall(r"depends on axioms: \[(.*?)\]", said))
            count = len(region["outputs"])
            say(
                code == 0 and said.count("depends on axioms") == count and axioms == {AXIOMS},
                f"region {n}'s slices: {count} theorems on [{AXIOMS}], {used}",
                said,
            )
        proofs = {}
        for fn, module, callees in FUNCTIONS:
            proofs[module] = generate(work, pilot, fn, module, callees)
            (work / f"{module}.lean").write_text(proofs[module])
            code, said, used = lean(work / f"{module}.lean", env, "-DwarningAsError=true")
            axioms = re.findall(r"'(.*?)' depends on axioms: \[(.*?)\]", said)
            say(
                code == 0 and len(axioms) == 2 and all(a == AXIOMS for _, a in axioms),
                f"{fn}: {module}.lean, {len(proofs[module].splitlines())} lines, checks, {used}",
                said,
            )
            for theorem, on in axioms:
                print(f"      '{theorem}' depends on axioms: [{on}]")
            code, said, used = run("timeout", "900", "leanchecker", module, env=env)
            say(code == 0, f"{fn}: leanchecker replays {module}, {used}", said)
        if write:
            for module, text in proofs.items():
                (HERE / f"{module}.lean").write_text(text)
        # Wrong candidates. The proof files are the ones just checked, to the byte: gen.py never read the candidate. So
        # are the slices' theorems. Only `Cand` is another.
        source = (pilot / "candidate.pic.ll").read_text().splitlines(keepends=True)
        for k, (name, (line, old, new, expect)) in enumerate(MUTANTS.items()):
            where = work / f"mutant{k}"
            where.mkdir()
            if source[line - 1].count(old) != 1:
                sys.exit(f"mutant {name}: line {line} doesn't have its mask once")
            wrong = list(source)
            wrong[line - 1] = wrong[line - 1].replace(old, new)
            (where / "candidate.pic.ll").write_text("".join(wrong))
            wrong_env = {**env, "LEAN_PATH": f"{where}:{env['LEAN_PATH']}"}
            translate(tool, where / "candidate.pic.ll", "Cand", where, wrong_env, "--no-code")
            for fn, module, callees in FUNCTIONS:
                if module not in expect:
                    continue
                shutil.copy(work / f"{module}.lean", where)
                code, said, used = lean(where / f"{module}.lean", wrong_env, "-DwarningAsError=true")
                errors = re.findall(r"error: (.*)", said)
                want = expect[module]
                if want is None:
                    say(code == 0, f"mutant, {name}: {module}.lean still checks, as that function isn't changed", said)
                else:
                    say(
                        code != 0 and bool(errors) and all(want in e for e in errors) and not LIMIT.search(said),
                        f"mutant, {name}: {module}.lean stops, {used}: {errors[0] if errors else said[:200]}",
                        said,
                    )
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return 1 if failed else 0


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != "--write"]
    if len(args) != 3:
        sys.exit(__doc__)
    sys.exit(main(Path(args[0]).resolve(), Path(args[1]).resolve(), Path(args[2]).resolve(), "--write" in sys.argv))
