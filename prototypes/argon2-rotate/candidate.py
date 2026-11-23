#!/usr/bin/env python3
"""Builds the candidate docs/argon2.md measures: libsodium, at the kernel corpus's pin, with the Argon2
AVX-512 unit compiled from rotate-a.patch's header. A prototype, outside CI.

It copies a build of libsodium, as bench/kernels/profile.sh makes one, with `make V=1`'s output kept. Then,
for each of the two objects libtool compiled from the unit, the one the shared library links and the one the
static archive does:

1. Runs the build's own compile command on a copy of the unit beside the patched header, to IR.
2. Turns the IR into an object with `llc -O3`, in the object's place in the copy.

Then it has make link the libraries again, and says which functions of the unit's object changed. Two
functions of other units share a name with one of them, so it compares the unit's object, not the library.

usage: candidate.py SOURCE BUILD BUILD_LOG OUT
SOURCE is libsodium's source at the pin, `bench/kernels/kernels.py source libsodium`. OUT gets the tree, and
OUT.pic.ll and OUT.pie.ll, the two IRs, and OUT.base.pic.ll and OUT.base.pie.ll, clang's own for each object.
"""

import os
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
UNIT = "crypto_pwhash/argon2/argon2-fill-block-avx512f.c"
HEADER = "crypto_pwhash/argon2/blamka-round-avx512f.h"
OBJECT = "crypto_pwhash/argon2/.libs/libavx512f_la-argon2-fill-block-avx512f.o"
# Stock clang, as bench/kernels/profile.sh has it.
ENV = {
    **os.environ,
    "NIX_ENFORCE_NO_NATIVE": "0",
    "NIX_HARDENING_ENABLE": "",
    "CC": "clang",
    "CXX": "clang++",
}
ENV.pop("SOURCE_DATE_EPOCH", None)


def sh(*args: object, cwd: Path | None = None) -> str:
    r = subprocess.run([str(a) for a in args], capture_output=True, text=True, env=ENV, cwd=cwd, check=False)
    if r.returncode != 0:
        sys.exit(f"{' '.join(map(str, args))[:400]}\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
    return r.stdout


def disassembly(obj: Path, function: str) -> str:
    """A function's machine code, without addresses, so moving it isn't a change."""
    text = sh("objdump", "-d", "-r", "--no-show-raw-insn", "--no-addresses", f"--disassemble={function}", obj)
    return re.sub(r"-?0x[0-9a-f]+\(%rip\)", "D(%rip)", "\n".join(text.splitlines()[6:]))


def main(source: Path, build: Path, log: Path, out: Path) -> int:
    src = source / "src" / "libsodium"
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(build, out, symlinks=True)
    patched = out.with_name(out.name + "-src")
    shutil.rmtree(patched, ignore_errors=True)
    patched.mkdir()
    shutil.copy(src / UNIT, patched / "unit.c")
    shutil.copy(src / HEADER, patched / Path(HEADER).name)
    sh("patch", "-p5", "-d", patched, "-i", HERE / "rotate-a.patch")
    cwd = out / "src" / "libsodium"
    prefix = "libtool: compile:"
    compiles = [
        line[len(prefix) :]
        for line in log.read_text().splitlines()
        if line.startswith(prefix) and UNIT in line
    ]
    if len(compiles) != 2:
        sys.exit(f"{log} has {len(compiles)} compile commands for {UNIT}, not the two libtool makes")
    for command in compiles:
        args = [a for a in shlex.split(command) if a not in (">/dev/null", "2>&1")]
        at = args.index("-o")
        obj = args[at + 1]
        del args[at : at + 2]
        args.remove("-c")
        args = [a for a in args if not a.endswith(UNIT)]
        kind = "pic" if "/.libs/" in obj else "pie"
        ll = out.with_name(f"{out.name}.{kind}.ll")
        include = f"-I{src / Path(UNIT).parent}"
        # Clang's own IR for this object, from the same command: what regions.py compares with.
        emit = ("-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o")
        sh(*args, src / UNIT, *emit, out.with_name(f"{out.name}.base.{kind}.ll"), cwd=cwd)
        sh(
            *args,
            include,
            patched / "unit.c",
            "-S",
            "-emit-llvm",
            "-Xclang",
            "-emit-llvm-uselists",
            "-o",
            ll,
            cwd=cwd,
        )
        sh("opt", "-passes=verify", "-disable-output", ll)
        sh("llc", "-O3", "-relocation-model=pic", "-filetype=obj", ll, "-o", cwd / obj)
        print(f"replaced {obj} from {ll.name}")
    os.utime(cwd / "crypto_pwhash/argon2/libavx512f_la-argon2-fill-block-avx512f.lo")
    sh("make", "-C", cwd, "libsodium.la")
    before, after = build / "src" / "libsodium" / OBJECT, cwd / OBJECT
    names = sorted(
        {
            w[2]
            for line in sh("nm", "--defined-only", before).splitlines()
            if len(w := line.split()) == 3 and w[1] in "Tt"
        }
    )
    changed = [f for f in names if disassembly(before, f) != disassembly(after, f)]
    print(
        f"functions of {Path(OBJECT).name} that changed: {', '.join(changed) or 'none'}, "
        f"of {', '.join(names)}"
    )
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    sys.exit(main(*(Path(a).resolve() for a in sys.argv[1:])))
