#!/usr/bin/env python3
"""Runs each slice pair natively, on the processor, and compares them: testing, and not proof, but it doesn't
depend on the Lean model. Inputs are random bytes, with some runs where every byte is drawn from the extremes
(0, 15, 16, 127, 128, 255), which is where saturation and wrapping would show.

usage: native_check.py SLICES_DIR WORK_DIR [--runs N]
"""

import json
import re
import subprocess
import sys
from pathlib import Path

TYPE = re.compile(r"(<(\d+) x i(\d+)>|i(\d+)) (%[\w.]+)")


def found(m: re.Match[str] | None, what: str) -> re.Match[str]:
    """A match that has to be there."""
    if m is None:
        raise SystemExit(f"no {what}")
    return m


def size(t: str) -> int:
    m = re.match(r"<(\d+) x i(\d+)>", t)
    return int(m.group(1)) * int(m.group(2)) // 8 if m else int(t[1:]) // 8


def main() -> int:
    slices, work = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    runs = int(sys.argv[sys.argv.index("--runs") + 1]) if "--runs" in sys.argv else 200000
    work.mkdir(parents=True, exist_ok=True)
    index = json.loads((slices / "slices.json").read_text())
    objects, checks = [], []
    for entry in index:
        name = entry["name"]
        for kind in ("src", "tgt"):
            obj = work / f"{name}.{kind}.o"
            subprocess.run(
                [
                    "llc",
                    "-O2",
                    "-mcpu=znver5",
                    "-filetype=obj",
                    str(slices / f"{name}.{kind}.ll"),
                    "-o",
                    str(obj),
                ],
                check=True,
            )
            objects.append(str(obj))
        lines = (slices / f"{name}.src.ll").read_text().splitlines()
        define = next(line for line in lines if line.startswith("define"))
        ret = found(re.match(r"define (<\d+ x i\d+>)", define), "return type").group(1)
        params = [(m.group(1), m.group(5)) for m in TYPE.finditer(define.split("(", 1)[1])]
        lines = [f"define i32 @check_{name}(ptr %in) {{"]
        offset, args = 0, []
        for k, (t, _) in enumerate(params):
            lines.append(f"  %p{k} = getelementptr i8, ptr %in, i64 {offset}")
            lines.append(f"  %a{k} = load {t}, ptr %p{k}, align 1")
            args.append(f"{t} %a{k}")
            offset += size(t)
        n = int(found(re.match(r"<(\d+)", ret), "lanes").group(1))
        lines += [
            f"  %s = call {ret} @{name}_src({', '.join(args)})",
            f"  %t = call {ret} @{name}_tgt({', '.join(args)})",
            f"  %d = icmp ne {ret} %s, %t",
            f"  %any = call i1 @llvm.vector.reduce.or.v{n}i1(<{n} x i1> %d)",
            "  %r = zext i1 %any to i32",
            "  ret i32 %r",
            "}",
            f"declare {ret} @{name}_src({', '.join(t for t, _ in params)})",
            f"declare {ret} @{name}_tgt({', '.join(t for t, _ in params)})",
            f"declare i1 @llvm.vector.reduce.or.v{n}i1(<{n} x i1>)",
        ]
        ll = work / f"check_{name}.ll"
        ll.write_text('target triple = "x86_64-unknown-linux-gnu"\n' + "\n".join(lines) + "\n")
        obj = work / f"check_{name}.o"
        subprocess.run(["llc", "-O2", "-mcpu=znver5", "-filetype=obj", str(ll), "-o", str(obj)], check=True)
        objects.append(str(obj))
        checks.append((name, offset))
    driver = work / "driver.c"
    driver.write_text(
        "#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n"
        + "".join(f"int check_{n}(const unsigned char *);\n" for n, _ in checks)
        + "static uint64_t s = 88172645463325252ULL;\n"
        "static unsigned char byte(int extreme) {\n"
        "  static const unsigned char edge[] = {0, 15, 16, 127, 128, 255};\n"
        "  s ^= s << 13; s ^= s >> 7; s ^= s << 17;\n"
        "  return extreme ? edge[(s >> 32) % 6] : (unsigned char)s;\n}\n"
        "int main(void) {\n  static unsigned char in[4096];\n  int bad = 0;\n"
        + "".join(
            f"  for (long r = 0; r < {runs}; r++) {{ int e = r % 4 == 0;"
            f" for (int i = 0; i < {o}; i++) in[i] = byte(e);"
            f' if (check_{n}(in)) {{ printf("MISMATCH {n} run %ld\\n", r); bad++; break; }} }}\n'
            for n, o in checks
        )
        + f'  printf("%d of {len(checks)} slice pairs differ, {runs} inputs each\\n", bad);\n'
        + "  return bad != 0;\n}\n"
    )
    exe = work / "check"
    subprocess.run(["clang", "-O1", "-march=znver5", str(driver), *objects, "-o", str(exe)], check=True)
    return subprocess.run([str(exe)], check=False).returncode


if __name__ == "__main__":
    sys.exit(main())
