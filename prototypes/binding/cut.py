#!/usr/bin/env python3
"""Replaces each call to a named function with a call that stops the model, and nothing else.

usage: cut.py IN.ll OUT.ll CALLEE...

`ir-lean` refuses a call to a function outside the module. A call to a declared `noreturn` function with no
result is the one it accepts, as `Outcome.stop .noReturnCall`. So each `%r = call T @callee(...)` becomes that
call, then `%r = add T 0, 0` to keep the IR well formed: the add never runs, since the model has stopped. The
arguments aren't evaluated again, so nothing that came before the call changes. Every other line is copied
unchanged, and the script fails unless it replaced at least one call to each callee.

A theorem that the edited function returns `Outcome.ok` shows no path it covers reaches a cut call, so on
those paths the edited and the original function run the same instructions. That last step is an argument on
paper, not in Lean, and it's the one this prototype trusts: see README.md.
"""

import re
import sys
from pathlib import Path

STOP = "ir_lean_binding_outside"
CALL = re.compile(r"^  (%[\w.]+) = (?:tail )?call [^@]*?\b(i\d+) @([\w.]+)\(.*\)(?: #\d+)?$")


def main() -> int:
    if len(sys.argv) < 4:
        print(__doc__, file=sys.stderr)
        return 2
    src, out, callees = Path(sys.argv[1]), Path(sys.argv[2]), set(sys.argv[3:])
    cut = dict.fromkeys(callees, 0)
    result = []
    for line in src.read_text(encoding="utf-8").split("\n"):
        m = CALL.match(line)
        if m and m.group(3) in callees:
            name, ty, callee = m.groups()
            cut[callee] += 1
            result.append(f"  call void @{STOP}() #1000")
            result.append(f"  {name} = add {ty} 0, 0")
        else:
            result.append(line)
    missing = [c for c, n in cut.items() if n == 0]
    if missing:
        print(f"cut.py: no call to {', '.join(missing)}", file=sys.stderr)
        return 1
    result += [f"declare void @{STOP}() #1000", "attributes #1000 = { noreturn nounwind }", ""]
    out.write_text("\n".join(result), encoding="utf-8")
    for c, n in sorted(cut.items()):
        print(f"cut {n} call(s) to @{c}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
