"""What the model, IRLean, declares that Python needs to know: the reasons a run is undefined, `IRLean.UB`,
and the reasons the model stops without an answer, `IRLean.ModelStop`.

Every tool and test reads them here, and none keeps a copy. A copy goes stale: tests/verify_negative.py's list
of `IRLean.UB` missed `noProgress` and `noReturn` when #62 added them. `ub_reasons` and `model_stops` read
IRLean/Basic.lean, which needs no Lean, and `from_lean` asks Lean itself, which tests/irlean_test.py checks
they agree with, so the reading can't drift from what Lean sees either.
"""

from __future__ import annotations

import re
from functools import cache
from pathlib import Path

from . import ROOT, lean, proc

BASIC = ROOT / "IRLean" / "Basic.lean"
UB = "IRLean.UB"
MODEL_STOP = "IRLean.ModelStop"
CONSTRUCTOR = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", re.M)


def _code(text: str) -> str:
    """`text` without its comments, so nothing in a doc comment reads as a constructor."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def constructors(name: str, source: Path | None = None) -> tuple[str, ...]:
    """The constructors of the inductive type `name`, such as `IRLean.UB`, in the order IRLean/Basic.lean, or
    `source`, declares them. Raises ValueError if it isn't declared there, or has none."""
    short = name.removeprefix("IRLean.")
    text = _code((source or BASIC).read_text())
    m = re.search(rf"^inductive {re.escape(short)}\b[^\n]*\bwhere\b(.*?)(?=^\S|\Z)", text, re.M | re.S)
    if m is None:
        raise ValueError(f"{source or BASIC} doesn't declare inductive {short}")
    body = m.group(1).split("deriving", 1)[0]
    found = tuple(CONSTRUCTOR.findall(body))
    if not found:
        raise ValueError(f"{name} has no constructors in {source or BASIC}")
    return found


@cache
def ub_reasons() -> tuple[str, ...]:
    """Every reason a run is undefined: `IRLean.UB`'s constructors, in order."""
    return constructors(UB)


@cache
def model_stops() -> tuple[str, ...]:
    """Every reason the model stops without an answer: `IRLean.ModelStop`'s constructors, in order."""
    return constructors(MODEL_STOP)


QUERY = """import IRLean
open Lean in
#eval show CoreM Unit from do
  for n in [{names}] do
    let some (.inductInfo i) := (← getEnv).find? n | throwError "{{n}} isn't an inductive type"
    for c in i.ctors do
      IO.println s!"IRLEAN_CTOR {{n}} {{c.getString!}}"
"""


def from_lean(*names: str, memory_mb: int = 2000, timeout: float = 300) -> dict[str, tuple[str, ...]]:
    """The constructors of each of `names`, as Lean reads them from IRLean's built library, which `lake build`
    makes. Raises RuntimeError if Lean doesn't answer."""
    query = QUERY.format(names=", ".join(f"``{n}" for n in names))
    r = proc.run(lean.argv(memory_mb, "--stdin"), stdin=query, env=lean.env(), timeout=timeout)
    out: dict[str, list[str]] = {n: [] for n in names}
    for line in r.out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0] == "IRLEAN_CTOR" and parts[1] in out:
            out[parts[1]].append(parts[2])
    if not r.ok or not all(out.values()):
        raise RuntimeError(
            f"Lean didn't list {', '.join(names)}: exit {r.exit} {r.limit or ''} {r.output[-1000:]}"
        )
    return {n: tuple(c) for n, c in out.items()}
