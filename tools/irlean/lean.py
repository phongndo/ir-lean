"""Calling Lean: `lean`, `lake` and `leanchecker` with their limits, reading what Lean prints, and the axiom
audit.

Each Lean process gets a memory cap with `-M`, and 64 MB thread stacks with `-s`. Lean gives each thread a
stack of about 1 GiB, all of it committed, and bv_decide forks the Lean process to start its solver, so on a
machine with less RAM and swap than that commit, such as CI's runner, the fork can fail with ENOMEM. 64 MB is
plenty for the proofs here.

A Lean error saying it ran out of heartbeats, time, memory, stack, recursion depth, SAT solver time or `simp`
steps is a limit: the step might pass with more, so it never counts as the step failing on its own, or as
passing.
"""

from __future__ import annotations

import os
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from . import ROOT

LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
TOOLCHAIN_FILE = ROOT / "lean-toolchain"
AXIOM_AUDIT = ROOT / "tests" / "check_axioms.lean"
STACK_KB = 65536

# Each limit Lean reports, by the reason tools/verify.py gives for it, in the order it checks them.
LIMITS: list[tuple[str, re.Pattern[str]]] = [
    ("memory_limit", re.compile(r"excessive memory consumption|out of memory", re.I)),
    ("heartbeat_limit", re.compile(r"maximum number of heartbeats|\(deterministic\) timeout")),
    ("recursion_limit", re.compile(r"maximum recursion depth has been reached")),
    ("stack_limit", re.compile(r"deep recursion was detected|stack overflow", re.I)),
    ("solver_limit", re.compile(r"SAT solver timed out")),
    ("step_limit", re.compile(r"maximum number of steps exceeded")),
]
# Any of them, as one pattern, as tests/proofs.sh lists them.
LIMIT = re.compile(
    r"maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|"
    r"stack overflow|excessive memory|out of memory|SAT solver timed out|maximum number of steps",
    re.IGNORECASE,
)
# A message Lean prints, with where it is.
MESSAGE = re.compile(
    r"^(?P<file>.+?):(?P<line>\d+):(?P<column>\d+): "
    r"(?P<severity>error|warning|info)(?:\([^)]*\))?: (?P<text>.*)$"
)
# An error line, as `file:line:column: error`, with an optional kind after it.
ERROR = re.compile(r"^.*?:(\d+):(\d+): error")


def toolchain() -> str:
    """The toolchain lean-toolchain pins, as elan names it."""
    return TOOLCHAIN_FILE.read_text().strip()


def limit_of(text: str) -> str | None:
    """The first limit in `text`, by its reason in LIMITS, or None."""
    for reason, pattern in LIMITS:
        if pattern.search(text):
            return reason
    return None


def is_limit(text: str) -> bool:
    return LIMIT.search(text) is not None


@dataclass
class Message:
    severity: str
    file: str
    line: int
    column: int
    text: str


def messages(output: str) -> list[Message]:
    """Lean's errors, warnings and information in `output`, each with the lines that continue it."""
    found: list[Message] = []
    for line in output.splitlines():
        m = MESSAGE.match(line)
        if m:
            found.append(Message(m["severity"], m["file"], int(m["line"]), int(m["column"]), m["text"]))
        elif found and line.strip():
            found[-1].text += "\n" + line
    return found


def errors(output: str) -> list[str]:
    """The lines of `output` that are Lean errors."""
    return [line for line in output.splitlines() if ERROR.match(line)]


def lean_path(*dirs: str | os.PathLike[str], library: bool = True) -> str:
    """LEAN_PATH for modules in `dirs`, then IRLean's library."""
    return os.pathsep.join([*(os.fspath(d) for d in dirs), *([str(LIBRARY)] if library else [])])


def env(
    *dirs: str | os.PathLike[str],
    library: bool = True,
    base: Mapping[str, str] | None = None,
    pin: bool = False,
    **extra: str,
) -> dict[str, str]:
    """The environment for a Lean process reading modules from `dirs` and IRLean's library: `base`, by default
    this process's, with LEAN_PATH and `extra`. `pin` also names the pinned toolchain to elan, so the `lean`
    it runs
    is lean-toolchain's whatever directory it runs in."""
    out = dict(os.environ if base is None else base)
    if dirs or library:
        out["LEAN_PATH"] = lean_path(*dirs, library=library)
    if pin:
        out["ELAN_TOOLCHAIN"] = toolchain()
    out.update(extra)
    return out


def argv(
    memory_mb: int | str,
    *args: str | os.PathLike[str],
    lean: str = "lean",
    threads: int | None = None,
    stack_kb: int | None = STACK_KB,
) -> list[str]:
    """`lean` capped at `memory_mb`, with `threads` threads if given, and 64 MB thread stacks unless
    `stack_kb` is
    None."""
    out = [lean]
    if threads is not None:
        out.append(f"-j{threads}")
    out += ["-M", str(memory_mb)]
    if stack_kb is not None:
        out += ["-s", str(stack_kb)]
    return out + [os.fspath(a) for a in args]


def checker(*modules: str, leanchecker: str = "leanchecker") -> list[str]:
    """`leanchecker` replaying `modules` through the kernel. Lean code in a proof can add a declaration the
    kernel
    never checked, with `debug.skipKernelTC`, and only this notices."""
    return [leanchecker, *modules]


def audit_env(
    module: str,
    generated: str | None = None,
    theorems: str | None = None,
    base: Mapping[str, str] | None = None,
) -> dict[str, str]:
    """What tests/check_axioms.lean reads: the module to audit, and if given, the namespaces ir-lean generated
    and
    the lines of a theorem and the function it has to be about. Merged over `base`, if given."""
    out = dict(base or {})
    out["IRLEAN_CHECK_MODULE"] = module
    if generated is not None:
        out["IRLEAN_CHECK_GENERATED"] = generated
    if theorems is not None:
        out["IRLEAN_CHECK_THEOREMS"] = theorems
    return out


def audit_argv(memory_mb: int | str, lean: str = "lean", threads: int | None = None) -> list[str]:
    """tests/check_axioms.lean, which reads a module and everything it imports as data, and refuses any axiom
    but
    the standard three and the ones bv_decide adds, which it reruns, and any `implemented_by` or `extern`."""
    return argv(memory_mb, AXIOM_AUDIT, lean=lean, threads=threads)


def library_modules() -> list[Path]:
    """IRLean's compiled modules: `IRLean*.olean` and `IRLean/*.olean`, sorted."""
    return sorted(LIBRARY.glob("IRLean*.olean")) + sorted((LIBRARY / "IRLean").glob("*.olean"))
