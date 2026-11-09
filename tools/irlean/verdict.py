"""The one place Python decides a verdict: that a claim is proved, certified or refuted, or that a check
caught something wrong. docs/trust.md#where-python-decides-a-verdict has the contract.

Lean's kernel checks proofs, but Python decides which file, which theorem and which verdict count, and that
has gone wrong: a crashed native check counted as catching a wrong rewrite, a slice that failed to compile
counted as a refutation, and a scorer counted cached results whose certificates were gone. So every tool and
test asks `decide`, and only `decide` grants one of the four. It grants one only on clean evidence: each
process it rests on ended on its own, with the exit code that means success, and no limit stopped it. Anything
else, a crash, a timeout, a memory cap, a non-zero exit, a missing file, a failed or skipped check, is
`unknown` if a limit could explain it and more time or memory might decide it, and `error` otherwise. Never
success.

What each claim needs, besides every one of `checks` passing and every one of `files` being there:

- proved: a module, which `lean` compiled, `replay` (leanchecker) replayed, and `axioms` passed the audit; or
  `upstream`, a checker's process and the record it printed, saying `proved`.
- certified: at least one of `files`, the evidence it's bound to, and one of: a module, as for proved;
  `cached`, a verdict this checker stored for exactly these files and tools; or `upstream` saying `bound` or
  `proved`.
- refuted: a module, as for proved, of a theorem that the claim is false; `kernel`, the kernel accepting such
  a theorem inside the Lean process `lean`; `evaluated`, the model's compiled code, run by `lean`, finding the
  claim false at an input; or `upstream` saying `counterexample`. For `kernel` and `evaluated`, `lean` has to
  have ended cleanly too.
- caught: `step`, a check that has to fail on wrong code, ending on its own with `found_exit`, and a `finding`
  of its own: what it found, which isn't a resource limit.

The caller still says which file, theorem and finding are the ones that matter. What `decide` makes sure of is
that no process it rests on crashed, ran out of something or failed, and that nothing it needs is missing.
"""

from __future__ import annotations

import signal
from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any

from . import lean as lean_
from . import schemas


class Verdict(StrEnum):
    PROVED = "proved"
    CERTIFIED = "certified"
    REFUTED = "refuted"
    CAUGHT = "caught"
    # A limit stopped something it rests on. More time or memory might decide it.
    UNKNOWN = "unknown"
    # Anything else.
    ERROR = "error"


CLAIMS = (Verdict.PROVED, Verdict.CERTIFIED, Verdict.REFUTED, Verdict.CAUGHT)

# What a checker's record says when it grants each claim: its schema, the status it says, and the exit code it
# ends with. A record is only read if its process ended with that code.
UPSTREAM: dict[Verdict, tuple[tuple[str, str, int], ...]] = {
    Verdict.PROVED: ((schemas.VERIFY, "proved", 0),),
    Verdict.CERTIFIED: ((schemas.BINDING_VERDICT, "bound", 0), (schemas.VERIFY, "proved", 0)),
    Verdict.REFUTED: ((schemas.VERIFY, "counterexample", 2), (schemas.PROOFTEST, "counterexample", 2)),
    Verdict.CAUGHT: (),
}


@dataclass(frozen=True)
class Step:
    """How one process a verdict rests on ended."""

    name: str
    # Its exit code, minus the signal that killed it, or None if it didn't run or never ended.
    exit: int | None
    # A limit its runner enforced and that stopped it, such as `time_limit`.
    limit: str | None = None
    # What it printed, both streams, which Lean's own limit messages are read from.
    output: str = ""

    @classmethod
    def of(cls, name: str, ran: Any) -> Step:
        """From an `irlean.proc.Ran`."""
        return cls(name, ran.exit, ran.limit, ran.output)


@dataclass(frozen=True)
class Evidence:
    """What a verdict rests on. Each field is optional; `decide` says which a claim needs."""

    # The Lean process that compiled the theorem, or for `kernel` and `evaluated`, the one that answered.
    lean: Step | None = None
    # leanchecker, replaying the theorem's modules through the kernel.
    replay: Step | None = None
    # The axiom audit: tests/check_axioms.lean's process, or the answer of one that applied its policy.
    axioms: Step | bool | None = None
    # The answer of a kernel check made inside `lean`: True if it accepted the theorem.
    kernel: bool | None = None
    # The model's compiled code at an input: True if it found the claim false there.
    evaluated: bool | None = None
    # A stored verdict of this checker for exactly these files and tools.
    cached: bool = False
    # Another checker's process and the record it printed, whose verdict this one rests on.
    upstream: tuple[Step, Any] | None = None
    # For caught: the check that has to fail on wrong code, the exit code that says it found something, and
    # what it found.
    step: Step | None = None
    found_exit: int = 1
    finding: str | None = None
    # Each file the verdict is about, and whether it's there, as recorded.
    files: Mapping[str, bool] = field(default_factory=dict)
    # Each other check the verdict needs, and whether it passed. None is not run.
    checks: Mapping[str, bool | None] = field(default_factory=dict)


@dataclass(frozen=True)
class Decision:
    verdict: Verdict
    # A stable code for why.
    reason: str
    detail: str = ""

    @property
    def granted(self) -> bool:
        return self.verdict in CLAIMS


def _code(value: Any) -> int | None:
    """`value` if it's exactly an int, as an exit code is. In Python, `False == 0`."""
    return value if type(value) is int else None


def _limit(step: Step, read_output: bool) -> str | None:
    """The limit that stopped `step`, if one did: its runner's, SIGKILL, which is how a cap or the OOM killer
    stops a process, or, if `read_output` and it failed, one Lean reported."""
    if step.limit is not None:
        return str(step.limit)
    code = _code(step.exit)
    if code is None or code == 0:
        return None
    if code in (-signal.SIGKILL, 128 + signal.SIGKILL):
        return "killed"
    if read_output and code > 0:
        return lean_.limit_of(step.output) or ("resource_limit" if lean_.is_limit(step.output) else None)
    return None


def _ended(step: Step | None, want: int = 0) -> str | None:
    """Why `step` didn't end on its own with `want`, or None if it did."""
    if step is None or step.exit is None:
        return "didn't run"
    if _code(step.exit) is None:
        return f"ended with {step.exit!r}, which isn't an exit code"
    if step.limit is not None:
        return f"stopped at {step.limit}"
    if step.exit < 0:
        return f"died of signal {-step.exit}"
    if step.exit != want:
        return f"exited with {step.exit}, not {want}"
    return None


def _module(e: Evidence) -> str | None:
    """Why the evidence isn't a checked module, or None if it is."""
    for what, step in (("lean", e.lean), ("leanchecker", e.replay)):
        if why := _ended(step):
            return f"{what} {why}"
    if isinstance(e.axioms, Step):
        if why := _ended(e.axioms):
            return f"the axiom audit {why}"
    elif e.axioms is not True:
        return "the axiom audit didn't run" if e.axioms is None else "the axiom audit failed"
    return None


def _upstream(claim: Verdict, step: Step, record: Any) -> str | None:
    """Why a checker's process and record don't grant `claim`, or None if they do: the record is of a schema
    that grants it, says the status that does, and says the exit code its process ended with."""
    if not isinstance(record, dict):
        return "its record isn't a JSON object"
    for schema, status, code in UPSTREAM[claim]:
        if record.get("schema") == schema and record.get("status") == status:
            if why := _ended(step, code):
                return f"{step.name} {why}"
            if _code(record.get("exit_code")) != code:
                return f"its record says exit code {record.get('exit_code')!r}, not {code}"
            return None
    said = f"{record.get('schema')!r} says {record.get('status')!r}"
    return f"{step.name}'s record {said}, which doesn't grant {claim}"


def decide(claim: Verdict | str, e: Evidence) -> Decision:
    """Whether `e` grants `claim`: the claim, if it does, and otherwise `unknown` or `error`, with why. In
    order:

    1. A limit that stopped any process it rests on: `unknown`. A process killed by SIGKILL counts, as a cap
       or the OOM killer stops one that way, and so does a Lean limit in the output of a Lean process that
       failed.
    2. A file that isn't there, or a check that failed or didn't run: `error`. A certificate needs at least
       one file.
    3. The claim's own evidence, as the module's table says. Anything short of it: `error`."""
    if claim not in [str(c) for c in CLAIMS]:
        raise ValueError(f"{claim!r} isn't a claim: one of {', '.join(CLAIMS)}")
    claim = Verdict(claim)
    steps = [(s, True) for s in (e.lean, e.replay, e.axioms) if isinstance(s, Step)]
    steps += [(s, False) for s in (e.upstream[0] if e.upstream else None, e.step) if s is not None]
    for step, read_output in steps:
        if limit := _limit(step, read_output):
            return Decision(Verdict.UNKNOWN, "limit", f"{step.name}: {limit}")
    missing = sorted(name for name, there in e.files.items() if there is not True)
    if missing:
        return Decision(Verdict.ERROR, "missing_file", f"not there as recorded: {', '.join(missing)}")
    if claim is Verdict.CERTIFIED and not e.files:
        return Decision(Verdict.ERROR, "unbound", "a certificate has to be about files, and none were given")
    unmet = sorted(name for name, passed in e.checks.items() if passed is not True)
    if unmet:
        return Decision(Verdict.ERROR, "check_failed", f"didn't pass: {', '.join(unmet)}")

    if claim is Verdict.CAUGHT:
        finding = (e.finding or "").strip()
        if why := _ended(e.step, e.found_exit):
            return Decision(Verdict.ERROR, "not_caught", f"{e.step.name if e.step else 'the check'} {why}")
        if not finding:
            return Decision(Verdict.ERROR, "no_finding", "it failed without saying what it found")
        if lean_.is_limit(finding):
            return Decision(Verdict.UNKNOWN, "limit", f"what it found is a limit: {finding[:200]}")
        return Decision(claim, "own_error", finding[:300])
    if e.upstream is not None:
        step, record = e.upstream
        if why := _upstream(claim, step, record):
            return Decision(Verdict.ERROR, "upstream", why)
        return Decision(claim, "upstream", f"{step.name} says {record['status']}")
    if claim is Verdict.CERTIFIED and e.cached is True:
        return Decision(claim, "cached", "a stored verdict for exactly these files and tools")
    if claim is Verdict.REFUTED and (e.kernel is True or e.evaluated is True):
        # What a process answered counts only if it then ended cleanly: one that crashed or was stopped after
        # answering says nothing it can be held to.
        if why := _ended(e.lean):
            return Decision(Verdict.ERROR, "unconfirmed", f"the process that answered {why}")
        if e.kernel is True:
            return Decision(claim, "kernel_refuted", "the kernel checked that the claim is false")
        return Decision(claim, "evaluation_refuted", "the model's compiled code finds the claim false")
    if why := _module(e):
        return Decision(Verdict.ERROR, "no_evidence", why)
    return Decision(claim, "kernel_checked", "compiled, replayed by leanchecker, and its axioms allowed")
