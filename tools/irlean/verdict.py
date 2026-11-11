"""The one place Python decides a verdict: that a run grants something a reader acts on as settled, such as
proved, certified, a counterexample, or a check that caught something wrong. docs/verdicts.md is the design,
and docs/trust.md#where-python-decides-a-verdict the contract.

Lean's kernel checks proofs, but Python decides which file, which theorem and which verdict count, and that
has gone wrong: a crashed native check counted as catching a wrong rewrite, a slice that failed to compile
counted as a refutation, and a scorer counted cached results whose certificates were gone. So every tool and
test asks `decide`, and only `decide` grants. It grants only on clean evidence: each process it rests on
ended on its own, with the exit code that means success, and no limit stopped it. Anything else, a crash, a
timeout, a memory cap, a non-zero exit, a missing file, a failed or skipped check, is `unknown` if a limit
could explain it and more time or memory might decide it, and `error` otherwise. Never success.

It's asked in two forms. A grant by name, from GRANTS, whose requirements are fixed there and not by the
caller: `decide("verify.proved", Evidence(...))`. And the old form, one of CLAIMS, whose caller picks the
checks it passes, which each tool keeps until it moves onto its grants. tests/verdict_test.py counts the old
form's calls, and the count can only fall. What each claim of the old form needs, besides every one of
`checks` passing and every one of `files` being there:

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

`limit_of` alone says which limit stopped a process, in either form. IRLEAN_DENY_ALL takes every grant away.
And evidence that isn't what its fields say can't be made: each raises TypeError where it's built.
"""

from __future__ import annotations

import collections
import functools
import itertools
import os
import re
import signal
import types
import typing
from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Annotated, Any

from . import lean as lean_
from . import schemas

# What a field's annotation adds to its type: an exit code, or minus the signal that ended a process; a count;
# and a name, which isn't empty.
Code = Annotated[int, lambda v: -64 <= v <= 255]
Count = Annotated[int, lambda v: v >= 0]
Name = Annotated[str, lambda v: v != ""]


def _fits(value: Any, hint: Any) -> bool:
    """Whether `value` is what `hint`, a field's annotation, says, by exact type: in Python, True is an int,
    "false" is truthy, and a str is a sequence of its letters."""
    origin, args = _parts(hint)
    if hint is Any:
        return True
    if origin is Annotated:
        return _fits(value, args[0]) and all(ok(value) for ok in args[1:])
    if origin in (typing.Union, types.UnionType):
        return any(_fits(value, a) for a in args)
    if origin is tuple:
        each = args[:1] * len(value) if type(value) is tuple and args[-1:] == (...,) else args
        return type(value) is tuple and len(each) == len(value) and all(map(_fits, value, each))
    if origin is Mapping:
        return isinstance(value, Mapping) and all(all(map(_fits, kv, args)) for kv in value.items())
    return type(value) is hint


@functools.cache
def _parts(hint: Any) -> tuple[Any, tuple[Any, ...]]:
    return typing.get_origin(hint), typing.get_args(hint)


@functools.cache
def _hints(kind: type) -> dict[str, Any]:
    return typing.get_type_hints(kind, include_extras=True)


def _made(self: Any) -> None:
    """Raises TypeError if a field of `self` isn't exactly what it's declared as, so `decide` never reads one
    that only looks right, such as a `whole` of "false", which is truthy."""
    for name, hint in _hints(type(self)).items():
        if not _fits(getattr(self, name), hint):
            raise TypeError(f"{type(self).__name__} can't have {name}={getattr(self, name)!r}"[:500])


class Verdict(StrEnum):
    PROVED = "proved"
    CERTIFIED = "certified"
    REFUTED = "refuted"
    CAUGHT = "caught"
    # A grant by name, from GRANTS. The Decision says which.
    GRANTED = "granted"
    # A limit stopped something it rests on, or more cases might decide it.
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
class Cases:
    """How each case of a run over many counts. A case is a Step named by its identity in the plan, whose exit
    says what it found. An exit none of these name is a case that failed."""

    # It met the hypotheses, and the property held.
    holds: tuple[Code, ...]
    # It didn't meet the hypotheses.
    discards: tuple[Code, ...] = ()
    # The model stopped where the property needs an answer.
    stops: tuple[Code, ...] = ()
    # The request's field that says how many cases have to hold, unless the plan is the whole domain.
    at_least: Name | None = None

    __post_init__ = _made


@dataclass(frozen=True)
class Grant:
    """An output a reader acts on as settled, and what it needs: each of `steps` ending on its own with exit
    0, each of `checks` exactly True, at least one file and each of them there if `files`, every case planned
    observed once if `cases`, and none of `excludes` granted on the same evidence."""

    # The status it's reported as, the exit code it ends with, and the schema of the record that says it.
    word: Name
    exit: Code
    schema: Name
    steps: tuple[str, ...] = ()
    checks: tuple[str, ...] = ()
    files: bool = False
    excludes: tuple[str, ...] = ()
    cases: Cases | None = None

    __post_init__ = _made


# The check that the files a grant's checks read didn't change while they ran.
UNCHANGED = "artifacts_unchanged"
# tools/verify.py's checks, which `proved` needs every one of. docs/verify.md.
VERIFY_CHECKS = (
    "request",
    "toolchain",
    "inputs",
    "ir_valid",
    "translate",
    "generate",
    "compile_generated",
    "compile_proof",
    "claim",
    "theorem",
    "mentions_target",
    "axioms",
    "kernel_replay",
    UNCHANGED,
)
# Each grant a tool asks for by name, and what it requires. tests/verdict/grants.json is a copy, so a change
# here is one a reviewer sees. Each tool's pull request in docs/verdicts.md's migration adds its own.
GRANTS: dict[str, Grant] = {
    "verify.proved": Grant(
        "proved",
        0,
        schemas.VERIFY,
        steps=("lean", "axioms", "replay"),
        checks=VERIFY_CHECKS,
        files=True,
        excludes=("verify.counterexample",),
    ),
    # Since #111: the process that evaluated the witness ended cleanly, its answer carried the nonce only it
    # was given, and the witness is a literal.
    "verify.counterexample": Grant(
        "counterexample",
        2,
        schemas.VERIFY,
        steps=("witnesses",),
        checks=("falsified", "nonce", "literal"),
        excludes=("verify.proved",),
    ),
}


@dataclass(frozen=True)
class Step:
    """How one process a verdict rests on ended."""

    name: str
    # Its exit code, minus the signal that killed it, or None if it didn't run or never ended.
    exit: Code | None
    # A limit its runner enforced and that stopped it, such as `time_limit`.
    limit: Name | None = None
    # What it printed, both streams, which Lean's own limit messages are read from.
    output: str = ""

    __post_init__ = _made

    @classmethod
    def of(cls, name: str, ran: Any) -> Step:
        """From an `irlean.proc.Ran`."""
        return cls(name, ran.exit, ran.limit, ran.output)


@dataclass(frozen=True)
class Plan:
    """What a run over many cases planned, from its request, before anything ran."""

    # Each case's identity.
    cases: tuple[str, ...]
    # How many have to hold, as the request's field its grant's Cases names says.
    at_least: Count = 0
    # Whether the cases are the whole domain, so how many hold doesn't matter.
    whole: bool = False

    __post_init__ = _made


@dataclass(frozen=True)
class Evidence:
    """What a verdict rests on. Each field is optional; `decide` says which each grant and claim needs."""

    # The Lean process that compiled the theorem, or for `kernel` and `evaluated`, the one that answered.
    lean: Step | None = None
    # leanchecker, replaying the theorem's modules through the kernel.
    replay: Step | None = None
    # The axiom audit: tests/check_axioms.lean's process, or for a claim, the answer of one that applied its
    # policy.
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
    found_exit: Code = 1
    finding: str | None = None
    # Each file the verdict is about, and whether it's there, as recorded.
    files: Mapping[str, bool] = field(default_factory=dict)
    # Each other check the verdict needs, and whether it passed. None is not run.
    checks: Mapping[str, bool | None] = field(default_factory=dict)
    # For a grant: the processes it rests on besides `lean`, `replay`, `axioms` and `step`, by the names its
    # grant gives them.
    steps: Mapping[str, Step] = field(default_factory=dict)
    # For a run over many cases: what it planned, and each case it observed, as a Step named by the case, in
    # the order observed and unfiltered.
    plan: Plan | None = None
    cases: tuple[Step, ...] = ()

    def __post_init__(self) -> None:
        for name in ("files", "checks", "steps"):
            # A copy no caller holds, so what's checked here is what `decide` reads.
            if isinstance(value := getattr(self, name), Mapping):
                object.__setattr__(self, name, types.MappingProxyType(dict(value)))
        _made(self)


@dataclass(frozen=True)
class Decision:
    verdict: Verdict
    # A stable code for why.
    reason: str
    detail: str = ""
    # The grant's name, if it was asked for by name.
    grant: str = ""

    __post_init__ = _made

    @property
    def granted(self) -> bool:
        return self.verdict in CLAIMS or self.verdict is Verdict.GRANTED


# What `timeout` exits with when the time runs out.
TIMEOUT_EXIT = 124
# Lean's runtime stopping at a limit outside any message: its memory exception, its panic when it can't
# allocate, and its stack guard.
RUNTIME = re.compile(
    r"^(?:libc\+\+abi: terminating due to uncaught exception of type lean::memory_exception"
    r"|INTERNAL PANIC: out of memory|(?P<stack>Stack overflow detected))",
    re.M,
)
# Where an error starts: as Lean prints one, with where it is; as lake prints one, without; and as an
# exception leanchecker didn't catch.
ERROR_START = re.compile(r"^(?:.+?:\d+:\d+: error(?:\([^)]*\))?|error|uncaught exception): ")
# The environment variable that takes every grant away.
DENY_ALL = "IRLEAN_DENY_ALL"


def _code(value: Any) -> int | None:
    """`value` if it's exactly an int, as an exit code is. In Python, `False == 0`."""
    return value if type(value) is int else None


def _first_error(output: str) -> str | None:
    """The first error in `output`, with the lines that continue it, or None."""
    lines = output.splitlines()
    for i, line in enumerate(lines):
        if ERROR_START.match(line):
            rest = itertools.takewhile(
                lambda more: not (ERROR_START.match(more) or lean_.MESSAGE.match(more)), lines[i + 1 :]
            )
            return "\n".join([line, *rest])
    return None


def limit_of(step: Step) -> str | None:
    """The limit that stopped `step`, if one did: its runner's; SIGKILL, from a signal or a shell's 137, which
    is how a cap or the OOM killer stops a process; `timeout`'s 124; Lean's memory exception, panic or stack
    guard; or a limit in its first error, by irlean.lean.LIMITS. The first error decides, since what fails
    after a limit often fails because of it. A process that exited 0 wasn't stopped, whatever it printed."""
    if step.limit is not None:
        return str(step.limit)
    code = _code(step.exit)
    if code is None or code == 0:
        return None
    if code in (-signal.SIGKILL, 128 + signal.SIGKILL):
        return "killed"
    if code == TIMEOUT_EXIT:
        return "time_limit"
    if runtime := RUNTIME.search(step.output):
        return "stack_limit" if runtime["stack"] else "memory_limit"
    said = _first_error(step.output)
    return lean_.limit_of(said) if said else None


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


def _denied() -> bool:
    return os.environ.get(DENY_ALL, "") not in ("", "0")


def decide(name: Verdict | str, e: Evidence) -> Decision:
    """Whether `e` grants `name`: a grant in GRANTS, or, in the old form, one of CLAIMS. The grant if it does,
    and otherwise `unknown` or `error`, with why. With IRLEAN_DENY_ALL set to anything but 0, nothing is
    granted: what would have been is `error`, `denied`."""
    if isinstance(name, str) and not isinstance(name, Verdict) and name in GRANTS:
        decision = _grant(name, e)
    else:
        decision = _claim(name, e)
    if decision.granted and _denied():
        return Decision(Verdict.ERROR, "denied", f"{DENY_ALL} is set, and it would have granted {name}")
    return decision


# Grants by name


def _required(e: Evidence, name: str) -> Any:
    """The step a grant names `name`: one of Evidence's own, or one of its `steps`."""
    own = {"lean": e.lean, "replay": e.replay, "axioms": e.axioms, "step": e.step}
    return own[name] if name in own else e.steps.get(name)


def _crashed(step: Step) -> bool:
    """Whether `step`, which no limit stopped, crashed: it ended with something that isn't an exit code, of a
    signal, or with an exit of 128 or more."""
    code = _code(step.exit)
    return code is None or code < 0 or code >= 128


def _listed(name: str) -> set[str]:
    """The checks evidence for `name` can have: its own, and those of each grant it excludes, which the same
    evidence is asked for."""
    grant = GRANTS[name]
    return {*grant.checks, *(c for other in grant.excludes for c in GRANTS[other].checks)}


def _incomplete(planned: tuple[str, ...], observed: list[str]) -> str | None:
    """What's wrong with the cases observed against those planned, or None if each was observed once."""
    plan, times = collections.Counter(planned), collections.Counter(observed)
    problems = {
        "planned twice": sorted(c for c, n in plan.items() if n > 1),
        "not observed": [c for c in plan if c not in times],
        "observed twice": sorted(c for c, n in times.items() if n > 1),
        "not planned": sorted(c for c in times if c not in plan),
    }
    said = "; ".join(f"{what}: {', '.join(cases)}" for what, cases in problems.items() if cases)
    return said[:500] or None


def _grant(name: str, e: Evidence, excluding: bool = True) -> Decision:
    """`decide` for a grant by name, in this order: a limit on any step or case it rests on, `unknown`; a
    crash, `error`; something it requires absent, or a check it doesn't list, `error`, `internal_error`; the
    plan against the cases, `error`, `incomplete`; each requirement that isn't clean, `error`, as its own
    reason; a model stop, `unknown`; too few cases that hold, unless the plan is the whole domain, `unknown`;
    none that hold, `error`; and a grant it excludes that the same evidence grants, `error`,
    `contradiction`."""
    grant = GRANTS[name]
    steps = [(r, _required(e, r)) for r in grant.steps]
    cases = list(e.cases) if grant.cases else []
    ran = [s for _, s in steps if isinstance(s, Step)] + [c for c in cases if isinstance(c, Step)]
    for step in ran:
        if limit := limit_of(step):
            return Decision(Verdict.UNKNOWN, limit, f"{step.name} stopped at {limit}")
    for step in ran:
        if step.exit is not None and _crashed(step):
            return Decision(Verdict.ERROR, "tool_failed", f"{step.name} {_ended(step)}")

    absent = [r for r, s in steps if not isinstance(s, Step) or s.exit is None]
    absent += [c for c in grant.checks if e.checks.get(c) is None]
    absent += [f"{c}, which {name} doesn't list" for c in e.checks if c not in _listed(name)]
    if grant.files and not e.files:
        absent.append("files")
    if grant.cases:
        absent += [f"case {c!r}" for c in cases if not isinstance(c, Step) or c.exit is None]
        if not isinstance(e.plan, Plan):
            absent.append("a plan")
        elif grant.cases.at_least and (_code(e.plan.at_least) is None or e.plan.at_least < 1):
            absent.append(grant.cases.at_least)
    if absent:
        return Decision(Verdict.ERROR, "internal_error", f"absent: {', '.join(absent)}"[:500])
    if grant.cases:
        assert isinstance(e.plan, Plan)
        if not e.plan.cases:
            return Decision(Verdict.UNKNOWN, "nothing_planned", "the plan has no cases")
        if why := _incomplete(tuple(e.plan.cases), [c.name for c in cases]):
            return Decision(Verdict.ERROR, "incomplete", why)

    if UNCHANGED in grant.checks and e.checks[UNCHANGED] is not True:
        return Decision(Verdict.ERROR, "artifacts_modified", "files its checks read changed while they ran")
    for r, step in steps:
        if why := _ended(step):
            return Decision(Verdict.ERROR, r, f"{step.name} {why}")
    for c in grant.checks:
        if e.checks[c] is not True:
            return Decision(Verdict.ERROR, c, f"{c} is {e.checks[c]!r}, not True")
    if grant.files and (gone := sorted(f for f, there in e.files.items() if there is not True)):
        return Decision(Verdict.ERROR, "missing_file", f"not there as recorded: {', '.join(gone)}"[:500])
    reason, detail = "clean", f"each of its {len(steps)} steps and {len(grant.checks)} checks"
    if grant.cases:
        assert isinstance(e.plan, Plan)
        named = {*grant.cases.holds, *grant.cases.discards, *grant.cases.stops}
        if failed := [c.name for c in cases if c.exit not in named]:
            return Decision(Verdict.ERROR, "case_failed", f"failed: {', '.join(failed)}"[:500])
        if stopped := [c.name for c in cases if c.exit in grant.cases.stops]:
            return Decision(
                Verdict.UNKNOWN, "model_stopped", f"the model stopped: {', '.join(stopped)}"[:500]
            )
        held = sum(c.exit in grant.cases.holds for c in cases)
        if not e.plan.whole and grant.cases.at_least and held < e.plan.at_least:
            why = f"{held} of {len(cases)} cases hold, and {grant.cases.at_least} is {e.plan.at_least}"
            return Decision(Verdict.UNKNOWN, "too_few_satisfying", why)
        if held == 0:
            return Decision(Verdict.ERROR, "vacuous", f"none of {len(cases)} cases met the hypotheses")
        reason = "exhaustive" if e.plan.whole else "sampled"
        detail = f"{held} of {len(cases)} cases hold, and none failed"
    if excluding:
        for other in grant.excludes:
            if _grant(other, e, excluding=False).granted:
                return Decision(Verdict.ERROR, "contradiction", f"the same evidence grants {other}")
    return Decision(Verdict.GRANTED, reason, detail, grant=name)


# The old form: a claim


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


def _claim(claim: Verdict | str, e: Evidence) -> Decision:
    """`decide` for a claim, in order:

    1. A limit that stopped any process it rests on, by `limit_of`: `unknown`.
    2. A file that isn't there, or a check that failed or didn't run: `error`. A certificate needs at least
       one file.
    3. The claim's own evidence, as the module's docstring says. Anything short of it: `error`."""
    if claim not in [str(c) for c in CLAIMS]:
        raise ValueError(f"{claim!r} isn't a claim, one of {', '.join(CLAIMS)}, or a grant in GRANTS")
    claim = Verdict(claim)
    for step in (e.lean, e.replay, e.axioms, e.upstream[0] if e.upstream else None, e.step):
        if isinstance(step, Step) and (limit := limit_of(step)):
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
        if lean_.limit_of(finding):
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
