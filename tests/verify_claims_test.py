#!/usr/bin/env python3
"""BIND-03's acceptance: tools/verify_claims.py accepts every claim the scorer accepts, and refuses forged
ones.

The scorer's claims are the 87 functions of LLVM's own code that tests/llvm.py proves, from
tests/llvm/targets.toml, with the theorem each names. This builds one piece of evidence holding all of them,
and the verifier has to replay it. So does every control tools/verify.py, the scorer's checker, certifies in
tests/verification_negative, and tools/verify.py has to prove each of those here too, so the two are seen to
agree on the same inputs.

Then each forged claim breaks one thing about a good one, and has to be refused for that reason, never
another: a wrong statement, stale anchors, an extra axiom, `sorry`, a theorem added past the kernel, and the
rest in CASES. Claims that can't be complete, or whose coverage nothing can decide yet, are refused before any
replay.

And its guard, docs/verdicts.md's test 8: a replay is `replayed` only with every check of REPLAYED passed
once, over every module it planned, and a claim `verified` only with each evidence file's replay so. A check
skipped, passed twice or over a module short is `error`, `incomplete`; IRLEAN_DENY_ALL takes every grant away,
with a non-zero exit; and files changed while the evidence's code ran are `error`, exit 5.

usage: tests/verify_claims_test.py [--tier static|live|all] [--only NAME ...] [--jobs N]

`static` needs only Python. `live` needs the dev shell, build/ir-lean and `lake build IRLean`.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import re
import shutil
import sys
import tempfile
import time
import tomllib
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import verify_claims as vc  # noqa: E402
from irlean import hashing, proc  # noqa: E402

TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
WORK = ROOT / "build" / "verify-claims-test"
DENY_ALL = "IRLEAN_DENY_ALL"


def sha(path: Path) -> str:
    return hashing.sha256_file(path)


def unit(config: dict[str, Any], target: dict[str, Any]) -> dict[str, Any]:
    flags = config["flags"][target["flags"]]
    return {
        "source": target["source"],
        "source_in": "repo" if target.get("wrapper") else "llvm-project",
        "language": "c++" if flags.get("cxx") else "c",
        "flags": [*flags.get("args", []), *target.get("args", [])],
        "include": flags.get("include", []),
        "local_include": flags.get("local_include", []),
        "llvm_config": bool(flags.get("llvm_config")),
        "extract": [],
        "namespace": target["module"],
        "translate": ["--no-code"],
        "anchors": {},
        "repo_files": {},
        "ir_sha256": "",
        "lean_sha256": "",
    }


def corpus(only: list[str] | None = None, model_proofs: bool = True) -> dict[str, Any]:
    """Evidence, to be recorded, for every function tests/llvm.py proves, or the targets in `only`. With
    `model_proofs`, a statement may use its proof module's definitions, as tests/llvm.py's do."""
    config = tomllib.loads(TARGETS.read_text())
    targets = [t for t in config["target"] if not only or t["module"] in only]
    files = dict.fromkeys(config["support"], "") | {t["proof"]: "" for t in targets}
    theorems = [
        {"module": t["proof"], "name": d["theorem"], "about": [d.get("symbol", f)], "statement": "",
         "statement_sha256": ""}
        for t in targets
        for f, d in t["functions"].items()
    ]  # fmt: skip
    return {
        "schema": vc.EVIDENCE_SCHEMA,
        "llvm": {k: config["project"][k] for k in ("tag", "commit", "nix_hash")},
        "lean_version": "",
        "units": [unit(config, t) for t in targets],
        # tests/llvm.py reads each statement with its proof module's definitions, such as LEB128's `Encoded`.
        "lean": {
            "root": "tests/llvm",
            "files": files,
            "model": list(files) if model_proofs else list(config["support"]),
        },
        "theorems": theorems,
        "cuts": [],
        "contexts": "all",
    }


# --- Static cases: claims refused before anything is replayed ---------------------------------------------


def claim(**over: Any) -> dict[str, Any]:
    c = {
        "item": "pass:instcombine",
        "dimension": "code-binding",
        "contexts": "all",
        "status": "complete",
        "evidence": [{"kind": "binding-check", "path": "tests/llvm_scope/coverage.json", "sha256": "0" * 64}],
        "anchors": {},
        "gaps": [],
    }
    return c | over


def static_cases() -> list[tuple[str, dict[str, Any], str]]:
    inv = json.loads(vc.INVENTORY.read_text())
    anchors = next(i for i in inv["items"] if i["id"] == "pass:instcombine")["anchors"]
    good_anchors = claim(anchors=anchors)
    return [
        ("partial", claim(status="partial", anchors=anchors), "not_complete"),
        ("admitted", claim(status="admitted", anchors=anchors), "not_complete"),
        ("some contexts", claim(contexts=["opt:default<O2>"], anchors=anchors), "contexts_uncovered"),
        ("gaps", claim(gaps=["vectors"], anchors=anchors), "gaps_listed"),
        (
            "translation validation",
            claim(dimension="translation-validation", anchors=anchors),
            "dimension_unverifiable",
        ),
        ("unknown pass", claim(item="pass:no-such-pass"), "claim_invalid"),
        ("all-input with no rewrite list", claim(dimension="all-input"), "coverage_undecidable"),
        ("composition", claim(dimension="composition"), "coverage_undecidable"),
        (
            "code binding, stale anchors",
            claim(anchors={**anchors, next(iter(anchors)): "0" * 64}),
            "stale_anchors",
        ),
        ("code binding, anchors left out", claim(anchors={}), "stale_anchors"),
        ("code binding with no closure", good_anchors, "coverage_undecidable"),
    ]


def run_static() -> list[str]:
    failures = []
    for name, c, want in static_cases():
        v = vc.decide_claim(c)
        ok = v["status"] == "refused" and v["reason"] == want
        print(f"{'ok  ' if ok else 'FAIL'} static: {name}: {v['status']} {v['reason']}")
        if not ok:
            failures.append(
                f"static {name}: wanted refused {want}, got {v['status']} {v['reason']}: {v['detail']}"
            )
    # A process that ran out of memory says nothing about the evidence: unknown, never refused. A fork that
    # fails with ENOMEM, as bv_decide's can on a CI runner, reads this way.
    enomem = "Proof.lean:1:1: error: resource exhausted (error code: 12, not enough memory)"
    ran = vc.Ran(["lean"], 1, "", enomem, False, 0.0)
    try:
        vc.need(ran, "proof_compile_failed", "lean Proof")
        got = "passed"
    except vc.Stop as stop:
        got = stop.status
    print(f"{'ok  ' if got == 'unknown' else 'FAIL'} static: a process out of memory is {got}")
    if got != "unknown":
        failures.append(f"a process out of memory is {got}, not unknown")
    # tests/llvm_scope.py asks this verifier, and only for a complete claim.
    sys.path.insert(0, str(ROOT / "tests"))
    import llvm_scope

    ok = llvm_scope.VERIFIERS.get("binding-check") is vc.check_claim
    print(
        f"{'ok  ' if ok else 'FAIL'} static: tests/llvm_scope.py asks this verifier for code-binding claims"
    )
    if not ok:
        failures.append("tests/llvm_scope.py's VERIFIERS doesn't use tools/verify_claims.py")
    return failures + run_guard()


# --- The guard: only a whole replay grants, docs/verdicts.md's test 8 ---------------------------------------

# The checks a replay needs, each passed exactly once, fixed here so that taking one off vc.REPLAYED fails.
REPLAYED = (
    "pin", "anchors", "ir_replay", "translation_replay", "compile_generated", "compile_evidence",
    "statements", "axioms", "kernel_replay", "unchanged",
)  # fmt: skip
# A plan of one generated module and two of the evidence's own, and what each check over modules has to cover.
PLAN = {"units": [{"namespace": "Gen"}], "lean": {"files": {"Kit": "", "Proof": ""}}}
WHOLE = {
    "compile_generated": ["Gen"],
    "compile_evidence": ["Kit", "Proof"],
    "kernel_replay": ["Gen", "Kit", "Proof"],
}
INCOMPLETE = ("error", "incomplete")


def replay_of(checks: Sequence[str] = REPLAYED, modules: dict[str, list[str]] = WHOLE) -> vc.Replay:
    """A replay of PLAN that passed `checks` and covered `modules`, with no process run."""
    nowhere = Path("/nonexistent")
    t = vc.Tools(nowhere, nowhere, nowhere, nowhere, "", [])
    r = vc.Replay(copy.deepcopy(PLAN), t, nowhere, 1, 1, 1.0, False, copy.deepcopy(PLAN))
    for c in checks:
        r.passed(c)
    for step, done in modules.items():
        r.observed[step] += done
    return r


def outcome(f: Callable[[], Any], deny: str = "") -> tuple[str, str]:
    """The status and reason `f` gives with IRLEAN_DENY_ALL set to `deny`, or the exception it raises."""
    try:
        with mock.patch.dict(os.environ, {DENY_ALL: deny}):
            v = f()
            v = v.verdict if isinstance(v, vc.Replayed) else v
    except vc.Stop as s:
        return s.status, s.reason
    except Exception as e:
        return "raised", type(e).__name__
    return v["status"], v["reason"]


def replayed(path: str) -> vc.Replayed:
    """A whole replay's result, for the evidence file `path`, asked with IRLEAN_DENY_ALL unset."""
    with mock.patch.dict(os.environ, {DENY_ALL: ""}):
        return vc.complete(replay_of(), "x", path=path)


def guard_cases() -> list[tuple[str, Callable[[], Any], str, tuple[str, str]]]:
    """(name, what's asked, IRLEAN_DENY_ALL, the status and reason it gives) for the guard's functions."""
    whole = ("replayed", "replayed")
    cases: list[tuple[str, Callable[[], Any], str, tuple[str, str]]] = [
        ("a whole replay", lambda: vc.complete(replay_of(), "x"), "", whole),
        ("a whole replay, IRLEAN_DENY_ALL=0", lambda: vc.complete(replay_of(), "x"), "0", whole),
        (
            "a whole replay, IRLEAN_DENY_ALL=1",
            lambda: vc.complete(replay_of(), "x"),
            "1",
            ("error", "denied"),
        ),
        ("a check no one lists", lambda: vc.complete(replay_of([*REPLAYED, "extra"]), "x"), "", INCOMPLETE),
    ]
    for c in REPLAYED:
        rest = [k for k in REPLAYED if k != c]
        cases.append((f"{c} left out", lambda rest=rest: vc.complete(replay_of(rest), "x"), "", INCOMPLETE))
        twice = [*REPLAYED, c]
        cases.append((f"{c} passed twice", lambda t=twice: vc.complete(replay_of(t), "x"), "", INCOMPLETE))
    for step, done in WHOLE.items():
        changed = [(f"{step} on a module not planned", WHOLE | {step: [*done, "Other"]})]
        for m in done:
            changed.append((f"{step} without {m}", WHOLE | {step: [k for k in done if k != m]}))
            changed.append((f"{step} on {m} twice", WHOLE | {step: [*done, m]}))
        for name, modules in changed:
            cases.append((name, lambda ms=modules: vc.complete(replay_of(modules=ms), "x"), "", INCOMPLETE))
    raised = ("raised", "ValueError")
    for word in ("replayed", "verified"):
        cases.append((f"verdict asked for {word}", lambda w=word: vc.verdict(w, w, "x"), "", raised))
    # A claim is verified only with each evidence file it plans replayed, each by complete.
    a, b, c, ab = replayed("a.json"), replayed("b.json"), replayed("c.json"), ["a.json", "b.json"]
    for name, results, planned, deny, want in [
        ("verified, each evidence file replayed", [b, a], ab, "", ("verified", "verified")),
        ("verified, IRLEAN_DENY_ALL=1", [a, b], ab, "1", ("error", "denied")),
        ("verified, an evidence file planned and not replayed", [a], ab, "", INCOMPLETE),
        ("verified, another file's replay in a planned one's place", [a, c], ab, "", INCOMPLETE),
        ("verified, one file's replay twice", [a, a], ab, "", INCOMPLETE),
        ("verified, a verdict saying replayed, not complete's result", [a, b.verdict], ab, "", INCOMPLETE),
        ("verified, no evidence", [], [], "", INCOMPLETE),
        ("verified, one refused", [vc.verdict("refused", "x", "y")], ["a.json"], "", INCOMPLETE),
    ]:  # fmt: skip
        cases.append((name, lambda r=results, p=planned: vc.verified(r, p, "x"), deny, want))
    return cases


def run_guard() -> list[str]:
    failures = []
    fixed = getattr(vc, "REPLAYED", None) == REPLAYED
    print(f"{'ok  ' if fixed else 'FAIL'} static: guard: REPLAYED is the design's fixed list of checks")
    if not fixed:
        failures.append(f"guard: vc.REPLAYED is {getattr(vc, 'REPLAYED', None)}, not {REPLAYED}")
    for name, f, deny, want in guard_cases():
        got = outcome(f, deny)
        print(f"{'ok  ' if got == want else 'FAIL'} static: guard: {name}: {' '.join(got)}")
        if got != want:
            failures.append(f"guard {name}: wanted {' '.join(want)}, got {' '.join(got)}")
    return failures


# --- Live cases -------------------------------------------------------------------------------------------

ASHLDI3 = """import CrtAshldi3
import Kit

namespace Llvm

theorem ashldi3_correct (a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshldi3._ashldi3 (some a) (some b) =
      IRLean.Outcome.ok (some (a <<< b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtAshldi3._ashldi3
  all_goals llvm_close
"""

STATEMENT = """(a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshldi3._ashldi3 (some a) (some b) = IRLean.Outcome.ok (some (a <<< b))"""


def proof(body: str) -> str:
    return f"import CrtAshldi3\nimport Kit\nimport Lean\n\nnamespace Llvm\n\n{body}\n\nend Llvm\n"


# Each forged proof module stands in for tests/llvm/Ashldi3.lean, with its hash recorded, so only what it says
# can refuse it.
TACTICS = "  simp only [IRLean.Outcome.ok]\n  llvm_exec CrtAshldi3._ashldi3\n  all_goals llvm_close"
WEAKER = proof(f"theorem ashldi3_correct {STATEMENT.replace('64#32)', '1#32)')} := by\n{TACTICS}")
AXIOM = proof(f"axiom shifts {STATEMENT}\n\ntheorem ashldi3_correct {STATEMENT} := shifts a b h")
SORRY = proof(f"theorem ashldi3_correct {STATEMENT} := by sorry")
SKIPPED = proof(
    "open Lean Elab Command in\nset_option debug.skipKernelTC true in\n"
    "run_cmd liftCoreM <| addDecl <| .thmDecl {\n"
    "  name := `Llvm.oops, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n\n"
    f"theorem ashldi3_correct {STATEMENT} := oops.elim"
)
OWN_DEFINITION = proof(
    "def shifted (a : BitVec 64) (b : BitVec 32) : BitVec 64 := a <<< b\n\n"
    f"theorem ashldi3_correct {STATEMENT.replace('(a <<< b)', '(shifted a b)')} := by\n"
    "  simp only [IRLean.Outcome.ok, shifted]\n  llvm_exec CrtAshldi3._ashldi3\n  all_goals llvm_close"
)
# The proof defines the generated function's name itself, and imports nothing ir-lean generated.
NAMED_LIKE_TARGET = (
    "import Kit\n\nnamespace CrtAshldi3\n\n"
    "def _ashldi3 (a : Option (BitVec 64)) (b : Option (BitVec 32)) :\n"
    "    IRLean.Outcome (Option (BitVec 64)) :=\n"
    "  IRLean.Outcome.ok (match a, b with | some a, some b => some (a <<< b) | _, _ => none)\n\n"
    f"end CrtAshldi3\n\nnamespace Llvm\n\ntheorem ashldi3_correct {STATEMENT} := rfl\n\nend Llvm\n"
)
REWRITES_GENERATED = (
    ASHLDI3 + "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/CrtAshldi3.lean") "-- rewritten\\n"\n'
)
MAKES_INIT = (
    ASHLDI3 + "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/Shadow.olean") "x"\n'
)
SLEEPS = ASHLDI3 + "\n#eval IO.sleep 120000\n"


def edit_proof(text: str) -> Callable[[dict[str, Any], Path], None]:
    def edit(ev: dict[str, Any], lean_dir: Path) -> None:
        (lean_dir / "Ashldi3.lean").write_text(text)
        ev["lean"]["files"]["Ashldi3"] = sha(lean_dir / "Ashldi3.lean")

    return edit


def edit_evidence(change: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any], Path], None]:
    def edit(ev: dict[str, Any], lean_dir: Path) -> None:
        change(ev)

    return edit


def set_anchor(ev: dict[str, Any]) -> None:
    anchors = ev["units"][0]["anchors"]
    anchors["compiler-rt/lib/builtins/ashldi3.c"] = "0" * 64


def drop_anchor(ev: dict[str, Any]) -> None:
    ev["units"][0]["anchors"].pop("compiler-rt/lib/builtins/int_lib.h")


def other_pin(ev: dict[str, Any]) -> None:
    ev["llvm"]["commit"] = "0" * 40


def other_flags(ev: dict[str, Any]) -> None:
    ev["units"][0]["flags"] = [f if f != "-O3" else "-O0" for f in ev["units"][0]["flags"]]


def edited_lean(ev: dict[str, Any]) -> None:
    ev["units"][0]["lean_sha256"] = "0" * 64


def other_statement(ev: dict[str, Any]) -> None:
    ev["theorems"][0]["statement_sha256"] = hashing.sha256(b"(c 1:_ [])")


def reworded(ev: dict[str, Any]) -> None:
    ev["theorems"][0]["statement"] = ev["theorems"][0]["statement"].replace("64#32", "64")


def extra_field(ev: dict[str, Any]) -> None:
    ev["units"][0]["trusted"] = True


def cut(ev: dict[str, Any]) -> None:
    ev["cuts"] = ["__ashlti3"]


def listed_twice(ev: dict[str, Any]) -> None:
    ev["theorems"].append(copy.deepcopy(ev["theorems"][0]) | {"about": ["__ashlti3"]})


def plugin(ev: dict[str, Any]) -> None:
    ev["units"][0]["flags"].append("-fplugin=/tmp/anything.so")


def stand_in(ev: dict[str, Any], lean_dir: Path) -> None:
    """A unit of hand-written IR defining the same symbol, listed first, so it could stand in for the compiled
    function in a closure's coverage."""
    ll = lean_dir / "StandIn.ll"
    layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
    ll.write_text(
        f'target datalayout = "{layout}"\ntarget triple = "x86_64-unknown-linux-gnu"\n\n'
        "define i64 @__ashldi3(i64 noundef %a, i32 noundef %b) {\n  ret i64 %a\n}\n"
    )
    ir = copy.deepcopy(ev["units"][0]) | {
        "source": str(ll.relative_to(ROOT)), "source_in": "repo", "language": "ir", "flags": [],
        "include": [], "local_include": [], "llvm_config": False, "namespace": "StandIn", "translate": [],
        "anchors": {}, "repo_files": {str(ll.relative_to(ROOT)): sha(ll)}, "ir_sha256": sha(ll),
    }  # fmt: skip
    # Its own translation's hash, recorded as a forger would, so only the symbol defined twice is wrong.
    argv = [str(ROOT / "build" / "ir-lean"), "StandIn.ll", "--namespace", "StandIn", "-o", "StandIn.lean"]
    r = proc.run(argv, cwd=lean_dir, timeout=300)
    if r.exit != 0:
        raise SystemExit(f"FAIL ir-lean on the stand-in: {r.stderr.decode(errors='replace')}")
    ir["lean_sha256"] = sha(lean_dir / "StandIn.lean")
    ev["units"].insert(0, ir)


# name, how the good evidence is changed, the status and reason it has to get.
CASES: list[tuple[str, Callable[[dict[str, Any], Path], None], str, str]] = [
    ("wrong statement: a weaker hypothesis", edit_proof(WEAKER), "refused", "statement_mismatch"),
    (
        "wrong statement: another statement's hash",
        edit_evidence(other_statement),
        "refused",
        "statement_mismatch",
    ),
    ("wrong statement: printed differently", edit_evidence(reworded), "refused", "statement_mismatch"),
    (
        "wrong statement: a definition of the proof's own",
        edit_proof(OWN_DEFINITION),
        "refused",
        "foreign_constant",
    ),
    (
        "wrong statement: about a function named like the target",
        edit_proof(NAMED_LIKE_TARGET),
        "refused",
        "foreign_constant",
    ),
    ("stale anchors: the source's hash", edit_evidence(set_anchor), "refused", "stale_anchors"),
    ("stale anchors: a header left out", edit_evidence(drop_anchor), "refused", "stale_anchors"),
    ("stale anchors: another llvm-project", edit_evidence(other_pin), "refused", "stale_anchors"),
    ("extra axiom", edit_proof(AXIOM), "refused", "disallowed_axiom"),
    ("sorry", edit_proof(SORRY), "refused", "sorry"),
    ("kernel check skipped", edit_proof(SKIPPED), "refused", "kernel_replay_failed"),
    ("other flags", edit_evidence(other_flags), "refused", "ir_replay_mismatch"),
    ("edited translation", edit_evidence(edited_lean), "refused", "translation_replay_mismatch"),
    ("an extra field", edit_evidence(extra_field), "refused", "evidence_invalid"),
    ("proof rewrites a generated module", edit_proof(REWRITES_GENERATED), "error", "artifacts_modified"),
    ("proof adds a module where Lean looks", edit_proof(MAKES_INIT), "error", "artifacts_modified"),
    ("a call cut out", edit_evidence(cut), "partial", "cut"),
    (
        "a theorem listed twice, about another function",
        edit_evidence(listed_twice),
        "refused",
        "evidence_invalid",
    ),
    ("a flag that loads a plugin into clang", edit_evidence(plugin), "refused", "evidence_invalid"),
    ("the function also defined by hand-written IR", stand_in, "refused", "evidence_invalid"),
]


class Live:
    def __init__(self, jobs: int) -> None:
        self.jobs = jobs
        WORK.mkdir(parents=True, exist_ok=True)
        self.work = Path(tempfile.mkdtemp(prefix="run-", dir=WORK))

    def replay(self, ev: dict[str, Any], name: str, record: bool = False, **opts: Any) -> tuple[dict, Any]:
        started = time.monotonic()
        d = self.work / re.sub(r"[^A-Za-z0-9_.-]+", "_", name)
        d.mkdir(parents=True, exist_ok=True)
        v, out = vc.replay_evidence(copy.deepcopy(ev), work=d, jobs=self.jobs, record=record, **opts)
        v = v.verdict if isinstance(v, vc.Replayed) else v
        print(f"     {name}: {v['status']} {v['reason']} in {time.monotonic() - started:.1f} s")
        return v, out

    def cli(self, ev: dict[str, Any], name: str, *args: str, deny: str = "") -> tuple[dict[str, Any], int]:
        """Replays `ev` as a reader does, with tools/verify_claims.py evidence and IRLEAN_DENY_ALL set to
        `deny`: the verdict it prints, and its exit code."""
        started = time.monotonic()
        d = self.work / re.sub(r"[^A-Za-z0-9_.-]+", "_", name)
        d.mkdir(parents=True, exist_ok=True)
        (d / "evidence.json").write_text(json.dumps(ev))
        argv = [str(ROOT / "tools" / "verify_claims.py"), "evidence", str(d / "evidence.json"),
                "--work", str(d / "work"), "--jobs", str(self.jobs), *args]  # fmt: skip
        r = proc.run(argv, env={**os.environ, DENY_ALL: deny}, timeout=1800)
        try:
            v = json.loads(r.out)
        except json.JSONDecodeError:
            v = {"status": "no answer", "reason": f"exit {r.exit}", "detail": r.err[-2000:]}
        took = time.monotonic() - started
        print(f"     {name}: {v['status']} {v['reason']}, exit {r.exit}, in {took:.1f} s")
        return v, r.exit

    def good(self) -> dict[str, Any]:
        v, ev = self.replay(corpus(["CrtAshldi3"], model_proofs=False), "record ashldi3", record=True)
        if v["status"] != "replayed":
            raise SystemExit(f"FAIL recording the good evidence: {v['reason']}: {v['detail']}")
        return ev

    def corpus(self, failures: list[str]) -> None:
        """Every function tests/llvm.py proves, replayed as one piece of evidence."""
        ev = corpus()
        v, recorded = self.replay(ev, "every target tests/llvm.py proves", record=True)
        n = len(ev["theorems"])
        if v["status"] != "replayed":
            failures.append(f"corpus: {v['status']} {v['reason']}: {v['detail'][:3000]}")
            print(f"FAIL corpus: the verifier refuses what tests/llvm.py proves: {v['reason']}")
            return
        print(f"ok   corpus: {n} theorems about {len(recorded['units'])} units of LLVM's code replay")

    def scorer(self, failures: list[str]) -> None:
        """Every control tools/verify.py, the scorer's checker, certifies in tests/verification_negative, with
        the same IR and proof: the verifier has to replay each, and tools/verify.py has to prove each here
        too."""
        pin = tomllib.loads(TARGETS.read_text())["project"]
        cases = sorted((ROOT / "tests" / "verification_negative" / "cases").glob("control_*"))
        if not cases:
            failures.append("scorer: no controls in tests/verification_negative")
        for case in cases:
            manifest = json.loads((case / "case.json").read_text())
            if not manifest["expect"]["certified"]:
                continue
            request = manifest["request"]
            d = self.work / f"scorer-{case.name}"
            shutil.copytree(case, d)
            (d / "request.json").write_text(json.dumps(request))
            r = proc.run([str(ROOT / "tools" / "verify.py"), "check", str(d / "request.json")], timeout=900)
            try:
                scored = json.loads(r.out)["status"]
            except (json.JSONDecodeError, KeyError):
                scored = f"no answer: {r.err[-2000:]}"
            proof = request["proof"].removesuffix(".lean")
            ir = unit({"flags": {"none": {}}}, {"source": "", "flags": "none", "module": ""})
            ir |= {"source": str((case / request["input"]["ir"]).relative_to(ROOT)), "source_in": "repo",
                   "language": "ir", "namespace": request["namespace"], "translate": []}  # fmt: skip
            about = [n.removeprefix(request["namespace"] + ".") for n in manifest["names"]]
            ev = {
                "schema": vc.EVIDENCE_SCHEMA,
                "llvm": {k: pin[k] for k in ("tag", "commit", "nix_hash")},
                "lean_version": "",
                "units": [ir],
                "lean": {"root": str(case.relative_to(ROOT)), "files": {proof: ""}, "model": []},
                "theorems": [{"module": proof, "name": request["theorem"], "about": about, "statement": "",
                              "statement_sha256": ""}],
                "cuts": [],
                "contexts": "all",
            }  # fmt: skip
            v, _ = self.replay(ev, f"verifier on {case.name}", record=True)
            ok = scored == "proved" and v["status"] == "replayed"
            mark = "ok  " if ok else "FAIL"
            print(f"{mark} scorer: tools/verify.py says {scored}, the verifier {v['status']}, on {case.name}")
            if not ok:
                got = f"verify.py {scored}, verifier {v['status']} {v['reason']}: {v['detail'][:2000]}"
                failures.append(f"scorer {case.name}: {got}")

    def cases(self, good: dict[str, Any], only: list[str] | None, failures: list[str]) -> None:
        for name, change, status, reason in CASES:
            if only and not any(o in name for o in only):
                continue
            ev = copy.deepcopy(good)
            lean_dir = self.work / ("lean-" + str(abs(hash(name))))
            shutil.copytree(ROOT / "tests" / "llvm", lean_dir)
            ev["lean"]["root"] = str(lean_dir.relative_to(ROOT))
            change(ev, lean_dir)
            v, code = self.cli(ev, name)
            ok = (v["status"], v["reason"], code) == (status, reason, vc.EXIT[status])
            print(f"{'ok  ' if ok else 'FAIL'} forged: {name}: {v['status']} {v['reason']}, exit {code}")
            if not ok:
                got = f"{v['status']} {v['reason']}, exit {code}: {v['detail'][:2000]}"
                want = f"{status} {reason}, exit {vc.EXIT[status]}"
                failures.append(f"forged {name}: wanted {want}, got {got}")

    def guard(self, good: dict[str, Any], only: list[str] | None, failures: list[str]) -> None:
        """docs/verdicts.md's test 8, through replay_evidence and main: a replay that skipped a step, by a bug
        here or a caller's, isn't replayed, and IRLEAN_DENY_ALL takes the grant away, with no record and a
        non-zero exit."""
        kernel, passed = vc.Replay.kernel, vc.Replay.passed

        def one_short(r: vc.Replay) -> None:
            # leanchecker replays every module but the evidence's last, as a list built short would.
            files = r.ev["lean"]["files"]
            last = list(files)[-1]
            h = files.pop(last)
            try:
                kernel(r)
            finally:
                files[last] = h

        def twice(r: vc.Replay, name: str, detail: str = "") -> None:
            # The anchors' check counted twice, as one passed in a loop over units would be.
            for _ in range(1 + (name == "anchors")):
                passed(r, name, detail)

        for name, method, step in [("the kernel's replay skipped", "kernel", lambda r: None),
                                   ("the kernel's replay a module short", "kernel", one_short),
                                   ("a check passed twice", "passed", twice)]:  # fmt: skip
            if only and not any(o in name for o in only):
                continue
            with mock.patch.object(vc.Replay, method, step):
                v, _ = self.replay(good, name)
            ok = (v["status"], v["reason"]) == INCOMPLETE
            print(f"{'ok  ' if ok else 'FAIL'} guard: {name}: {v['status']} {v['reason']}")
            if not ok:
                failures.append(f"guard {name}: wanted error incomplete, got {v['status']} {v['reason']}")
        if only and not any(o in DENY_ALL for o in only):
            return
        for deny, want, code in [("", ("replayed", "replayed"), 0), ("1", ("error", "denied"), 5)]:
            record = self.work / f"deny-{deny or 'unset'}.json"
            v, got = self.cli(good, f"{DENY_ALL}={deny}", "--record", str(record), deny=deny)
            ok = (v["status"], v["reason"], got, record.exists()) == (*want, code, code == 0)
            said = (
                f"{v['status']} {v['reason']}, exit {got}, record {'written' if record.exists() else 'none'}"
            )
            print(f"{'ok  ' if ok else 'FAIL'} guard: {DENY_ALL}={deny}: {said}")
            if not ok:
                failures.append(f"guard {DENY_ALL}={deny}: wanted {' '.join(want)}, exit {code}, got {said}")

    def limits(self, good: dict[str, Any], failures: list[str]) -> None:
        """A proof that outlasts the time it's given is unknown, never refused or replayed."""
        ev = copy.deepcopy(good)
        lean_dir = self.work / "lean-sleeps"
        shutil.copytree(ROOT / "tests" / "llvm", lean_dir)
        ev["lean"]["root"] = str(lean_dir.relative_to(ROOT))
        edit_proof(SLEEPS)(ev, lean_dir)
        v, _ = self.replay(ev, "a proof that sleeps past the time limit", timeout=20)
        ok = v["status"] == "unknown"
        print(f"{'ok  ' if ok else 'FAIL'} limit: a proof past its time limit is {v['status']} {v['reason']}")
        if not ok:
            failures.append(f"limit: wanted unknown, got {v['status']} {v['reason']}")

    def claims(self, good: dict[str, Any], failures: list[str]) -> None:
        """A complete code-binding claim for a pass whose closure is one function: verified, and refused when
        the closure has a function no theorem is about, or the evidence is for some contexts or changed."""
        inv = json.loads(vc.INVENTORY.read_text())
        anchors = good["units"][0]["anchors"]
        item = {"id": "pass:toy-shift", "name": "toy-shift", "anchors": anchors, "unresolved_classes": []}
        inv["items"] = [item]
        d = self.work / "claims"
        (d / "closure").mkdir(parents=True)
        (d / "inventory.json").write_text(json.dumps(inv))
        evidence = d / "toy-shift.evidence.json"
        evidence.write_text(json.dumps(good))
        source = "compiler-rt/lib/builtins/ashldi3.c"
        functions: list[dict[str, str]] = [{"symbol": "__ashldi3", "file": source}]
        closure = {"schema": vc.CLOSURE_SCHEMA, "complete": True, "files": anchors, "functions": functions}
        c = {"item": "pass:toy-shift", "dimension": "code-binding", "contexts": "all", "status": "complete",
             "anchors": anchors, "gaps": [], "evidence": [{"kind": "binding-check",
             "path": str(evidence.relative_to(ROOT)), "sha256": sha(evidence)}]}  # fmt: skip
        uncovered = closure | {"functions": [*functions, {"symbol": "__ashlti3", "file": source}]}
        some = copy.deepcopy(good) | {"contexts": ["opt:default<O2>"]}
        some_path = evidence.with_name("toy-shift-some.evidence.json")
        some_path.write_text(json.dumps(some))
        c_some = c | {"evidence": [{"kind": "binding-check", "path": str(some_path.relative_to(ROOT)),
                                    "sha256": sha(some_path)}]}  # fmt: skip
        for name, cl, clo, want in [
            ("a pass whose closure is one proved function", c, closure, ("verified", "verified")),
            ("a closure function no theorem is about", c, uncovered, ("refused", "closure_uncovered")),
            ("evidence for only some contexts", c_some, closure, ("refused", "contexts_uncovered")),
            ("evidence changed since the claim", c | {"evidence": [{**c["evidence"][0], "sha256": "0" * 64}]},
             closure, ("refused", "stale_evidence")),
        ]:  # fmt: skip
            (d / "closure" / "toy-shift.json").write_text(json.dumps(clo))
            v = vc.decide_claim(cl, inventory=d / "inventory.json", closures=d / "closure",
                                replay_options={"jobs": self.jobs})  # fmt: skip
            ok = (v["status"], v["reason"]) == want
            print(f"{'ok  ' if ok else 'FAIL'} claim: {name}: {v['status']} {v['reason']}")
            if not ok:
                failures.append(
                    f"claim {name}: wanted {want}, got {v['status']} {v['reason']}: {v['detail'][:2000]}"
                )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tier", choices=["static", "live", "all"], default="all")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("LEAN_JOBS", "4")))
    args = ap.parse_args()
    # Set where this runs, it would take every grant away the tests expect.
    os.environ.pop(DENY_ALL, None)
    failures: list[str] = []
    if args.tier in ("static", "all"):
        failures += run_static()
    if args.tier in ("live", "all"):
        live = Live(args.jobs)
        try:
            good = live.good()
            if not args.only:
                live.corpus(failures)
                live.scorer(failures)
                live.limits(good, failures)
                live.claims(good, failures)
            live.guard(good, args.only, failures)
            live.cases(good, args.only, failures)
        finally:
            shutil.rmtree(live.work, ignore_errors=True)
    for f in failures:
        print(f"FAIL {f}", file=sys.stderr)
    print(f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
