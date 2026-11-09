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

usage: tests/verify_claims_test.py [--tier static|live|all] [--only NAME ...] [--jobs N]

`static` needs only Python. `live` needs the dev shell, build/ir-lean and `lake build IRLean`.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import shutil
import sys
import tempfile
import time
import tomllib
from collections.abc import Callable
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import verify_claims as vc  # noqa: E402
from irlean import proc  # noqa: E402

TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
WORK = ROOT / "build" / "verify-claims-test"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    # tests/llvm_scope.py asks this verifier, and only for a complete claim.
    sys.path.insert(0, str(ROOT / "tests"))
    import llvm_scope

    ok = llvm_scope.VERIFIERS.get("binding-check") is vc.check_claim
    print(
        f"{'ok  ' if ok else 'FAIL'} static: tests/llvm_scope.py asks this verifier for code-binding claims"
    )
    if not ok:
        failures.append("tests/llvm_scope.py's VERIFIERS doesn't use tools/verify_claims.py")
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
    ev["theorems"][0]["statement_sha256"] = hashlib.sha256(b"(c 1:_ [])").hexdigest()


def reworded(ev: dict[str, Any]) -> None:
    ev["theorems"][0]["statement"] = ev["theorems"][0]["statement"].replace("64#32", "64")


def extra_field(ev: dict[str, Any]) -> None:
    ev["units"][0]["trusted"] = True


def cut(ev: dict[str, Any]) -> None:
    ev["cuts"] = ["__ashlti3"]


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
    ("proof rewrites a generated module", edit_proof(REWRITES_GENERATED), "refused", "artifacts_modified"),
    ("proof adds a module where Lean looks", edit_proof(MAKES_INIT), "refused", "artifacts_modified"),
    ("a call cut out", edit_evidence(cut), "partial", "cut"),
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
        print(f"     {name}: {v['status']} {v['reason']} in {time.monotonic() - started:.1f} s")
        return v, out

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
            v, _ = self.replay(ev, name)
            ok = (v["status"], v["reason"]) == (status, reason)
            print(f"{'ok  ' if ok else 'FAIL'} forged: {name}: {v['status']} {v['reason']}")
            if not ok:
                got = f"{v['status']} {v['reason']}: {v['detail'][:2000]}"
                failures.append(f"forged {name}: wanted {status} {reason}, got {got}")

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
            live.cases(good, args.only, failures)
        finally:
            shutil.rmtree(live.work, ignore_errors=True)
    for f in failures:
        print(f"FAIL {f}", file=sys.stderr)
    print(f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
