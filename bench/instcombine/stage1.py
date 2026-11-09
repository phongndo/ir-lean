#!/usr/bin/env python3
"""Stage 1 of proved superoptimization: certify InstCombine's own rewrites with ir-lean, compare the verdicts
with Alive2's, and check that no known-wrong rewrite gets a certificate. docs/stage1.md says what each verdict
means, how the pairs are made, and what the numbers do and don't say.

Each stage reads what the ones before wrote under WORK, build/stage1 by default, and skips what's done, so a
long run can stop and go on:

  pairs     Runs `opt -passes=instcombine` on each test, and for each function the run changed, cuts that
            function into a module of its own with llvm-extract and runs opt on it alone, as tools/binding.py
            replays it. Classifies each pair by what the model and the gates can judge.
  prove     For each pair the model can judge, writes a refinement theorem whose proof is found by case splits
            and `bv_decide`, and checks it with tools/verify.py, for every input that's a value or poison.
            Only a result tests/verify_negative.py's gate accepts is `proved`.
  certify   For each proved pair tools/binding.py can bind, records and verifies a bundle, as
            `ir_instance_refinement`. Only `bound`, from this run, with exit code 0, is a certificate.
  alive     Asks Alive2 about every changed pair, through tests/alive.py's flags.
  refute    Runs the model on Alive2's counterexample and on edge values, through tools/verify.py, for each
            pair that wasn't proved, and asks whether a counterexample goes through a model stop.
  report    Counts everything, builds the agreement matrix, and writes summary.json with the toolchain.

  all       pairs to refute, then report. ci runs them on bench/instcombine/fixture and checks expect.json.
  known-fetch, known-build, known-pairs   The known-miscompilation corpus, known_wrong.json.

usage: bench/instcombine/stage1.py [--work DIR] all [--files TEST ...] [--sample N] [--seed S]
       bench/instcombine/stage1.py [--work DIR] pairs|prove|certify|alive|refute|report [options]
       bench/instcombine/stage1.py [--work DIR] known-pairs, then prove ... report on that WORK
       bench/instcombine/stage1.py [--work DIR] ci
"""

from __future__ import annotations

import argparse
import concurrent.futures
import functools
import importlib.util
import json
import os
import random
import re
import shlex
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, model, proc, schemas  # noqa: E402
from irlean import verdict as core  # noqa: E402

TOOL = ROOT / "build" / "ir-lean"
BINDING_PY = ROOT / "tools" / "binding.py"
LIBRARY = ROOT / ".lake" / "build" / "lib" / "lean"
WORK = ROOT / "build" / "stage1"
SCHEMA = schemas.STAGE1_PAIR
SUMMARY_SCHEMA = schemas.STAGE1_SUMMARY
# The namespace of every certificate tools/binding.py checks. Each compiles in a directory of its own, so
# they can share it.
NS = "S1"
THEOREM = f"{NS}.cert"
HEARTBEATS = 2000000
# At most 2^CASE_BITS cases, poison or a value for each argument and lane.
CASE_BITS = 8


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# The gate's own predicates, so a pair is unsupported here exactly when tools/binding.py would call it so.
B = load("binding", BINDING_PY)


def sha(data: str | bytes) -> str:
    return hashing.sha256_text(data) if isinstance(data, str) else hashing.sha256(data)


def sh(
    argv: list[str],
    stdin: str | None = None,
    timeout: float = 120,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> tuple[int | None, str, str]:
    """(exit code, stdout, stderr), through irlean.proc. The exit code is None if a limit stopped it."""
    ran = proc.run(argv, timeout=timeout, stdin=stdin, cwd=cwd, env={**os.environ, **(env or {})})
    return (None if ran.limit else ran.exit), ran.out, ran.err


def llvm_tests() -> Path:
    src = os.environ.get("LLVM_PROJECT_SRC")
    if not src:
        sys.exit("LLVM_PROJECT_SRC isn't set: run inside nix develop")
    return Path(src) / "llvm" / "test" / "Transforms"


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(llvm_tests().parent.parent.parent))
    except ValueError:
        return str(path)


# ------------------------------------------------------------------------------------------------------------
# Pairs

RUN_LINE = re.compile(r"^\s*;\s*RUN:(.*)$", re.M)
# Promises to progress or to return. Recorded for the report: since SEM-07 the model checks them.
PROMISES = re.compile(r"\b(mustprogress|willreturn)\b")
DEFINE_NAME = re.compile(r'^define [^@]*@("(?:[^"\\]|\\.)*"|[-\w.$]+)\(', re.M)


def run_spec(text: str) -> tuple[str, str | None, list[str]]:
    """The instcombine spec and -mtriple of the test's first RUN line that runs instcombine alone, and the
    options it gives that a bundle can't hold. Without one, plain `instcombine` and no triple."""
    joined, cur = [], ""
    for m in RUN_LINE.finditer(text):
        line = m.group(1).rstrip()
        if line.endswith("\\"):
            cur += line[:-1] + " "
            continue
        joined.append((cur + line).strip())
        cur = ""
    for command in joined:
        try:
            words = shlex.split(command.split("|", 1)[0])
        except ValueError:
            continue
        if not words or words[0] != "opt":
            continue
        spec, mtriple, other = None, None, []
        i = 1
        while i < len(words):
            w = words[i]
            if w.startswith(("-passes=", "--passes=")):
                spec = w.split("=", 1)[1]
            elif w.startswith(("-mtriple=", "--mtriple=")):
                mtriple = w.split("=", 1)[1]
            elif w in ("-mtriple", "--mtriple") and i + 1 < len(words):
                mtriple = words[i + 1]
                i += 1
            elif w in ("-o",) and i + 1 < len(words):
                i += 1
            elif w not in ("-S", "-", "%s", "<", "-disable-output") and not w.startswith(("<", ">", "2>")):
                other.append(w)
            i += 1
        if spec and re.fullmatch(r"instcombine(<[^>]*>)?", spec):
            return spec, mtriple, other
    return "instcombine", None, []


def names(ll: str) -> list[str]:
    return [n[1:-1] if n.startswith('"') else n for n in DEFINE_NAME.findall(ll)]


def func_text(ll: str, name: str) -> str | None:
    """A function's text with its attribute groups written out, so a change to its attributes counts."""
    quoted = re.escape(name if re.fullmatch(r"[-\w.$]+", name) else f'"{name}"')
    m = re.search(rf"^define [^@]*@{quoted}\(.*?^}}", ll, re.M | re.S)
    if not m:
        return None
    groups = dict(re.findall(r"^attributes (#\d+) = \{ (.*) \}$", ll, re.M))
    return re.sub(r"#\d+\b", lambda g: "{" + groups.get(g.group(0), g.group(0)) + "}", m.group(0))


def opt(ll: str, passes: str, mtriple: str | None, timeout: float = 120) -> tuple[str | None, str]:
    """`opt -S -passes=SPEC`, reading stdin, exactly as tools/binding.py runs it."""
    code, out, err = sh(B.opt_argv("opt", passes, mtriple), stdin=ll, timeout=timeout)
    if code is None:
        return None, "opt_timeout"
    return (
        (out, "")
        if code == 0
        else (None, err.strip().splitlines()[-1][:300] if err.strip() else f"exit {code}")
    )


def report_row(ll_path: Path, function: str) -> list[str] | None:
    code, out, _ = sh([str(TOOL), str(ll_path), "--report"], timeout=120)
    if code not in (0, 3):
        return None
    for line in out.splitlines():
        row = line.split("\t")
        if len(row) >= 2 and row[1] == function:
            return row
    return None


def pair_id(test: str, function: str) -> str:
    return sha(f"{test}\0{function}")[:16]


def make_pair(test: str, function: str, src_all: str, spec: str, mtriple: str | None, work: Path) -> dict:
    """One changed function, cut into its own module, with opt run on that alone."""
    pid = pair_id(test, function)
    d = work / "pairs" / pid
    d.mkdir(parents=True, exist_ok=True)
    rec: dict[str, Any] = {
        "schema": SCHEMA,
        "id": pid,
        "test": test,
        "function": function,
        "spec": spec,
        "mtriple": mtriple,
    }
    code, extracted, err = sh(["llvm-extract", "-S", f"--func={function}", "-", "-o", "-"], stdin=src_all)
    if code != 0:
        return {**rec, "status": "error", "reason": "extract_failed", "detail": err[-300:]}
    (d / "input.ll").write_text(extracted)
    src, why = opt(extracted, "verify", mtriple)
    if src is None:
        return {**rec, "status": "error", "reason": "opt_rejects_extracted", "detail": why}
    tgt, why = opt(extracted, spec, mtriple)
    if tgt is None:
        return {**rec, "status": "error", "reason": "opt_failed", "detail": why}
    (d / "src.ll").write_text(src)
    (d / "tgt.ll").write_text(tgt)
    rec.update(input_sha256=sha(extracted), src_sha256=sha(src), tgt_sha256=sha(tgt))
    a, b = func_text(src, function), func_text(tgt, function)
    if b is None:
        return {**rec, "status": "skipped", "reason": "removed_by_pass"}
    if a == b:
        return {**rec, "status": "skipped", "reason": "unchanged_alone"}
    return classify(rec, d, src, tgt, function)


def test_pairs(path: Path, work: Path) -> dict:
    """Every changed function of one test, as pairs, with what happened to the test as a whole."""
    test = rel(path)
    text = path.read_text(errors="replace")
    spec, mtriple, other = run_spec(text)
    out: dict[str, Any] = {
        "test": test,
        "spec": spec,
        "mtriple": mtriple,
        "other_options": other,
        "pairs": [],
    }
    src_all, why = opt(text, "verify", mtriple)
    if src_all is None:
        return {**out, "status": "opt_rejects", "detail": why}
    tgt_all, why = opt(text, spec, mtriple)
    if tgt_all is None and spec == "instcombine":
        # A test whose rewrites don't reach a fixpoint in one run, which opt refuses, as its RUN line says.
        spec = "instcombine<no-verify-fixpoint>"
        out["spec"] = spec
        tgt_all, why = opt(text, spec, mtriple)
    if tgt_all is None:
        return {**out, "status": "opt_failed", "detail": why}
    fs = names(src_all)
    out["functions"] = len(fs)
    changed = [f for f in fs if func_text(src_all, f) != func_text(tgt_all, f)]
    out["changed"] = len(changed)
    out["pairs"] = [make_pair(test, f, src_all, spec, mtriple, work) for f in changed]
    return {**out, "status": "ok"}


def cmd_pairs(args: argparse.Namespace) -> int:
    work: Path = args.work
    work.mkdir(parents=True, exist_ok=True)
    if args.files:
        files = [Path(f).resolve() for f in args.files]
    else:
        files = sorted((llvm_tests() / "InstCombine").rglob("*.ll"))
        if args.sample:
            files = sorted(random.Random(args.seed).sample(files, min(args.sample, len(files))))
    t0 = time.time()
    tests = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for n, t in enumerate(pool.map(lambda p: test_pairs(p, work), files), 1):
            tests.append(t)
            if n % 100 == 0:
                print(f"{n}/{len(files)} tests, {time.time() - t0:.0f} s", file=sys.stderr)
    pairs = [p for t in tests for p in t["pairs"]]
    with open(work / "tests.jsonl", "w") as f:
        for t in tests:
            f.write(json.dumps({k: v for k, v in t.items() if k != "pairs"}) + "\n")
    with open(work / "pairs.jsonl", "w") as f:
        for p in pairs:
            f.write(json.dumps(p) + "\n")
    counts: dict[str, int] = {}
    for p in pairs:
        key = f"{p['status']}:{p['reason']}"
        counts[key] = counts.get(key, 0) + 1
    print(
        json.dumps(
            {
                "tests": len(tests),
                "seconds": round(time.time() - t0, 1),
                "functions": sum(t.get("functions", 0) for t in tests),
                "changed": sum(t.get("changed", 0) for t in tests),
                "pairs": counts,
            },
            indent=1,
        )
    )
    return 0


# ------------------------------------------------------------------------------------------------------------
# Proofs, through tools/verify.py and the negative-verification gate

VN = load("verify_negative", ROOT / "tests" / "verify_negative.py")
# Inputs that are values or poison, never undef: Alive2's --disable-undef-input.

AUTOMATION = """namespace {ns}.Auto

theorem run_ite {{β ρ : Type}} (step : β → Outcome (Next β ρ)) (c : Prop) [Decidable c] (a b : β) :
    run step (if c then a else b) = if c then run step a else run step b := by split <;> rfl
theorem le_ok [Refine α] (x : α) (b : Outcome α) :
    Refine.le (some (Except.ok x) : Outcome α) b ↔ ∃ y, b = some (.ok y) ∧ Refine.le x y := Iff.rfl
theorem le_ub [Refine α] (r : UB) (b : Outcome α) :
    Refine.le (some (Except.error (Stop.undefined r)) : Outcome α) b ↔ True := iff_of_true trivial trivial
theorem le_stop [Refine α] (s : ModelStop) (b : Outcome α) :
    Refine.le (some (Except.error (Stop.model s)) : Outcome α) b ↔ False := iff_false_intro id
theorem le_spin [Refine α] (b : Outcome α) : Refine.le (none : Outcome α) b ↔ b = none := Iff.rfl
theorem val_le_none (b : Val w) : Refine.le (none : Val w) b ↔ True := iff_of_true trivial trivial
theorem val_le_some (x : BitVec w) (b : Val w) : Refine.le (some x : Val w) b ↔ b = some x := Iff.rfl
theorem vec_le [Refine α] (a b : Vector α n) : Refine.le a b ↔ ∀ i : Fin n, Refine.le a[i] b[i] := Iff.rfl
theorem fin_forall_zero (P : Fin 0 → Prop) : (∀ i, P i) ↔ True := ⟨fun _ => trivial, fun _ i => i.elim0⟩
theorem fin_forall_succ {{n : Nat}} (P : Fin (n + 1) → Prop) : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun h => ⟨h 0, fun i => h i.succ⟩, fun ⟨h0, hs⟩ i => Fin.cases h0 hs i⟩

/-- Runs both sides a block at a time, splitting at each branch and each case of the refinement, and closes
each path with `bv_decide`. -/
macro "ir_refine" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [$ls,*, IRLean.noundef]
  repeat' (first
    | simp [$ls,*, llvm, llvm_val, {ns}.Auto.run_ite, IRLean.jump, IRLean.ret, IRLean.Outcome.ok,
        IRLean.Outcome.ub, Bool.cond_eq_ite, {ns}.Auto.le_ok, {ns}.Auto.le_ub, {ns}.Auto.le_stop,
        {ns}.Auto.le_spin, {ns}.Auto.val_le_none, {ns}.Auto.val_le_some, {ns}.Auto.vec_le,
        {ns}.Auto.fin_forall_zero, {ns}.Auto.fin_forall_succ] at *
    | rw [IRLean.run]
    | split
    | split at *)
  all_goals first
    | rfl
    | trivial
    | bv_decide
    | (exfalso; bv_decide)))

end {ns}.Auto
"""


SIGNATURE_LINE = re.compile(r"^noncomputable def (\S+)(.*) : (Outcomes? .*) :=(?: fun \S+ =>)?$", re.M)


def groups(text: str) -> list[str]:
    """The top-level parenthesized groups in `text`, which can nest, as `(A : (Vec 4 32))` does."""
    out, depth, cur = [], 0, ""
    for c in text:
        if c == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif c == ")":
            depth -= 1
            if depth == 0:
                out.append(cur)
                continue
        if depth >= 1:
            cur += c
    return out


def signature(module: str, name: str) -> tuple[list[str], str] | None:
    """The argument types and result type of a generated function, or None if it isn't there. Types lose the
    parentheses the emitter puts around some, so `(Vec 4 32)` is `Vec 4 32`."""
    for m in SIGNATURE_LINE.finditer(module):
        if m.group(1) in (name, f"«{name}»"):
            types = []
            for group in groups(m.group(2)):
                names_, _, ty = group.partition(" : ")
                ty = ty.strip()
                while ty.startswith("(") and ty.endswith(")") and groups(ty) == [ty[1:-1]]:
                    ty = ty[1:-1].strip()
                types += [ty] * len(names_.split())
            kind, _, inner = m.group(3).partition(" ")
            inner = inner.strip()
            while inner.startswith("(") and inner.endswith(")") and groups(inner) == [inner[1:-1]]:
                inner = inner[1:-1].strip()
            return types, f"{kind} ({inner})"
    return None


def claim(src: str, tgt: str, n: int, chooses: tuple[bool, bool]) -> str:
    """`IRLean.Refines src tgt`, as tools/binding_check.lean builds it. Since F3, a function whose run makes
    choices returns `IRLean.Outcomes`; where only one side does, the other is lifted with
    `IRLean.Outcomes.det`, the same outcome for every choice."""
    xs = " ".join(f"x{i}" for i in range(n))

    def lifted(f: str) -> str:
        return f"(fun {xs} => IRLean.Outcomes.det ({f} {xs}))" if n else f"(IRLean.Outcomes.det {f})"

    if chooses == (False, True):
        return f"IRLean.Refines {lifted(src)} {tgt}"
    if chooses == (True, False):
        return f"IRLean.Refines {src} {lifted(tgt)}"
    return f"IRLean.Refines {src} {tgt}"


# Past the arguments, how the proof takes each side's choices: for every way the target chooses, a source
# that makes none allows it, or one that does chooses the same, or, choosing alone, chooses 0 everywhere.
CHOICE_TACTIC = {
    (False, False): "",
    (False, True): "rw [IRLean.Refine.outcomes_det_left]\n  intro ct\n  ",
    (True, True): "apply IRLean.Refine.outcomes_of_same\n  intro ct\n  ",
    (True, False): "rw [IRLean.Refine.outcomes_det_right]\n  refine ⟨fun _ => 0, ?_⟩\n  ",
}


def proof(
    ns: str,
    src: str,
    tgt: str,
    args: list[str],
    imports: list[str],
    module: str,
    chooses: tuple[bool, bool] = (False, False),
) -> str:
    """A refinement certificate: the claim, stated as tools/binding_check.lean builds it, and a proof found by
    case splits and `bv_decide`. The proof is untrusted; the gates check it."""
    unfold = []
    for f in (src, tgt):
        unfold.append(f)
        bare = f.rsplit(".", 1)[-1]
        if re.search(rf"^namespace «?{re.escape(bare)}»?$", module, re.M):
            unfold.append(f"{f}.step")
    xs = [f"x{i}" for i in range(len(args))]
    intro = (f"intro {' '.join(xs)}\n  " if xs else "") + ("dsimp only\n  " if any(chooses) else "")
    intro += CHOICE_TACTIC[chooses]
    # Each vector argument is taken apart into its lanes, and each value, lane or not, into poison or a
    # value: at most 2^CASE_BITS cases, past which nothing is split and the proof is left to fail or run out.
    lanes = sum(int(m.group(1)) if (m := re.fullmatch(r"Vec (\d+) \d+", ty)) else 1 for ty in args)
    values: list[str] = []
    for i, (x, ty) in enumerate(zip(xs, args, strict=True)):
        if ty.startswith("Val "):
            values.append(x)
        elif (m := re.fullmatch(r"Vec (\d+) \d+", ty)) and lanes <= CASE_BITS:
            n = int(m.group(1))
            names_ = [f"{x}_{k}" for k in range(n)]
            pattern = "_ | ⟨_, _⟩"
            for name in reversed(names_):
                pattern = f"_ | ⟨{name}, {pattern}⟩"
            intro += f"obtain ⟨⟨l{i}⟩, h{i}⟩ := {x}\n  rcases l{i} with {pattern} <;> simp at h{i}\n  "
            values += names_
    if lanes > CASE_BITS:
        values = []
    split = " <;> ".join(f"cases {x}" for x in values)
    return (
        "".join(f"import {i}\n" for i in imports)
        + "\nopen IRLean\n\nset_option linter.unusedSimpArgs false\n"
        + "set_option exponentiation.threshold 4096\n\n"
        + AUTOMATION.format(ns=ns)
        + f"\nset_option maxHeartbeats {HEARTBEATS} in\n"
        + f"theorem {ns}.cert : {claim(src, tgt, len(args), chooses)} := by\n"
        + f"  {intro}{split + ' <;> ' if split else ''}ir_refine [{', '.join(unfold)}]\n"
    )


def rename(ll: str, old: str, new: str) -> str:
    quoted = re.escape(old if re.fullmatch(r"[-\w.$]+", old) else f'"{old}"')
    return re.sub(rf"@{quoted}(?=[\s(,)])", f"@{new}", ll)


def combined(pair: dict, d: Path) -> str | None:
    """One module with the pair's source as @src and its target as @tgt, which tools/verify.py takes as one
    input. Returns why not, or None."""
    work = WORK_OF(d)
    src = (work / "src.ll").read_text()
    tgt = (work / "tgt.ll").read_text()
    files = d / "files"
    files.mkdir(parents=True, exist_ok=True)
    (d / "a.ll").write_text(rename(src, pair["function"], "src"))
    (d / "b.ll").write_text(rename(tgt, pair["function"], "tgt"))
    code, _, err = sh(["llvm-link", "-S", str(d / "a.ll"), str(d / "b.ll"), "-o", str(files / "Opt.ll")])
    return None if code == 0 else f"llvm-link: {err.strip()[-300:]}"


def WORK_OF(d: Path) -> Path:
    return d.parent.parent / "pairs" / d.name


def verify_once(request: dict, files: Path, name: str, logs: Path, timeout: float) -> tuple[Any, Any, Any]:
    """tools/verify.py on one request, through irlean.proc, which stops it a minute past its own limit and
    kills whatever it leaves. Returns the negative-verification gate's view of the run, the checkers'
    hashes, and the run itself, for irlean.verdict."""
    path = files / f"{name}.json"
    path.write_text(json.dumps(request, ensure_ascii=False, indent=2) + "\n")
    checkers = VN.checker_hashes()
    argv = [sys.executable, str(ROOT / "tools" / "verify.py"), "check", str(path), "--tool", str(TOOL)]
    logs.mkdir(parents=True, exist_ok=True)
    ran = proc.run([*argv, "--work-dir", str(logs / "work")], timeout=timeout + 60, cwd=ROOT)
    (logs / "stdout.txt").write_bytes(ran.stdout)
    (logs / "stderr.txt").write_bytes(ran.stderr)
    harness = VN.Harness(
        exit=ran.exit if ran.exit >= 0 else None,
        signal=ran.signal,
        timed_out=ran.limit == "time_limit",
        seconds=round(ran.seconds, 2),
        peak_rss_mb=int(ran.peak_process_mb),
        stdout=ran.out,
        stderr=ran.err,
    )
    return harness, checkers, ran


def record_of(ran: Any) -> Any:
    try:
        return json.loads(ran.out)
    except ValueError:
        return None


def decided(claim: core.Verdict, ran: Any, record: Any, files: dict[str, bool]) -> core.Decision:
    """irlean.verdict on tools/verify.py's run and the record it printed, about these files."""
    return core.decide(
        claim, core.Evidence(upstream=(core.Step.of("tools/verify.py", ran), record), files=files)
    )


def prove_pair(pair: dict, work: Path, timeout: int, memory: int, versions: dict, v: Any) -> dict:
    d = work / "prove" / pair["id"]
    if d.exists():
        import shutil

        shutil.rmtree(d)
    d.mkdir(parents=True)
    out: dict[str, Any] = {"id": pair["id"]}
    why = combined(pair, d)
    files = d / "files"
    if why:
        return {**out, "lean": "error", "reason": "combine_failed", "detail": why}
    code, module, err = sh([str(TOOL), str(files / "Opt.ll"), "--no-code", "--namespace", "Opt"])
    sig_src, sig_tgt = signature(module, "src"), signature(module, "tgt")
    if code not in (0, 3) or sig_src is None or sig_tgt is None:
        return {**out, "lean": "unsupported", "reason": "emitter_combined", "detail": err.strip()[-300:]}
    out["args"], out["result"], out["tgt_result"] = sig_src[0], sig_src[1], sig_tgt[1]
    chooses = (sig_src[1].startswith("Outcomes "), sig_tgt[1].startswith("Outcomes "))
    out["chooses"] = list(chooses)
    pin = claim("Opt.src", "Opt.tgt", len(sig_src[0]), chooses)
    (files / "Proof.lean").write_text(
        proof("Opt", "Opt.src", "Opt.tgt", sig_src[0], ["Opt"], module, chooses)
    )
    request = {
        "input": {"ir": "Opt.ll"},
        "namespace": "Opt",
        "function": "tgt",
        "proof": "Proof.lean",
        "theorem": "Opt.cert",
        "statement": pin,
        "limits": {"timeout_seconds": timeout, "memory_mb": memory},
    }
    harness, checkers, ran = verify_once(request, files, "request", d / "check", timeout)
    envelope = VN.envelope_for(harness, checkers, None)
    (d / "envelope.json").write_text(json.dumps(envelope, indent=1, ensure_ascii=False) + "\n")
    expected = {
        "function": "tgt",
        "namespace": "Opt",
        "pin": pin,
        "names": ["Opt.src", "Opt.tgt"],
        "precondition": None,
        "files": {"input": VN.sha256_file(files / "Opt.ll"), "proof": VN.sha256_file(files / "Proof.lean")},
        "versions": versions,
        "checker_sha256": VN.checker_hashes(),
        "this_run": True,
    }
    denials = VN.gate(envelope, expected, v)
    result = envelope["result"] if isinstance(envelope["result"], dict) else {}
    out.update(
        seconds=harness.seconds,
        peak_rss_mb=harness.peak_rss_mb,
        verify_status=result.get("status"),
        verify_reason=result.get("reason"),
        denials=denials,
    )
    if not denials:
        # The gate passed; irlean.verdict decides, from tools/verify.py's run and record, and the files
        # it hashed.
        hashed = (result.get("artifacts") or {}).get("files") or {}
        files_ok = {
            role: (hashed.get(role) or {}).get("sha256") == h for role, h in expected["files"].items()
        }
        decision = decided(core.Verdict.PROVED, ran, record_of(ran), files_ok)
        if decision.granted:
            return {**out, "lean": "proved", "reason": "kernel_checked"}
        return {
            **out,
            "lean": str(decision.verdict),
            "reason": f"verdict_{decision.reason}",
            "detail": decision.detail,
        }
    status = result.get("status")
    diag = json.dumps(result.get("diagnostics") or "")
    out["bv_counterexample"] = "counterexample" in diag
    if harness.timed_out or status == "timeout":
        return {**out, "lean": "unknown", "reason": result.get("reason") or "harness_timeout"}
    if status == "unsupported":
        return {**out, "lean": "unsupported", "reason": result.get("reason")}
    if status == "error" and result.get("reason") == "proof_failed":
        return {**out, "lean": "failed", "reason": "proof_not_found"}
    return {**out, "lean": "error", "reason": result.get("reason") or ",".join(denials)}


def read_jsonl(path: Path) -> list[dict]:
    return (
        [json.loads(line) for line in path.read_text().splitlines() if line.strip()] if path.exists() else []
    )


def sample(work: Path, upto: int | None) -> set[str] | None:
    """The first `upto` changed pairs the model or Alive2 can be asked about, in the order of their ids. An id
    is a SHA-256 of the test and function, so this is a uniform sample of them, the same one every run, and
    each larger sample holds the smaller ones. None for every pair."""
    if upto is None:
        return None
    ids = sorted(
        p["id"] for p in read_jsonl(work / "pairs.jsonl") if p["status"] in ("candidate", "unsupported")
    )
    return set(ids[:upto])


def cmd_prove(args: argparse.Namespace) -> int:
    work: Path = args.work
    pairs = [p for p in read_jsonl(work / "pairs.jsonl") if p["status"] == "candidate"]
    done = {r["id"]: r for r in read_jsonl(work / "prove.jsonl")} if not args.again else {}
    keep = sample(work, getattr(args, "upto", None))
    # Only pairs tools/binding.py can bind: with `certify`, every certificate there can be, which gives G1.
    only = eligible if getattr(args, "eligible_only", False) else (lambda p: True)
    todo = sorted(
        (p for p in pairs if p["id"] not in done and (keep is None or p["id"] in keep) and only(p)),
        key=lambda p: p["id"],
    )[: args.limit]
    v = VN.load_verify()
    versions = VN.current_versions(v, TOOL)
    t0 = time.time()
    with (
        open(work / "prove.jsonl", "a" if done else "w") as f,
        concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool,
    ):
        futures = [
            pool.submit(prove_pair, p, work, args.timeout, args.lean_memory, versions, v) for p in todo
        ]
        for n, fut in enumerate(concurrent.futures.as_completed(futures), 1):
            r = fut.result()
            f.write(json.dumps(r) + "\n")
            f.flush()
            if n % 25 == 0:
                print(f"{n}/{len(todo)} pairs, {time.time() - t0:.0f} s", file=sys.stderr)
    rows = list(done.values()) + read_jsonl(work / "prove.jsonl")[len(done) :]
    counts: dict[str, int] = {}
    for r in rows:
        counts[f"{r['lean']}:{r['reason']}"] = counts.get(f"{r['lean']}:{r['reason']}", 0) + 1
    print(json.dumps({"pairs": len(rows), "seconds": round(time.time() - t0, 1), "counts": counts}, indent=1))
    return 0


# ------------------------------------------------------------------------------------------------------------
# Certificates, through tools/binding.py

VERDICT_SCHEMA = schemas.BINDING_VERDICT


def certify_pair(pair: dict, prove: dict, work: Path, timeout: int, memory: int) -> dict:
    """Records a bundle for the pair's opt run and verifies it from scratch. Only `bound`, with exit code 0,
    about this pair's input, function, pass spec and claim kind, is a certificate."""
    import shutil

    out: dict[str, Any] = {"id": pair["id"]}
    d = work / "certify" / pair["id"]
    if d.exists():
        shutil.rmtree(d)
    d.mkdir(parents=True)
    lean = pair["lean_name"]
    sigs, modules = [], []
    for side in ("Src", "Tgt"):
        ll = work / "pairs" / pair["id"] / f"{side.lower()}.ll"
        code, module, err = sh([str(TOOL), str(ll), "--no-code", "--namespace", f"{NS}.{side}"])
        sigs.append(signature(module, lean) if code in (0, 3) else None)
        modules.append(module)
    if sigs[0] is None or sigs[1] is None:
        return {**out, "gate": "error", "reason": "no_signature", "detail": err[-300:]}
    chooses = (sigs[0][1].startswith("Outcomes "), sigs[1][1].startswith("Outcomes "))
    lean_ref = lean if re.fullmatch(r"[A-Za-z_][\w']*", lean) else f"«{lean}»"
    cert = d / "Cert.lean"
    src_f, tgt_f = f"{NS}.Src.{lean_ref}", f"{NS}.Tgt.{lean_ref}"
    imports = [f"{NS}.Src", f"{NS}.Tgt"]
    cert.write_text(proof(NS, src_f, tgt_f, sigs[0][0], imports, "\n".join(modules), chooses))
    bundle = d / "bundle"
    t0 = time.time()
    record = [
        sys.executable,
        str(BINDING_PY),
        "record",
        "--input",
        str(work / "pairs" / pair["id"] / "input.ll"),
        "--passes",
        pair["spec"],
        "--function",
        pair["function"],
        "--certificate",
        str(cert),
        "--theorem",
        THEOREM,
        "--namespace",
        NS,
        "--kind",
        "ir_instance_refinement",
        "--out",
        str(bundle),
        "--timeout",
        str(timeout),
        "--memory",
        str(memory),
    ]
    if pair["mtriple"]:
        record[record.index("--function") : record.index("--function")] = ["--mtriple", pair["mtriple"]]
    code, _, err = sh(record, timeout=timeout * 3)
    if code != 0:
        return {
            **out,
            "gate": "error",
            "reason": "record_failed",
            "detail": err.strip()[-300:],
            "seconds": round(time.time() - t0, 1),
        }
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    argv = [sys.executable, str(BINDING_PY), "verify", str(manifest_path), "--timeout", str(timeout)]
    ran = proc.run([*argv, "--memory", str(memory)], timeout=timeout * 12, cwd=ROOT)
    out["seconds"] = round(time.time() - t0, 1)
    (d / "verdict.json").write_bytes(ran.stdout)
    verdict = record_of(ran)
    if not isinstance(verdict, dict):
        return {**out, "gate": "error", "reason": "verdict_unreadable", "detail": ran.err.strip()[-300:]}
    status = verdict.get("status")
    out.update(
        binding_status=status,
        binding_reason=verdict.get("reason"),
        detail=str(verdict.get("detail", ""))[:300],
    )
    about = (
        manifest["claim"]["function"] == pair["function"]
        and manifest["transform"]["passes"] == pair["spec"]
        and manifest["claim"]["kind"] == "ir_instance_refinement"
        and manifest["artifacts"]["input"]["sha256"] == pair["input_sha256"]
    )
    if status == "bound":
        # irlean.verdict decides, from tools/binding.py's run and verdict, and that the bundle is this pair's.
        decision = core.decide(
            core.Verdict.CERTIFIED,
            core.Evidence(
                upstream=(core.Step.of("tools/binding.py", ran), verdict),
                files={"input": manifest["artifacts"]["input"]["sha256"] == pair["input_sha256"]},
                checks={
                    "about_this_pair": about,
                    "replayed": verdict.get("reason") == "replayed",
                    "refinement": (verdict.get("claim") or {}).get("kind") == "ir_instance_refinement",
                },
            ),
        )
        if decision.granted:
            return {**out, "gate": "bound", "reason": "replayed"}
        return {**out, "gate": "error", "reason": f"verdict_{decision.reason}", "detail": decision.detail}
    return {**out, "gate": status or "error", "reason": verdict.get("reason") or "unknown"}


def eligible(pair: dict) -> bool:
    """What tools/binding.py can bind: an opt run, with no argument that can be undef. Since SEM-07 it binds
    targets with `mustprogress` or `willreturn` too, since the model checks them."""
    return pair["status"] == "candidate" and bool(pair.get("spec")) and not pair["undef_arguments"]


def cmd_certify(args: argparse.Namespace) -> int:
    work: Path = args.work
    pairs = {p["id"]: p for p in read_jsonl(work / "pairs.jsonl")}
    proved = {r["id"]: r for r in read_jsonl(work / "prove.jsonl") if r["lean"] == "proved"}
    done = {r["id"] for r in read_jsonl(work / "certify.jsonl")}
    keep = sample(work, getattr(args, "upto", None))
    todo = [
        pairs[i]
        for i in sorted(proved)
        if eligible(pairs[i]) and i not in done and (keep is None or i in keep)
    ][: args.limit]
    t0 = time.time()
    with (
        open(work / "certify.jsonl", "a") as f,
        concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool,
    ):
        futures = [
            pool.submit(certify_pair, p, proved[p["id"]], work, args.timeout, args.lean_memory) for p in todo
        ]
        for n, fut in enumerate(concurrent.futures.as_completed(futures), 1):
            f.write(json.dumps(fut.result()) + "\n")
            f.flush()
            if n % 10 == 0:
                print(f"{n}/{len(todo)} bundles, {time.time() - t0:.0f} s", file=sys.stderr)
    counts: dict[str, int] = {}
    for r in read_jsonl(work / "certify.jsonl"):
        counts[f"{r['gate']}:{r['reason']}"] = counts.get(f"{r['gate']}:{r['reason']}", 0) + 1
    print(json.dumps({"seconds": round(time.time() - t0, 1), "counts": counts}, indent=1))
    return 0


# ------------------------------------------------------------------------------------------------------------
# Alive2, through tests/alive.py


@functools.cache
def alive_module() -> Any:
    sys.path.insert(0, str(ROOT / "tests"))
    return load("alive", ROOT / "tests" / "alive.py")


EXAMPLE = re.compile(r"^(i\d+) %(\S+) = (poison|#x([0-9a-f]+) \(.*\))$", re.M)


def alive_pair(pair: dict, work: Path, timeout: int) -> dict:
    a = alive_module()
    a.TIMEOUT_SECONDS = timeout
    d = work / "pairs" / pair["id"]
    t0 = time.time()
    with tempfile.TemporaryDirectory(dir=work) as tmp:
        output = a.run((d / "src.ll").read_text(), (d / "tgt.ll").read_text(), tmp)
    seconds = round(time.time() - t0, 2)
    (work / "alive").mkdir(exist_ok=True)
    (work / "alive" / f"{pair['id']}.txt").write_text(output)
    verdict = a.verdict(output)
    reason = ""
    if verdict == "unknown":
        if "Source function is always UB" in output:
            reason = "src_always_ub"
        elif "didn't finish" in output or re.search(r"\bTimeout\b", output):
            reason = "timeout"
        elif m := re.search(r"^ERROR: (.*)$", output, re.M):
            reason = "error: " + m.group(1)[:120]
        else:
            reason = "other"
    elif verdict == "incorrect":
        m = re.search(r"^ERROR: (.*)$", output, re.M)
        reason = m.group(1)[:120] if m else ""
    with_undef = None
    if pair.get("known") and verdict == "correct":
        # Wrong only when an argument is undef, which IRLean's inputs never are: asked without
        # --disable-undef-input, keeping --fail-src-ub.
        with tempfile.TemporaryDirectory(dir=work) as tmp:
            a_, b_ = Path(tmp) / "a.ll", Path(tmp) / "b.ll"
            a_.write_text((d / "src.ll").read_text())
            b_.write_text((d / "tgt.ll").read_text())
            code, o, e = sh(
                ["alive-tv", *[f for f in a.FLAGS if f != "--disable-undef-input"], str(a_), str(b_)],
                timeout=timeout,
            )
        with_undef = a.verdict(o + e) if code is not None else "unknown"
    example = {}
    if verdict == "incorrect" and "Example:" in output:
        block = output.split("Example:", 1)[1].split("\nSource:", 1)[0]
        for m in EXAMPLE.finditer(block):
            example[m.group(2)] = "poison" if m.group(3) == "poison" else int(m.group(4), 16)
    return {
        "id": pair["id"],
        "alive": verdict,
        "reason": reason,
        "seconds": seconds,
        "example": example,
        "with_undef": with_undef,
    }


def cmd_alive(args: argparse.Namespace) -> int:
    work: Path = args.work
    wanted = ("candidate",) if getattr(args, "candidates_only", False) else ("candidate", "unsupported")
    pairs = [p for p in read_jsonl(work / "pairs.jsonl") if p["status"] in wanted]
    done = {r["id"] for r in read_jsonl(work / "alive.jsonl")}
    keep = sample(work, getattr(args, "upto", None))
    todo = sorted(
        (p for p in pairs if p["id"] not in done and (keep is None or p["id"] in keep)), key=lambda p: p["id"]
    )[: args.limit]
    t0 = time.time()
    with (
        open(work / "alive.jsonl", "a") as f,
        concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool,
    ):
        for n, r in enumerate(pool.map(lambda p: alive_pair(p, work, args.timeout), todo), 1):
            f.write(json.dumps(r) + "\n")
            f.flush()
            if n % 100 == 0:
                print(f"{n}/{len(todo)} pairs, {time.time() - t0:.0f} s", file=sys.stderr)
    counts: dict[str, int] = {}
    for r in read_jsonl(work / "alive.jsonl"):
        k = f"{r['alive']}:{r['reason'] if r['alive'] == 'unknown' else ''}"
        counts[k] = counts.get(k, 0) + 1
    print(json.dumps({"seconds": round(time.time() - t0, 1), "counts": counts}, indent=1))
    return 0


# ------------------------------------------------------------------------------------------------------------
# Refutations: the model run on inputs, through tools/verify.py


# Read from the model by irlean.model, so a reason or a stop added to IRLean is never left out here.
MODEL_STOPS = model.model_stops()
UB_REASONS = model.ub_reasons()
RETURNS = "IRLean.andThen ({0}) (fun _ => IRLean.Outcome.ok ()) = IRLean.Outcome.ok ()"
# The decidable claim of tests/verify_negative.py, over every reason IRLean.UB has: undefined behavior in the
# source allows anything, a run that never ends only another, a poison result any result, and a value itself.
# The same for a vector result, lane by lane, without a `match`, which a statement can't hold: a poison lane
# in the source allows any lane in the target there.
LANES = (
    "(List.range {n}).all (fun i => (IRLean.Vec.lane v i).isNone || "
    "IRLean.Vec.lane u i == IRLean.Vec.lane v i)"
)
VEC_REFINES = " ∨ ".join(
    [
        "(∃ r ∈ [" + ", ".join(f"IRLean.UB.{r}" for r in UB_REASONS) + "], {src} = IRLean.Outcome.ub r)",
        "({src} = Option.none ∧ {tgt} = Option.none)",
        "IRLean.andThen ({src}) (fun v => IRLean.andThen ({tgt}) (fun u => if "
        + LANES
        + " then IRLean.Outcome.ok () else IRLean.Outcome.ub IRLean.UB.unreachable)) = IRLean.Outcome.ok ()",
    ]
)
REFINES = " ∨ ".join(
    [
        "(∃ r ∈ [" + ", ".join(f"IRLean.UB.{r}" for r in UB_REASONS) + "], {src} = IRLean.Outcome.ub r)",
        "({src} = Option.none ∧ {tgt} = Option.none)",
        "({src} = IRLean.Outcome.ok Option.none ∧ " + RETURNS.format("{tgt}") + ")",
        "({src} ≠ IRLean.Outcome.ok Option.none ∧ " + RETURNS.format("{src}") + " ∧ {tgt} = {src})",
    ]
)


def edge_values(w: int) -> list[int | None]:
    top = (1 << w) - 1
    vals = [0, 1, top, 1 << (w - 1), (1 << (w - 1)) - 1, 2, top - 1]
    return [None, *sorted({v & top for v in vals})]


VAL = re.compile(r"Val (\d+)")
VEC = re.compile(r"Vec (\d+) (\d+)")
ALIVE_SCALAR = re.compile(r"^i\d+ %(\S+) = (poison|#x([0-9a-f]+) \(.*\))$", re.M)
ALIVE_VECTOR = re.compile(r"^<\d+ x i\d+> %(\S+) = < (.*) >$", re.M)


def alive_example(output: str) -> dict:
    """The inputs of Alive2's counterexample, by argument name: an integer, "poison", or a list of them for a
    vector. Empty if it printed none."""
    if "Example:" not in output:
        return {}
    block = output.split("Example:", 1)[1].split("\nSource:", 1)[0]
    out: dict[str, Any] = {}
    for m in ALIVE_SCALAR.finditer(block):
        out[m.group(1)] = "poison" if m.group(2) == "poison" else int(m.group(3), 16)
    for m in ALIVE_VECTOR.finditer(block):
        lanes = []
        for raw in m.group(2).split(", "):
            lane = raw.strip()
            hexa = re.match(r"#x([0-9a-f]+)", lane)
            if lane == "poison":
                lanes.append("poison")
            elif hexa:
                lanes.append(int(hexa.group(1), 16))
            else:
                break
        else:
            out[m.group(1)] = lanes
    return out


def witnesses(args: list[str], params: list[str], example: dict, limit: int, seed: str) -> list[dict]:
    """Alive2's counterexample first, if it has one, then edge values, at most `limit` in all: every
    combination when there are few, and a seeded sample otherwise. A vector's lanes take values
    independently."""
    shapes = []
    for a in args:
        if m := VAL.fullmatch(a):
            shapes.append((None, int(m.group(1))))
        elif m := VEC.fullmatch(a):
            shapes.append((int(m.group(1)), int(m.group(2))))
        else:
            return []

    def lane(v: Any, w: int) -> str:
        return "none" if v is None or v == "poison" else f"some {v}#{w}"

    def term(v: Any, shape: tuple[int | None, int]) -> str:
        n, w = shape
        return lane(v, w) if n is None else "#v[" + ", ".join(lane(x, w) for x in v) + "]"

    out = []
    if example and all(p in example for p in params):
        values = [example[p] for p in params]
        if all(
            (n is None) != isinstance(v, list) and (n is None or len(v) == n)
            for v, (n, _) in zip(values, shapes, strict=True)
        ):
            out.append({f"x{i}": term(v, s) for i, (v, s) in enumerate(zip(values, shapes, strict=True))})
    slots = [(i, w) for i, (n, w) in enumerate(shapes) for _ in range(n or 1)]
    choices = [edge_values(w) for _, w in slots]
    total = 1
    for c in choices:
        total *= len(c)
    rng = random.Random(seed)
    if total <= 4096:
        grid: list[list[int | None]] = [[]]
        for c in choices:
            grid = [[*g, v] for g in grid for v in c]
        rng.shuffle(grid)
    else:
        grid = [[rng.choice(c) for c in choices] for _ in range(limit)]
    for g in grid[: max(0, limit - len(out))]:
        values, k = [], 0
        for n, _ in shapes:
            values.append(g[k] if n is None else g[k : k + n])
            k += n or 1
        out.append({f"x{i}": term(v, s) for i, (v, s) in enumerate(zip(values, shapes, strict=True))})
    return out


def refute_pair(
    pair: dict, prove: dict, alive: dict | None, work: Path, timeout: int, memory: int, limit: int
) -> dict:
    """The model run on inputs, through tools/verify.py: a counterexample that irlean.verdict grants as
    refuted, and that no model stop explains, is the model's refutation."""
    out: dict[str, Any] = {"id": pair["id"]}
    args = prove.get("args")
    result_type = prove.get("result", "")
    vector_result = re.fullmatch(r"Outcomes? \(Vec (\d+) \d+\)", result_type)
    src_chooses, tgt_chooses = prove.get("chooses") or (False, False)
    if (
        args is None
        or not all(VAL.fullmatch(a) or VEC.fullmatch(a) for a in args)
        or not (re.fullmatch(r"Outcomes? \(Val \d+\)", result_type) or vector_result)
    ):
        return {**out, "refute": "unsupported", "reason": "not_integers_or_vectors"}
    if src_chooses:
        # Refuting needs every way the source chooses to fail, which no witness shows.
        return {**out, "refute": "unsupported", "reason": "source_chooses"}
    d = work / "prove" / pair["id"]
    files = d / "files"
    params = [
        x.split()[-1].lstrip("%")
        for x in B.parameters((work / "pairs" / pair["id"] / "src.ll").read_text(), pair["function"])
    ]
    xs = [f"x{i}" for i in range(len(args))]
    app = " ".join(xs)
    # A target that chooses is refuted by one way of choosing, which is a binder like the inputs.
    src, tgt = f"Opt.src {app}".strip(), f"Opt.tgt {app} ct".replace("  ", " ") if tgt_chooses else ""
    tgt = tgt or f"Opt.tgt {app}".strip()
    text = (
        VEC_REFINES.format(src=src, tgt=tgt, n=vector_result.group(1))
        if vector_result
        else REFINES.format(src=src, tgt=tgt)
    )
    saved = work / "alive" / f"{pair['id']}.txt"
    example = alive_example(saved.read_text()) if saved.exists() else {}
    if args:
        binders = " ".join(f"({x} : IRLean.{a})" for x, a in zip(xs, args, strict=True))
        ws = witnesses(args, params, example, limit, pair["id"])
    else:
        # tools/verify.py decides a statement at a witness, so one with no arguments gets a binder of its own.
        binders, ws = "(u : Unit)", [{"u": "()"}]
    if tgt_chooses:
        binders += " (ct : IRLean.Choice)"
        ws = [{**w, "ct": f"fun _ => {k}"} for w in ws[: max(1, limit // 2)] for k in (0, 1)]
    statement = f"∀ {binders}, {text}"
    request = {
        "input": {"ir": "Opt.ll"},
        "namespace": "Opt",
        "function": "tgt",
        "statement": statement,
        "witnesses": ws,
        "limits": {"timeout_seconds": timeout, "memory_mb": memory},
    }
    harness, _, ran = verify_once(request, files, "refute", d / "refute", timeout)
    result = record_of(ran) or {}
    out.update(
        seconds=harness.seconds,
        witnesses=len(ws),
        from_alive=bool(ws and example),
        verify_status=result.get("status"),
        verify_reason=result.get("reason"),
    )
    status = result.get("status")
    if status == "counterexample":
        refuted = decided(core.Verdict.REFUTED, ran, result, {})
        if not refuted.granted:
            return {**out, "refute": str(refuted.verdict), "reason": f"verdict_{refuted.reason}"}
        assignment = (result.get("counterexample") or {}).get("assignment")
        out["assignment"] = assignment
        # A model stop isn't LLVM's answer, so a counterexample through one says nothing about LLVM:
        # ask whether either side stops the model on that input.
        stops = "[" + ", ".join(f"IRLean.ModelStop.{s}" for s in MODEL_STOPS) + "]"
        stopped = " ∨ ".join(f"(∃ s ∈ {stops}, {f} = IRLean.Outcome.stop s)" for f in (src, tgt))
        probe = {**request, "statement": f"∀ {binders}, ¬({stopped})", "witnesses": [assignment]}
        harness2, _, ran2 = verify_once(probe, files, "stops", d / "stops", timeout)
        pr = record_of(ran2) or {}
        out["seconds"] = round(out["seconds"] + harness2.seconds, 2)
        if decided(core.Verdict.REFUTED, ran2, pr, {}).granted:
            return {**out, "refute": "model_stop", "reason": "a side stops the model on the counterexample"}
        if (
            pr.get("status") == "error"
            and pr.get("reason") == "not_proved"
            and ran2.exit == 1
            and not ran2.limit
        ):
            return {**out, "refute": "refuted", "reason": "witness_falsifies"}
        return {**out, "refute": "unknown", "reason": f"stop probe: {pr.get('status')}/{pr.get('reason')}"}
    if harness.timed_out or status == "timeout":
        return {**out, "refute": "unknown", "reason": result.get("reason") or "harness_timeout"}
    if status == "error" and result.get("reason") == "not_proved":
        return {**out, "refute": "none", "reason": "no_witness_falsifies"}
    return {**out, "refute": status or "error", "reason": result.get("reason") or "unreadable"}


def cmd_refute(args: argparse.Namespace) -> int:
    work: Path = args.work
    if "unknownCallee" not in MODEL_STOPS or "divByZero" not in UB_REASONS:
        sys.exit(
            f"can't read IRLean.UB or IRLean.ModelStop from IRLean/Basic.lean: {UB_REASONS} {MODEL_STOPS}"
        )
    pairs = {p["id"]: p for p in read_jsonl(work / "pairs.jsonl")}
    prove = {r["id"]: r for r in read_jsonl(work / "prove.jsonl")}
    alive = {r["id"]: r for r in read_jsonl(work / "alive.jsonl")}
    done = {r["id"] for r in read_jsonl(work / "refute.jsonl")}
    todo = [
        i
        for i, r in prove.items()
        if (i not in done and r["lean"] in ("failed", "unknown"))
        or (i in alive and alive[i]["alive"] == "incorrect" and r["lean"] != "unsupported" and i not in done)
    ]
    keep = sample(work, getattr(args, "upto", None))
    todo = sorted(i for i in todo if keep is None or i in keep)[: args.limit]
    t0 = time.time()
    with (
        open(work / "refute.jsonl", "a") as f,
        concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool,
    ):
        futures = [
            pool.submit(
                refute_pair,
                pairs[i],
                prove[i],
                alive.get(i),
                work,
                args.timeout,
                args.lean_memory,
                args.witnesses,
            )
            for i in todo
        ]
        for n, fut in enumerate(concurrent.futures.as_completed(futures), 1):
            f.write(json.dumps(fut.result()) + "\n")
            f.flush()
            if n % 25 == 0:
                print(f"{n}/{len(todo)} pairs, {time.time() - t0:.0f} s", file=sys.stderr)
    counts: dict[str, int] = {}
    for r in read_jsonl(work / "refute.jsonl"):
        counts[f"{r['refute']}:{r['reason']}"] = counts.get(f"{r['refute']}:{r['reason']}", 0) + 1
    print(json.dumps({"seconds": round(time.time() - t0, 1), "counts": counts}, indent=1))
    return 0


# ------------------------------------------------------------------------------------------------------------
# The report

LEAN_ORDER = ["certified", "proved", "refuted", "no_verdict", "unknown", "unsupported", "error"]
ALIVE_ORDER = ["correct", "incorrect", "src_always_ub", "timeout", "incomplete", "unsupported", "not_run"]


def lean_verdict(pair: dict, prove: dict | None, cert: dict | None, refute: dict | None) -> tuple[str, str]:
    """One verdict per pair, from the gates only. `certified` is a bound certificate. `proved` is a theorem
    tools/verify.py checked and the negative-verification gate accepted, for every input that's a value or
    poison, which isn't a certificate: an undef argument isn't covered. `refuted` is the model's
    counterexample, decided by running it."""
    if pair["status"] == "unsupported":
        return "unsupported", pair["reason"]
    if pair["status"] != "candidate" or prove is None:
        return "error", pair.get("reason") or "not_run"
    if cert is not None and cert["gate"] == "bound":
        return "certified", "bound"
    if prove["lean"] == "proved":
        return "proved", "kernel_checked"
    if refute is not None and refute["refute"] == "refuted":
        return "refuted", "witness_falsifies"
    if refute is not None and refute["refute"] == "model_stop":
        return "unsupported", "model_stop"
    if prove["lean"] == "failed":
        return "no_verdict", "proof_not_found"
    if prove["lean"] in ("unknown", "unsupported", "error"):
        return prove["lean"], prove["reason"]
    return "error", "unclassified"


def alive_column(a: dict | None) -> str:
    if a is None:
        return "not_run"
    if a["alive"] in ("correct", "incorrect"):
        return a["alive"]
    if a["reason"] == "src_always_ub":
        return "src_always_ub"
    if a["reason"] == "timeout":
        return "timeout"
    if re.match(r"error: (Unsupported|Could not translate)", a["reason"]):
        return "unsupported"
    # It approximated something and couldn't decide, or its solver gave up.
    return "incomplete"


def explain(lean: str, lean_reason: str, alive: str) -> str | None:
    """The kind of a disagreement, or None where the two agree or neither has a verdict. `investigate` is one
    to explain by hand: a model bug or an Alive2 bug."""
    definite_lean = lean in ("certified", "proved", "refuted")
    definite_alive = alive in ("correct", "incorrect")
    proof = lean in ("certified", "proved")
    if (proof and alive == "correct") or (lean == "refuted" and alive == "incorrect"):
        return None
    # A source always undefined allows any target, so the model refuting it there is a disagreement too.
    if (proof and alive == "incorrect") or (lean == "refuted" and alive in ("correct", "src_always_ub")):
        return "investigate"
    if definite_lean and alive == "timeout":
        return "alive2_timeout"
    if definite_lean and alive == "src_always_ub":
        return "source_always_ub"
    if definite_lean and alive == "incomplete":
        return "alive2_incomplete"
    if definite_lean and alive == "unsupported":
        return "alive2_unsupported"
    if lean == "unsupported" and definite_alive:
        return "unsupported"
    if lean in ("no_verdict", "unknown", "error") and alive == "incorrect":
        return "investigate"
    if lean in ("no_verdict", "unknown") and alive == "correct":
        return "lean_no_proof"
    return None


def toolchain() -> dict:
    def version(argv: list[str]) -> str:
        code, out, err = sh(argv, timeout=30)
        return ((out + err).strip().splitlines() or ["unknown"])[0] if code is not None else "unknown"

    def file_sha(name: str) -> str:
        path = Path(os.path.realpath(sh(["which", name])[1].strip() or name))
        return sha(path.read_bytes()) if path.is_file() else "missing"

    v = VN.load_verify()
    _, head, _ = sh(["git", "-C", str(ROOT), "rev-parse", "HEAD"])
    _, dirty, _ = sh(
        ["git", "-C", str(ROOT), "status", "--porcelain", "--", "src", "IRLean", "tools", "tests", "bench"]
    )
    lean_bin = (
        Path(
            sh(
                ["lean", "--print-prefix"],
                env={"ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip()},
            )[1].strip()
        )
        / "bin"
        / "lean"
    )
    opt_v = sh(["opt", "--version"])[1]
    return {
        "repo_commit": head.strip(),
        "repo_dirty": bool(dirty.strip()),
        "llvm_project": B.llvm_pin(),
        "opt": {
            "version": (re.search(r"LLVM version (\S+)", opt_v) or [None, "unknown"])[1],
            "sha256": file_sha("opt"),
        },
        "llvm_extract_sha256": file_sha("llvm-extract"),
        "llvm_link_sha256": file_sha("llvm-link"),
        "alive_tv": {
            "path": os.path.realpath(sh(["which", "alive-tv"])[1].strip()),
            "sha256": file_sha("alive-tv"),
            "flags": list(alive_module().FLAGS),
        },
        "llubi_sha256": file_sha("llubi"),
        "lean": {
            "version": version([str(lean_bin), "--version"]),
            "sha256": sha(lean_bin.read_bytes()) if lean_bin.is_file() else "missing",
        },
        "ir_lean_binary_sha256": sha(TOOL.read_bytes()),
        "irlean_library_sha256": v.library_hash(),
        "checkers_sha256": {
            **VN.checker_hashes(),
            "tools/binding.py": sha(BINDING_PY.read_bytes()),
            "tests/verify_negative.py": sha((ROOT / "tests" / "verify_negative.py").read_bytes()),
            "tests/alive.py": sha((ROOT / "tests" / "alive.py").read_bytes()),
            "bench/instcombine/stage1.py": sha(Path(__file__).read_bytes()),
        },
    }


def stats(values: list[Any]) -> dict:
    xs = sorted(float(x) for x in values if x is not None)
    if not xs:
        return {"n": 0}
    return {
        "n": len(xs),
        "total_s": round(sum(xs), 1),
        "median_s": round(xs[len(xs) // 2], 2),
        "p90_s": round(xs[int(len(xs) * 0.9)], 2),
        "max_s": round(xs[-1], 2),
    }


# Why the emitter refuses a function, grouped by feature. The emitter names one reason per function, the first
# it meets, so these are exclusive, in this order: a reason matching an earlier group counts there.
REFUSAL_GROUPS = [
    ("emitter gave no report, crashed", r"^emitter gave no report"),
    ("undef", r"^undef\b"),
    ("scalable vectors", r"vscale"),
    (
        "floating point",
        r"\b(float|double|half|bfloat|fp128|x86_fp80|ppc_fp128)\b|denormal_fpenv|strictfp|"
        r"amdgpu-ieee|\bf(add|sub|mul|div|rem|neg|cmp)\b|\bfp(ext|trunc|tosi|toui)\b|\b[su]itofp\b",
    ),
    (
        "target intrinsics",
        r"^intrinsic llvm\.(x86|amdgcn|aarch64|arm|nvvm|ppc|wasm|riscv|hexagon|s390|r600|spv|dx)\.",
    ),
    ("other intrinsics", r"^intrinsic "),
    ("division or remainder on vectors", r"^instruction .*\b[su](div|rem) <"),
    ("atomics", r"\b(atomicrmw|cmpxchg|fence)\b|\batomic\b"),
    ("metadata", r"^metadata"),
    ("constant expressions", r"^constant"),
    ("calls outside the module", r"^call to external|^variadic call|^call attribute|^call through"),
    ("attributes on vectors", r"on a vector"),
    ("vector casts and pointer vectors", r"bitcast <|bitcast .* to <|<\d+ x ptr>"),
    ("pointers: address spaces, inttoptr, external globals", r"addrspace|inttoptr|external global|ptrtoaddr"),
    ("data layouts", r"^data layout"),
    ("other attributes", r"attribute"),
    ("exceptions", r"exception"),
    ("other instructions", r"^instruction"),
    ("other types", r"^type"),
]
FEATURES = [
    ("floating point", r"\b(float|double|half|bfloat|fp128|x86_fp80|ppc_fp128)\b"),
    ("vectors", r"<\s*(vscale\s+x\s+)?\d+\s+x\s"),
    ("scalable vectors", r"<\s*vscale\s+x"),
    ("undef", r"\bundef\b"),
    ("calls to a declared function", r"\bcall\b[^\n]*@(?!llvm\.)"),
    ("target intrinsics", r"@llvm\.(x86|amdgcn|aarch64|arm|nvvm|ppc|wasm|riscv)\."),
    ("pointers", r"\bptr\b"),
    ("memory instructions", r"\b(load|store|alloca|getelementptr|memcpy|memset|memmove)\b"),
]


def refusals(work: Path, pairs: list[dict]) -> dict:
    refused = [p for p in pairs if p["status"] == "unsupported" and p["reason"] == "emitter"]
    groups: dict[str, int] = {name: 0 for name, _ in REFUSAL_GROUPS}
    groups["other"] = 0
    reasons: dict[str, int] = {}
    features = {name: 0 for name, _ in FEATURES}
    for p in refused:
        side = "src" if p["emitter"]["src"] != "ok" else "tgt"
        # No row for the function means ir-lean --report failed on the module, such as by crashing.
        reason = (
            p["emitter_detail"][side].split("\t")[-1].strip()
            if p["emitter"][side] != "missing"
            else "emitter gave no report"
        )
        key = re.sub(r"\b\d+\b", "N", re.sub(r"%[-\w.$\"]+", "%v", re.sub(r"@[-\w.$\"]+", "@F", reason)))[:80]
        reasons[key] = reasons.get(key, 0) + 1
        group = next((name for name, rx in REFUSAL_GROUPS if re.search(rx, reason)), "other")
        groups[group] += 1
        src = work / "pairs" / p["id"] / "src.ll"
        body = (func_text(src.read_text(), p["function"]) or "") if src.exists() else ""
        for name, rx in FEATURES:
            features[name] += bool(re.search(rx, body))
    return {
        "functions": len(refused),
        "by_first_reason": dict(sorted(groups.items(), key=lambda kv: -kv[1])),
        "commonest_reasons": dict(sorted(reasons.items(), key=lambda kv: -kv[1])[:40]),
        "features_in_the_source": features,
    }


def summarize(work: Path, upto: int | None = None) -> dict:
    """Every count. The tests, the pairs and why the emitter refuses some are about every pair; the verdicts,
    the matrix and the costs are about the sample, when `upto` gives one."""
    tests = read_jsonl(work / "tests.jsonl")
    pairs = read_jsonl(work / "pairs.jsonl")
    keep = sample(work, upto)

    def kept(path: Path) -> dict[str, dict]:
        return {r["id"]: r for r in read_jsonl(path) if keep is None or r["id"] in keep}

    prove, cert = kept(work / "prove.jsonl"), kept(work / "certify.jsonl")
    alive, refute = kept(work / "alive.jsonl"), kept(work / "refute.jsonl")

    def count(items: Any) -> dict:
        out: dict[str, int] = {}
        for k in items:
            out[k] = out.get(k, 0) + 1
        return dict(sorted(out.items(), key=lambda kv: -kv[1]))

    rows = [r for r in rows_of(work) if keep is None or r["id"] in keep]
    matrix = {lv: dict.fromkeys(ALIVE_ORDER, 0) for lv in LEAN_ORDER}
    for r in rows:
        matrix[r["lean"]][r["alive"]] += 1
    candidates = [p for p in pairs if p["status"] == "candidate"]
    measured = read_jsonl(work / "stages.jsonl")
    known = [r for r in rows if r["known"]]
    soundness = (
        {
            "pairs": len(known),
            "by_kind": count(f"{r['known_kind']}:{r['known_wrong']}" for r in known),
            "lean_on_confirmed_wrong": count(r["lean"] for r in known if r["known_wrong"] == "wrong"),
            "lean_on_wrong_only_with_undef": count(
                r["lean"] for r in known if r["known_wrong"] == "wrong_only_with_undef"
            ),
            "lean_on_not_confirmed": count(r["lean"] for r in known if r["known_wrong"] == "not_confirmed"),
            # A certificate for any known-wrong rewrite, or a proof of one that's wrong without undef, is a
            # model bug or a gate bug until shown otherwise.
            "violations": [
                r
                for r in known
                if (r["known_wrong"] in ("wrong", "wrong_only_with_undef") and r["lean"] == "certified")
                or (r["known_wrong"] == "wrong" and r["lean"] == "proved")
            ],
            "cases": len({r["known"] for r in known}),
        }
        if known
        else None
    )
    return {
        "schema": SUMMARY_SCHEMA,
        "tests": {
            "count": len(tests),
            "status": count(t["status"] for t in tests),
            "specs": count(t["spec"] for t in tests if t["status"] == "ok"),
        },
        "functions": {
            "defined": sum(t.get("functions", 0) for t in tests),
            "changed_by_the_test_run": sum(t.get("changed", 0) for t in tests),
        },
        "sample": None
        if keep is None
        else {
            "pairs": len(keep),
            "of": sum(1 for p in pairs if p["status"] in ("candidate", "unsupported")),
            "candidates": sum(1 for p in pairs if p["id"] in keep and p["status"] == "candidate"),
            "how": "the first pairs by id, a SHA-256 of test and function: a uniform sample",
        },
        "emitter_refusals": refusals(work, pairs),
        "pairs": {
            "status": count(f"{p['status']}:{p['reason']}" for p in pairs),
            "candidates": len(candidates),
            "candidates_with_undef_arguments": sum(1 for p in candidates if p["undef_arguments"]),
            "candidates_with_a_promise_in_the_target": sum(1 for p in candidates if p["trusted_promise"]),
            "candidates_with_a_promise_on_the_function": sum(
                1 for p in candidates if p["trusted_promise_in_function"]
            ),
            "candidates_with_vectors": sum(1 for p in candidates if p["vector"]),
            "certificate_eligible": sum(1 for p in candidates if eligible(p)),
        },
        "prove": count(f"{r['lean']}:{r['reason']}" for r in prove.values()),
        "certify": count(f"{r['gate']}:{r['reason']}" for r in cert.values()),
        "refute": count(f"{r['refute']}:{r['reason']}" for r in refute.values()),
        "alive": count(
            f"{r['alive']}:{r['reason'] if r['alive'] != 'correct' else ''}"[:90] for r in alive.values()
        ),
        "verdicts": {"lean": count(r["lean"] for r in rows), "alive": count(r["alive"] for r in rows)},
        "matrix": matrix,
        "soundness": soundness,
        "compared": sum(1 for r in rows if r["lean"] != "error" and r["alive"] != "not_run"),
        "disagreements": count(r["kind"] for r in rows if r["kind"]),
        "to_investigate": [r for r in rows if r["kind"] == "investigate"],
        "cost": {
            "prove": stats([r.get("seconds") for r in prove.values()]),
            "certify": stats([r.get("seconds") for r in cert.values()]),
            "alive": stats([r.get("seconds") for r in alive.values()]),
            "refute": stats([r.get("seconds") for r in refute.values()]),
            "stages": measured,
        },
    }


def cmd_report(args: argparse.Namespace) -> int:
    work: Path = args.work
    summary = summarize(work, getattr(args, "upto", None))
    summary["toolchain"] = toolchain()
    (work / "rows.jsonl").write_text("")
    out = args.out or work / "summary.json"
    Path(out).write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n")
    print(
        json.dumps(
            {
                k: summary[k]
                for k in (
                    "tests",
                    "functions",
                    "pairs",
                    "prove",
                    "certify",
                    "refute",
                    "alive",
                    "verdicts",
                    "matrix",
                    "compared",
                    "disagreements",
                )
            },
            indent=1,
        )
    )
    print(f"wrote {out}", file=sys.stderr)
    return 0


def cmd_all(args: argparse.Namespace) -> int:
    """Every stage in order, each timed, into WORK/stages.jsonl."""
    stages = [
        ("pairs", cmd_pairs),
        ("prove", cmd_prove),
        ("certify", cmd_certify),
        ("alive", cmd_alive),
        ("refute", cmd_refute),
    ]
    if args.skip_pairs:
        stages = stages[1:]
    for name, fn in stages:
        t0 = time.time()
        sub = argparse.Namespace(**vars(args))
        sub.jobs = {
            "pairs": 8,
            "prove": args.lean_jobs,
            "certify": args.certify_jobs,
            "alive": args.alive_jobs,
            "refute": args.lean_jobs,
        }[name]
        sub.timeout = {"prove": 120, "certify": 300, "alive": 120, "refute": 300}.get(name, 120)
        sub.lean_memory = {"certify": 3000}.get(name, 4000)
        code = fn(sub)
        with open(args.work / "stages.jsonl", "a") as f:
            f.write(
                json.dumps(
                    {"stage": name, "seconds": round(time.time() - t0, 1), "jobs": sub.jobs, "exit": code}
                )
                + "\n"
            )
        if code:
            return code
    return cmd_report(argparse.Namespace(work=args.work, out=None))


# ------------------------------------------------------------------------------------------------------------
# Known miscompilations

KNOWN = Path(__file__).resolve().parent / "known_wrong.json"
KNOWN_SCHEMA = schemas.STAGE1_KNOWN_WRONG
DASHBOARD = "https://web.ist.utl.pt/nuno.lopes/alive2/index.php"
DASHBOARD_RUN = "c3466a6048874dbf"
SHORTLINK = "https://alive2.llvm.org/ce/api/shortlinkinfo/"
FAMILY = r'"?(instcombine|instsimplify|aggressive-instcombine)(<[^>]*>)?"?'


def fetch(url: str) -> bytes:
    ran = proc.run(["curl", "-sS", "-f", "-m", "60", url], timeout=90)
    if not ran.ok:
        raise RuntimeError(f"{url}: {ran.err[-200:]}")
    time.sleep(0.3)
    return ran.stdout


def without_function(ll: str, name: str) -> str:
    return re.sub(rf"^define [^@]*@{re.escape(name)}\(.*?^}}\n?", "", ll, flags=re.M | re.S)


def cmd_known_fetch(args: argparse.Namespace) -> int:
    """Downloads what the corpus is built from: LLVM's issues labeled miscompilation and llvm:instcombine,
    the Alive2 explorer sessions they link, and Alive2's dashboard run of 2026-01-29, with each failing test's
    log."""
    import html
    import urllib.parse

    raw = args.work / "known" / "raw"
    (raw / "links").mkdir(parents=True, exist_ok=True)
    (raw / "dashboard").mkdir(parents=True, exist_ok=True)
    argv = ["gh", "issue", "list", "-R", "llvm/llvm-project", "--label", "miscompilation", "--label"]
    argv += ["llvm:instcombine", "--state", "all", "--limit", "1000"]
    listed = proc.run([*argv, "--json", "number,title,body,url,state,createdAt"], timeout=300)
    if not listed.ok:
        sys.exit(f"gh issue list failed: {listed.err[-300:]}")
    issues = json.loads(listed.out)
    (raw / "issues.json").write_text(json.dumps(issues, indent=0))
    for issue in issues:
        for link in sorted(set(re.findall(r"alive2\.llvm\.org/ce/z/([A-Za-z0-9_-]+)", issue["body"]))):
            out = raw / "links" / f"{link}.json"
            if not out.exists():
                out.write_bytes(fetch(SHORTLINK + link))
    page = fetch(f"{DASHBOARD}?hash={DASHBOARD_RUN}").decode(errors="replace")
    (raw / "dashboard.html").write_text(page)
    for test in sorted(set(re.findall(r"test=(Transforms%2F[^\"&]+)", page))):
        name = urllib.parse.unquote(test)
        out = raw / "dashboard" / (name.replace("/", "__") + ".txt")
        if not out.exists():
            text = fetch(f"{DASHBOARD}?hash={DASHBOARD_RUN}&test={test}").decode(errors="replace")
            out.write_text(html.unescape(re.sub(r"<[^>]+>", "", text)))
    print(
        f"{len(issues)} issues, {len(list((raw / 'links').iterdir()))} sessions, "
        f"{len(list((raw / 'dashboard').iterdir()))} dashboard tests"
    )
    return 0


def cmd_known_build(args: argparse.Namespace) -> int:
    """Writes known_wrong.json from what known-fetch downloaded. Issue cases keep their IR, since an issue
    can be edited. Dashboard cases name a test in the pinned llvm-project and the functions Alive2 failed in
    it."""
    raw = args.work / "known" / "raw"
    issues = json.loads((raw / "issues.json").read_text())
    cases = []
    seen = set()
    for issue in sorted(issues, key=lambda i: i["number"]):
        sources = []
        for link in sorted(set(re.findall(r"alive2\.llvm\.org/ce/z/([A-Za-z0-9_-]+)", issue["body"]))):
            path = raw / "links" / f"{link}.json"
            try:
                session = json.loads(path.read_text())["sessions"][0]
            except (OSError, ValueError, KeyError, IndexError):
                continue
            options = " ".join(c.get("options", "") for c in session.get("compilers", []))
            sources.append((f"https://alive2.llvm.org/ce/z/{link}", session["source"], options))
        for block in re.findall(r"```[a-z]*\n(.*?)```", issue["body"], re.S):
            if re.search(r"^define [^@]*@src\(", block, re.M) and re.search(
                r"^define [^@]*@tgt\(", block, re.M
            ):
                sources.append((issue["url"], block, ""))
        for where, source, options in sources:
            if sha(source) in seen:
                continue
            seen.add(sha(source))
            base = {
                "issue": issue["number"],
                "title": issue["title"][:120],
                "state": issue["state"],
                "from": where,
            }
            has_pair = re.search(r"^define [^@]*@src\(", source, re.M) and re.search(
                r"^define [^@]*@tgt\(", source, re.M
            )
            passes = re.search(rf"-passes={FAMILY}(?:\s|$)", options)
            if has_pair:
                cases.append({**base, "kind": "issue_pair", "ir": source})
            elif passes:
                cases.append(
                    {
                        **base,
                        "kind": "issue_reproducer",
                        "ir": source,
                        "spec": passes.group(0).split("=", 1)[1].strip().strip('"'),
                    }
                )
    for path in sorted((raw / "dashboard").iterdir()):
        text = path.read_text(errors="replace")
        test = "llvm/test/" + path.name.removesuffix(".txt").replace("__", "/")
        failing = []
        for part in text.split("-" * 40):
            if "Transformation doesn't verify!" in part:
                m = re.search(r'^define [^@]*@("[^"]+"|[-\w.$]+)\(', part, re.M)
                if m:
                    failing.append(m.group(1).strip('"'))
        if failing:
            cases.append(
                {
                    "kind": "dashboard",
                    "test": test,
                    "functions": sorted(set(failing)),
                    "from": f"{DASHBOARD}?hash={DASHBOARD_RUN}",
                }
            )
    for c in cases:
        c["id"] = sha(json.dumps(c, sort_keys=True))[:16]
    KNOWN.write_text(
        json.dumps(
            {
                "schema": KNOWN_SCHEMA,
                "sources": {
                    "issues": "llvm/llvm-project issues labeled miscompilation and "
                    "llvm:instcombine, fetched 2026-11-08",
                    "dashboard": f"Alive2's run of LLVM 8a4244b560f3 on 2026-01-29, "
                    f"{DASHBOARD}?hash={DASHBOARD_RUN}",
                },
                "cases": cases,
            },
            indent=1,
            ensure_ascii=False,
        )
        + "\n"
    )
    counts: dict[str, int] = {}
    for c in cases:
        counts[str(c["kind"])] = counts.get(str(c["kind"]), 0) + 1
    print(json.dumps(counts), f"{KNOWN.stat().st_size // 1024} KiB")
    return 0


def split_pair(ll: str) -> tuple[str, str]:
    """A module with @src and @tgt, as two modules whose function is @f."""
    src = rename(without_function(ll, "tgt"), "src", "f")
    tgt = rename(without_function(ll, "src"), "tgt", "f")
    return src, tgt


def known_pair(case: dict, work: Path) -> list[dict]:
    """The pairs one case gives: an issue's own pair, or what the pinned opt does to a reproducer or test."""
    out = []
    if case["kind"] == "issue_pair":
        pid = case["id"]
        d = work / "pairs" / pid
        d.mkdir(parents=True, exist_ok=True)
        rec: dict[str, Any] = {
            "schema": SCHEMA,
            "id": pid,
            "test": f"issue {case['issue']}",
            "function": "f",
            "spec": None,
            "mtriple": None,
            "known": case["id"],
            "known_kind": case["kind"],
        }
        a, b = split_pair(case["ir"])
        src, why_a = opt(a, "verify", None)
        tgt, why_b = opt(b, "verify", None)
        if src is None or tgt is None:
            return [{**rec, "status": "error", "reason": "opt_rejects", "detail": why_a or why_b}]
        (d / "input.ll").write_text(src)
        (d / "src.ll").write_text(src)
        (d / "tgt.ll").write_text(tgt)
        rec.update(input_sha256=sha(src), src_sha256=sha(src), tgt_sha256=sha(tgt))
        return [classify(rec, d, src, tgt, "f")]
    if case["kind"] == "issue_reproducer":
        text, spec, mtriple = case["ir"], case["spec"], None
        test = f"issue {case['issue']}"
        wanted = None
    else:
        path = llvm_tests().parent.parent.parent / case["test"]
        if not path.exists():
            return [
                {
                    "schema": SCHEMA,
                    "id": case["id"],
                    "test": case["test"],
                    "function": "",
                    "status": "error",
                    "reason": "test_missing_at_pin",
                    "known": case["id"],
                    "known_kind": case["kind"],
                }
            ]
        text = path.read_text(errors="replace")
        spec, mtriple, _ = run_spec_any(text)
        test = case["test"]
        wanted = set(case["functions"])
    src_all, why = opt(text, "verify", mtriple)
    if src_all is None:
        return [
            {
                "schema": SCHEMA,
                "id": case["id"],
                "test": test,
                "function": "",
                "status": "error",
                "reason": "opt_rejects",
                "detail": why,
                "known": case["id"],
                "known_kind": case["kind"],
            }
        ]
    tgt_all, why = opt(src_all, spec, mtriple)
    if tgt_all is None:
        return [
            {
                "schema": SCHEMA,
                "id": case["id"],
                "test": test,
                "function": "",
                "status": "error",
                "reason": "opt_failed",
                "detail": why,
                "known": case["id"],
                "known_kind": case["kind"],
            }
        ]
    for f in names(src_all):
        if wanted is not None and f not in wanted:
            continue
        if func_text(src_all, f) == func_text(tgt_all, f):
            out.append(
                {
                    "schema": SCHEMA,
                    "id": pair_id(test + case["id"], f),
                    "test": test,
                    "function": f,
                    "spec": spec,
                    "status": "skipped",
                    "reason": "unchanged_at_pin",
                    "known": case["id"],
                    "known_kind": case["kind"],
                }
            )
            continue
        r = make_pair(test + "#" + case["id"], f, src_all, spec, mtriple, work)
        out.append({**r, "test": test, "known": case["id"], "known_kind": case["kind"]})
    return out


def run_spec_any(text: str) -> tuple[str, str | None, list[str]]:
    """The first RUN line's single pass, for a dashboard test of any pass. Falls back to instcombine's."""
    for m in RUN_LINE.finditer(text):
        found = re.search(r"-passes=['\"]?([\w-]+(?:<[^>]*>)?)['\"]?(?:\s|$)", m.group(1))
        if found:
            mt = re.search(r"-mtriple[= ](\S+)", m.group(1))
            return found.group(1), mt.group(1) if mt else None, []
    return run_spec(text)


def classify(rec: dict, d: Path, src: str, tgt: str, function: str) -> dict:
    rows = {side: report_row(d / f"{side}.ll", function) for side in ("src", "tgt")}
    rec["emitter"] = {side: (row[0] if row else "missing") for side, row in rows.items()}
    rec["emitter_detail"] = {side: "\t".join(row[2:]) if row else "" for side, row in rows.items()}
    rec["signature"] = rows["src"][3] if rows["src"] and rows["src"][0] == "ok" else None
    rec["lean_name"] = rows["src"][2] if rows["src"] and rows["src"][0] == "ok" else None
    rec["pure"] = all(row is not None and row[0] == "ok" and row[-1] == "pure" for row in rows.values())
    loose = [
        x
        for x in B.parameters(src, function)
        if not re.search(r"\bnoundef\b", re.sub(r'%"[^"]*"|%[-\w.$]+|"[^"]*"', "", x))
    ]
    rec["undef_arguments"] = len(loose)
    rec["trusted_promise"] = bool(PROMISES.search(tgt))
    rec["trusted_promise_in_function"] = bool(PROMISES.search(func_text(tgt, function) or ""))
    rec["vector"] = bool(rec["signature"] and "<" in rec["signature"])
    if any(rec["emitter"][s] != "ok" for s in ("src", "tgt")):
        return {**rec, "status": "unsupported", "reason": "emitter"}
    if not rec["pure"]:
        return {**rec, "status": "unsupported", "reason": "memory"}
    return {**rec, "status": "candidate", "reason": ""}


def cmd_known_pairs(args: argparse.Namespace) -> int:
    work: Path = args.work
    work.mkdir(parents=True, exist_ok=True)
    corpus = json.loads(Path(getattr(args, "corpus", None) or KNOWN).read_text())
    assert corpus["schema"] == KNOWN_SCHEMA
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pairs = [p for ps in pool.map(lambda c: known_pair(c, work), corpus["cases"]) for p in ps]
    append = getattr(args, "append", False)
    with open(work / "pairs.jsonl", "a" if append else "w") as f:
        for p in pairs:
            f.write(json.dumps(p) + "\n")
    if not append:
        (work / "tests.jsonl").write_text("")
    counts: dict[str, int] = {}
    for p in pairs:
        k = f"{p.get('known_kind')}:{p['status']}:{p['reason']}"
        counts[k] = counts.get(k, 0) + 1
    print(json.dumps(dict(sorted(counts.items())), indent=1))
    return 0


# ------------------------------------------------------------------------------------------------------------
# The CI fixture

FIXTURE = Path(__file__).resolve().parent / "fixture"


def cmd_ci(args: argparse.Namespace) -> int:
    """Every stage on the fixture's few pairs, then each pair's verdicts against fixture/expect.json. Fails if
    a known-wrong rewrite is proved or certified, whatever the expectations say."""
    import shutil

    work: Path = args.work
    # A fresh run, apart from logs a caller keeps there.
    work.mkdir(parents=True, exist_ok=True)
    for entry in work.iterdir():
        if entry.name == "logs":
            continue
        if entry.is_dir():
            shutil.rmtree(entry)
        else:
            entry.unlink()
    t0 = time.time()
    base = {"work": work, "limit": None, "again": False, "witnesses": 16}
    steps = [
        (
            cmd_pairs,
            {"files": sorted(str(f) for f in FIXTURE.glob("*.ll")), "sample": None, "seed": 1, "jobs": 4},
        ),
        (cmd_known_pairs, {"jobs": 4, "corpus": FIXTURE / "known_wrong.json", "append": True}),
        (cmd_prove, {"jobs": 1, "timeout": 120, "lean_memory": 4000}),
        (cmd_certify, {"jobs": 1, "timeout": 300, "lean_memory": 3000}),
        (cmd_alive, {"jobs": 4, "timeout": 120}),
        (cmd_refute, {"jobs": 1, "timeout": 300, "lean_memory": 4000}),
    ]
    for fn, extra in steps:
        if fn(argparse.Namespace(**base, **extra)):
            print(f"FAIL  {fn.__name__} failed")
            return 1
    summary = summarize(work)
    expect = json.loads((FIXTURE / "expect.json").read_text())
    pairs = {p["id"]: p for p in read_jsonl(work / "pairs.jsonl")}
    rows = {
        (pairs[r["id"]]["test"].rsplit("/", 1)[-1], pairs[r["id"]]["function"]): r
        for r in [dict(r) for r in rows_of(work)]
    }
    failed = 0
    for key, want in expect["pairs"].items():
        test, function = key.split(":", 1)
        row = rows.get((test, function))
        if row is None:
            print(f"FAIL  {key}: no such pair")
            failed += 1
            continue
        got = {"lean": row["lean"], "alive": row["alive"]}
        if any(got[k] != v for k, v in want.items() if k in got):
            print(f"FAIL  {key}: {got}, expected {want}")
            failed += 1
        else:
            print(f"ok    {key}: Lean {row['lean']} ({row['lean_reason']}), Alive2 {row['alive']}")
    wrong = [
        r
        for r in rows.values()
        if (r["lean"] == "certified" and r["known_wrong"] in ("wrong", "wrong_only_with_undef"))
        or (r["lean"] == "proved" and r["known_wrong"] == "wrong")
    ]
    for r in wrong:
        print(f"FAIL  a known-wrong rewrite was {r['lean']}: {r['test']} {r['function']}")
        failed += 1
    if len(rows) != len(expect["pairs"]):
        print(f"FAIL  {len(rows)} pairs, and expect.json lists {len(expect['pairs'])}")
        failed += 1
    seen = {k: {c: n for c, n in v.items() if n} for k, v in summary["matrix"].items() if any(v.values())}
    print(
        f"{'FAIL' if failed else 'ok'}    {len(rows)} pairs in {time.time() - t0:.0f} s; "
        f"matrix {json.dumps(seen)}"
    )
    return 1 if failed else 0


def rows_of(work: Path) -> list[dict]:
    pairs = read_jsonl(work / "pairs.jsonl")
    prove = {r["id"]: r for r in read_jsonl(work / "prove.jsonl")}
    cert = {r["id"]: r for r in read_jsonl(work / "certify.jsonl")}
    alive = {r["id"]: r for r in read_jsonl(work / "alive.jsonl")}
    refute = {r["id"]: r for r in read_jsonl(work / "refute.jsonl")}
    out = []
    for p in pairs:
        if p["status"] == "skipped":
            continue
        lean, why = lean_verdict(p, prove.get(p["id"]), cert.get(p["id"]), refute.get(p["id"]))
        col = alive_column(alive.get(p["id"]))
        a = alive.get(p["id"]) or {}
        wrong = None
        if p.get("known"):
            wrong = (
                "wrong"
                if a.get("alive") == "incorrect"
                else "wrong_only_with_undef"
                if a.get("with_undef") == "incorrect"
                else "not_confirmed"
            )
        out.append(
            {
                "id": p["id"],
                "test": p["test"],
                "function": p["function"],
                "known": p.get("known"),
                "known_kind": p.get("known_kind"),
                "known_wrong": wrong,
                "lean": lean,
                "lean_reason": why,
                "alive": col,
                "alive_reason": a.get("reason", ""),
                "kind": explain(lean, why, col),
            }
        )
    return out


RESULTS = Path(__file__).resolve().parent / "results" / "summary.json"


def cmd_publish(args: argparse.Namespace) -> int:
    """Writes results/summary.json, the committed summary: InstCombine's sample, from `report --upto`, and the
    known miscompilations, from `report` on their WORK, each with the toolchain it ran on."""
    sample = json.loads(Path(args.sample).read_text())
    known = json.loads(Path(args.known).read_text())
    for s in (sample, known):
        schemas.check(s, SUMMARY_SCHEMA)
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    out = {"schema": SUMMARY_SCHEMA, "instcombine": sample, "known_wrong": known}
    RESULTS.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {RESULTS.relative_to(ROOT)}, {RESULTS.stat().st_size // 1024} KiB")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--work", type=Path, default=WORK)
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("pairs")
    p.add_argument("--files", nargs="*")
    p.add_argument("--sample", type=int)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--jobs", type=int, default=8)
    p = sub.add_parser("prove")
    p.add_argument("--eligible-only", action="store_true", help="only pairs tools/binding.py can bind")
    p.add_argument("--upto", type=int, help="only the first N changed pairs by id: a uniform sample")
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--lean-memory", type=int, default=4000)
    p.add_argument("--limit", type=int)
    p.add_argument("--again", action="store_true")
    p = sub.add_parser("certify")
    p.add_argument("--upto", type=int, help="only the first N changed pairs by id: a uniform sample")
    p.add_argument("--jobs", type=int, default=2)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--lean-memory", type=int, default=3000)
    p.add_argument("--limit", type=int)
    p = sub.add_parser("alive")
    p.add_argument("--upto", type=int, help="only the first N changed pairs by id: a uniform sample")
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--candidates-only", action="store_true")
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--limit", type=int)
    p = sub.add_parser("refute")
    p.add_argument("--upto", type=int, help="only the first N changed pairs by id: a uniform sample")
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--lean-memory", type=int, default=4000)
    p.add_argument("--witnesses", type=int, default=64)
    p.add_argument("--limit", type=int)
    p = sub.add_parser("all")
    p.add_argument("--files", nargs="*")
    p.add_argument("--sample", type=int)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--skip-pairs", action="store_true")
    p.add_argument("--lean-jobs", type=int, default=4)
    p.add_argument("--certify-jobs", type=int, default=2)
    p.add_argument("--alive-jobs", type=int, default=8)
    p.add_argument("--limit", type=int)
    p.add_argument("--witnesses", type=int, default=64)
    p.add_argument("--again", action="store_true")
    sub.add_parser("known-fetch")
    sub.add_parser("known-build")
    p = sub.add_parser("known-pairs")
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--corpus", type=Path)
    p.add_argument("--append", action="store_true")
    p = sub.add_parser("ci")
    p = sub.add_parser("publish")
    p.add_argument("--sample", type=Path, default=WORK / "summary-4000.json")
    p.add_argument("--known", type=Path, default=ROOT / "build" / "stage1-known" / "summary.json")
    p = sub.add_parser("report")
    p.add_argument("--upto", type=int, help="only the first N changed pairs by id: a uniform sample")
    p.add_argument("--out", type=Path)
    args = ap.parse_args()
    args.work = args.work.resolve()
    return {
        "pairs": cmd_pairs,
        "prove": cmd_prove,
        "certify": cmd_certify,
        "alive": cmd_alive,
        "refute": cmd_refute,
        "report": cmd_report,
        "all": cmd_all,
        "known-fetch": cmd_known_fetch,
        "known-build": cmd_known_build,
        "known-pairs": cmd_known_pairs,
        "publish": cmd_publish,
        "ci": cmd_ci,
    }[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
