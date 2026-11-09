#!/usr/bin/env python3
"""Checks the lemma store, docs/lemma-store.md, and that its checks can fail.

- `tools/store/store.py check` passes: every stored lemma meets the first three rules of the bar and the other
  admission checks, and each module's axioms and kernel replay are checked again, so every lemma is admitted
  or a candidate, and the index says which. The Peephole library's proofs count as uses, and a lemma one of
  its rewrite theorems uses names that rewrite. A module of the library that imports the store is refused.
- Lookup finds a stored lemma under a restatement, by key: variables renamed and reordered, hypotheses
  reordered, `>` for `<`, `not =` for `!=`, the operands of `and` and `or` swapped, and an equation the
  other way round. It finds a lemma whose conclusion becomes a goal at a real width, with its side
  conditions closed. A statement nothing proves finds nothing, and one that doesn't elaborate is an error.
- `store.py add` refuses each lemma in tests/store/must_refuse for the reason it's there, and one of #48's
  lemmas through `--existing`, and accepts tests/store/Admissible.lean, so the refusals aren't the checker
  refusing everything.
- `grind +suggestions` proves two goals from stored lemmas it isn't told the names of, and plain `grind`
  proves neither.
- The reuse example in tests/store/reuse: both proofs of each theorem check, the one from the store rests on
  the standard axioms only and the one without it on `bv_decide`'s, and leanchecker replays both.

Needs `lake build` first. Bounded: Lean runs with a memory cap, two at a time.
usage: tests/store_test.py build/ir-lean
"""

import concurrent.futures
import importlib.util
import json
import os
import re
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc  # noqa: E402

STORE = [sys.executable, str(ROOT / "tools" / "store" / "store.py")]
LIB = ROOT / ".lake" / "build" / "lib" / "lean"
FIXTURES = ROOT / "tests" / "store"
MB = os.environ.get("LEAN_MAX_MB", "4000")
failures: list[str] = []


def report(ok: bool, what: str, detail: str = "") -> None:
    print(f"{'ok  ' if ok else 'FAIL'}  {what}")
    if not ok:
        failures.append(what)
        if detail:
            print(detail[:4000])


def store(*args: str) -> tuple[int, dict]:
    p = proc.run([*STORE, *args, "--json"], cwd=ROOT)
    try:
        return p.exit, json.loads(p.out)
    except json.JSONDecodeError:
        return p.exit, {"status": "unparsed", "stdout": p.out[-3000:], "stderr": p.err[-3000:]}


def lean(args: list[str], *paths: Path) -> tuple[int, str, float]:
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(str(p) for p in (*paths, LIB))}
    p = proc.run(["lean", "-M", MB, *args], cwd=ROOT, env=env)
    return p.exit, p.output, p.seconds


# ------------------------------------------------------------------------------------------------------------
# The store checks


def check_store() -> None:
    code, r = store("check")
    if r.get("status") != "ok" or code != 0:
        refused = [f"{x['name']}: {x['reasons']}" for x in r.get("lemmas", []) if x["status"] == "refused"]
        report(
            False, "the store checks", json.dumps(r.get("drift", r))[:2000] + "\n" + "\n".join(refused)[:2000]
        )
        return
    c = r["counts"]
    report(
        c["refused"] == 0 and c["admitted"] + c["candidate"] == c["lemmas"],
        f"the store checks: {c['lemmas']} lemmas, {c['admitted']} admitted and {c['candidate']} candidates, "
        f"{c['hypotheses_witnessed']} hypotheses each shown needed, in {r['timings']['total_seconds']} s",
    )
    # The Peephole library's proofs count as uses, and each lemma names the rewrites whose theorems use it.
    by_name = {x["name"]: x for x in r["lemmas"]}
    zero = by_name.get("IRLean.Generic.add_zero", {})
    report(
        "IS.simplifyAddInst.L609" in zero.get("rewrites", [])
        and "Peephole.IS.simplifyAddInst.L609" in zero.get("used_by", []),
        "IRLean.Generic.add_zero is used by the theorem of IS.simplifyAddInst.L609, and names that rewrite",
        json.dumps(zero)[:2000],
    )


def check_peephole_cycle() -> None:
    """The store imports the Peephole library's lemma files, so a module of the library that imports the store
    is refused before anything is built."""
    spec = importlib.util.spec_from_file_location("store_tool", STORE[1])
    assert spec is not None and spec.loader is not None
    tool = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tool)
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / "Peephole" / "IS").mkdir(parents=True)
        (Path(tmp) / "Peephole" / "IS" / "Fine.lean").write_text("import Peephole.Term\n")
        (Path(tmp) / "Peephole" / "IS" / "Back.lean").write_text(
            "import Peephole.Term\nimport LemmaStore.Select\n"
        )
        found = tool.peephole_cycles(Path(tmp))
    report(
        found == ["Peephole.IS.Back imports LemmaStore.Select"] and tool.peephole_cycles() == [],
        "a Peephole module that imports the store is refused, and none does",
        str(found),
    )


# ------------------------------------------------------------------------------------------------------------
# Lookup

# (what it is, the statement, the lemma it has to find, by key, and whether the other way round)
RESTATED = [
    (
        "mul_twoPow with variables renamed and reordered, hypotheses reordered, and `>`",
        "∀ (k n : Nat) (nsw nuw : Bool) (v : Val n) (c : BitVec n), nsw = false ∨ k + 1 < n → n > k → "
        "c = BitVec.twoPow n k → Val.mul v (some c) nuw nsw = Val.shl v (some (BitVec.ofNat n k)) nuw nsw",
        "IRLean.Generic.mul_twoPow",
        False,
    ),
    (
        "mul_one with `¬ =` for `≠` and the operands of `∨` swapped",
        "∀ {n : Nat} (v : Val n) (f g : Bool), ¬ n = 1 ∨ g = false → Val.mul v (some 1#n) f g = v",
        "IRLean.Generic.mul_one",
        False,
    ),
    (
        "sdiv_isUB_iff with its variables reordered and the operands of `and` and `or` swapped",
        "∀ {n : Nat} (b a : BitVec n) (e : Bool), Contract.IsUB (Val.sdiv (some a) (some b) e) ↔ "
        "(b = BitVec.allOnes n ∧ a = BitVec.intMin n) ∨ b = 0#n",
        "IRLean.Contract.sdiv_isUB_iff",
        False,
    ),
    (
        "xor_zero the other way round",
        "∀ {n : Nat} (v : Val n), v = Val.xor v (some 0#n)",
        "IRLean.Generic.xor_zero",
        True,
    ),
    (
        "Refines.trans with its hypotheses swapped",
        "∀ {β : Type} [Refine β] {x y z : β}, Refines y z → Refines x y → Refines x z",
        "IRLean.Refines.trans",
        False,
    ),
]

# (what it is, the statement, the lemma whose conclusion it has to be an instance of)
INSTANCES = [
    (
        "`mul nuw nsw i32 %x, 8` to `shl nuw nsw i32 %x, 3`",
        "∀ (x : Val 32), Val.mul x (some 8#32) true true = Val.shl x (some 3#32) true true",
        "IRLean.Generic.mul_twoPow",
    ),
    (
        "`lshr i256 (shl nuw i256 %x, %s), %s` to `%x`",
        "∀ (x s : Val 256), Refines (Val.lshr (Val.shl x s true false) s) x",
        "IRLean.Generic.lshr_shl_nuw_refines",
    ),
]


def check_lookup(what: str, statement: str, name: str, reversed_: bool) -> None:
    code, r = store("lookup", "--statement", statement)
    hits = [m for m in r.get("exact", []) if m["name"] == name and m["reversed"] == reversed_]
    report(
        code == 0 and r.get("status") == "exact" and bool(hits), f"lookup finds {name} by key: {what}", str(r)
    )


def check_instance(what: str, statement: str, name: str) -> None:
    code, r = store("lookup", "--statement", statement)
    hits = [m for m in r.get("instances", []) if m["name"] == name and m["closes"]]
    sides = "; ".join(s["statement"] for m in hits for s in m["side_conditions"])
    report(
        code == 0 and bool(hits),
        f"lookup finds {name} for {what}, with every side condition closed: {sides or 'none'}",
        str(r),
    )


def check_lookup_misses() -> None:
    code, r = store("lookup", "--statement", "∀ (x : Val 8), Val.add x x = x")
    report(code == 3 and r.get("status") == "none", "lookup finds nothing for `add x, x` to `x`", str(r))
    code, r = store("lookup", "--statement", "∀ (x : Val 8), Val.nosuch x = x")
    report(
        code == 1 and r.get("reason") == "statement_invalid",
        "lookup calls a statement that doesn't elaborate an error",
        str(r),
    )


# ------------------------------------------------------------------------------------------------------------
# Admission

# Each fixture, and the reason it has to be refused for, with the rule of the bar that reason enforces.
MUST_REFUSE = {
    "Sorried.lean": "sorry",
    "ExtraAxiom.lean": "nonstandard_axiom",
    "BvDecide.lean": "nonstandard_axiom",
    "FixedWidth.lean": "fixed_width",
    "NoCounterexample.lean": "hypothesis_unwitnessed",
    "SorriedCounterexample.lean": "hypothesis_unwitnessed",
    "Duplicate.lean": "duplicate",
    "FalseStatement.lean": "does_not_check",
}
RESOURCE = re.compile(r"heartbeats|timeout|recursion|stack overflow|memory")


def add(path: Path) -> tuple[int, dict]:
    return store("add", str(path), "--family", "test", "--provenance", "tests/store_test.py", "--dry-run")


def check_refused(name: str, reason: str) -> None:
    code, r = add(FIXTURES / "must_refuse" / name)
    codes = {x["code"] for x in r.get("reasons", [])} | {
        x["code"] for lemma in r.get("lemmas", []) for x in lemma["reasons"]
    }
    details = [x["detail"] for x in r.get("reasons", [])] + [
        x["detail"] for lemma in r.get("lemmas", []) for x in lemma["reasons"] if x["code"] == reason
    ]
    ok = code == 2 and r.get("status") == "refused" and reason in codes
    if reason == "does_not_check":
        ok = ok and not any(RESOURCE.search(d) for d in details)
    first = (details[0].splitlines() or [""])[0][:160] if details else ""
    report(ok, f"add refuses must_refuse/{name}: {reason}: {first}", json.dumps(r)[:3000])


def check_existing_refused() -> None:
    """A lemma already proved in the library goes through the same checks: `shl_lshr_eq_iff` has a hypothesis
    nothing needs, so no counterexample for it exists."""
    code, r = store(
        "add",
        "--existing",
        "IRLean.Generic.shl_lshr_eq_iff",
        "--family",
        "test",
        "--provenance",
        "tests/store_test.py",
        "--dry-run",
    )
    codes = {x["code"] for lemma in r.get("lemmas", []) for x in lemma["reasons"]}
    report(
        code == 2 and r.get("status") == "refused" and "hypothesis_unwitnessed" in codes,
        "add --existing refuses IRLean.Generic.shl_lshr_eq_iff: hypothesis_unwitnessed",
        json.dumps(r)[:3000],
    )


def check_admitted() -> None:
    code, r = add(FIXTURES / "Admissible.lean")
    lemmas = r.get("lemmas", [])
    ok = code == 0 and r.get("status") == "accepted" and not r.get("stored") and len(lemmas) == 1
    ok = ok and lemmas[0]["status"] == "candidate" and lemmas[0]["hypotheses"][0]["status"] == "ok"
    report(
        ok,
        "add accepts Admissible.lean as a candidate, its hypothesis shown needed, and stores nothing on a "
        "dry run",
        json.dumps(r)[:3000],
    )


# ------------------------------------------------------------------------------------------------------------
# The premise selector, and the reuse example


def check_suggestions() -> None:
    code, out, secs = lean([str(FIXTURES / "Suggest.lean")])
    report(
        code == 0 and "error" not in out,
        f"grind +suggestions proves both goals from the store, in {secs:.1f} s",
        out,
    )
    # Without the suggestions grind proves neither, so it's the store that proves them.
    with tempfile.TemporaryDirectory() as tmp:
        plain = Path(tmp) / "Plain.lean"
        plain.write_text((FIXTURES / "Suggest.lean").read_text().replace("grind +suggestions", "grind"))
        code, out, _ = lean([str(plain)])
    errors = len(re.findall(r": error", out))
    report(code != 0 and errors == 2, f"plain grind proves neither goal: {errors} errors", out)


def axioms(module: str, work: Path) -> str:
    env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(work), str(LIB)]), "IRLEAN_CHECK_MODULE": module}
    p = proc.run(["lean", "-M", MB, "tests/check_axioms.lean"], cwd=ROOT, env=env)
    replay = proc.run(["leanchecker", module], cwd=ROOT, env=env)
    if p.exit != 0 or replay.exit != 0:
        return f"failed: {p.output}{replay.output}"
    return p.out.strip().splitlines()[-1]


def check_reuse(tool: Path) -> None:
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for w in (64, 256):
            for side, ns in (("src", "Src"), ("tgt", "Tgt")):
                p = proc.run(
                    [
                        str(tool),
                        str(FIXTURES / "reuse" / f"{side}{w}.ll"),
                        "--namespace",
                        f"{ns}{w}",
                        "-o",
                        str(work / f"{ns}{w}.lean"),
                    ]
                )
                if p.exit != 0:
                    report(False, f"ir-lean translates reuse/{side}{w}.ll", p.err)
                    return
                code, out, _ = lean(
                    ["-R", str(work), "-o", str(work / f"{ns}{w}.olean"), str(work / f"{ns}{w}.lean")], work
                )
                if code != 0:
                    report(False, f"the Lean ir-lean generated for reuse/{side}{w}.ll checks", out)
                    return

        def prove(name: str) -> tuple[str, int, str, float]:
            module = name.replace(".lean", "")
            code, out, secs = lean(
                [
                    "-R",
                    str(FIXTURES / "reuse"),
                    "-o",
                    str(work / f"{module}.olean"),
                    str(FIXTURES / "reuse" / name),
                ],
                work,
            )
            return name, code, out, secs

        names = ["After64.lean", "After256.lean", "Before64.lean", "Before256.lean"]
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(prove, names))
        for name, code, out, secs in results:
            module = name.replace(".lean", "")
            if code != 0:
                report(False, f"reuse/{name} checks", out)
                continue
            said = axioms(module, work)
            standard = re.search(r"and 0 from bv_decide", said) is not None
            want = name.startswith("After")
            report(
                standard == want and not said.startswith("failed"),
                f"reuse/{name} checks in {secs:.1f} s, rests on {said}, and leanchecker replays it",
                said,
            )


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    tool = Path(sys.argv[1]).resolve()
    started = time.monotonic()
    check_store()
    check_peephole_cycle()
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        jobs = [pool.submit(check_lookup, *case) for case in RESTATED]
        jobs += [pool.submit(check_instance, *case) for case in INSTANCES]
        jobs.append(pool.submit(check_lookup_misses))
        jobs += [pool.submit(check_refused, name, reason) for name, reason in MUST_REFUSE.items()]
        jobs.append(pool.submit(check_existing_refused))
        jobs.append(pool.submit(check_admitted))
        jobs.append(pool.submit(check_suggestions))
        for j in jobs:
            j.result()
    check_reuse(tool)
    print(f"in {time.monotonic() - started:.0f} s")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
