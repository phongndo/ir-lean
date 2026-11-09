#!/usr/bin/env python3
"""Checks tests/passes.py: that an instance counts only when tools/binding.py binds its bundle in the same
run, and that nothing else, a cache entry, a verdict it can't read, a changed bundle or a limit, ever counts.

The static tier needs only Python: how RUN lines are read, which functions are instances, what the cache
accepts, and how a verdict becomes a status, with tools/binding.py's output faked.

The live tier runs the scorer on tests/passes/, never on llvm-project, in build/passes-test, one process at
a time: the self-check, two functions bound and replayed independently, a second run from cache that verifies
them again, a changed certificate refused, a forged cache entry ignored, a RUN line with an option
unsupported, and limits that stop a step unknown. It needs `nix develop`, build/ir-lean and `lake build`.

usage: tests/passes_test.py [--tier static|live|all] [--keep]
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
import threading
from collections.abc import Callable
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "passes"
WORK = ROOT / "build" / "passes-test"
SCORER = [sys.executable, str(ROOT / "tests" / "passes.py")]
BINDING = [sys.executable, str(ROOT / "tools" / "binding.py")]
FIXTURES = [str(HERE / "instcombine.ll"), str(HERE / "options.ll")]
# A proof the automation can't finish in time: bv_decide on 64-bit multiplication, which takes far longer than
# the wall clock the test sets.
SLOW = str(HERE / "slow.ll")
# Two jobs, the most the scorer runs, and memory for three 3.5 GB Lean processes and 2 GB for the scorer, so
# the self-check tries three mutants at a time: less than a whole machine, as CI's 16 GB runners have.
LIMITS = ["--jobs", "2", "--memory", "12600", "--lean-memory", "3000"]


def load_passes() -> Any:
    spec = importlib.util.spec_from_file_location("passes", ROOT / "tests" / "passes.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Its dataclasses look themselves up by module name.
    sys.modules["passes"] = module
    spec.loader.exec_module(module)
    return module


P = load_passes()
B = P.B


class Failures:
    def __init__(self) -> None:
        self.items: list[str] = []
        self.passed = 0

    def check(self, ok: bool, what: str, detail: Any = "") -> None:
        if ok:
            self.passed += 1
            print(f"ok    {what}")
        else:
            self.items.append(what)
            print(f"FAIL  {what}: {str(detail)[:1500]}")


# ------------------------------------------------------------------------------------------------------------
# Static


def bare_scorer(work: Path, salt: str = "s" * 64) -> Any:
    """A Scorer without a toolchain, for what doesn't run anything."""
    s = object.__new__(P.Scorer)
    s.work, s.kind, s.timeout, s.lean_mb, s.use_cache, s.keep = (
        work,
        "ir_instance_equivalence",
        300,
        3000,
        True,
        False,
    )
    s.runs, s.bundles, s.verdicts = work / "runs", work / "bundles", work / "verdicts"
    s.scratch = work / "work"
    for d in (s.runs, s.bundles, s.verdicts, s.scratch):
        d.mkdir(parents=True, exist_ok=True)
    s.salt, s.env = salt, {}
    s.stats = {"fresh": 0, "reused": 0, "rechecked": 0, "stale_ignored": 0}
    s.lock = threading.Lock()
    return s


def static(f: Failures) -> None:
    f.check(
        P.parse_opt("opt < %s -passes=instcombine -S | FileCheck %s") == ("instcombine", None, ()),
        "a plain RUN line has a spec and no other options",
    )
    f.check(
        P.parse_opt("opt -S -passes='sccp' -mtriple x86_64-unknown-linux-gnu %s -o -")
        == ("sccp", "x86_64-unknown-linux-gnu", ()),
        "-mtriple, quoting and -o are read",
    )
    f.check(
        P.parse_opt("opt < %s -passes=instcombine -instcombine-max-num-phis=1 -S")
        == ("instcombine", None, ("-instcombine-max-num-phis=1",)),
        "another option is kept, not dropped",
    )
    f.check(
        P.parse_opt("not opt -passes=instcombine %s") is None, "a RUN line expecting opt to fail is no run"
    )
    f.check(
        P.parse_opt("opt -passes=sccp -disable-output %s 2>&1 | FileCheck %s") == ("sccp", None, ())
        and P.parse_opt("opt -passes=sccp %s -S 2> %t.err > %t") == ("sccp", None, ()),
        "shell redirections and -disable-output are where opt writes, not options",
    )
    f.check(
        P.parse_opt("opt -passes=sccp -mcpu=znver4 -data-layout=e %s")
        == ("sccp", None, ("-mcpu=znver4", "-data-layout=e")),
        "-mcpu and -data-layout are options a bundle can't represent",
    )
    f.check(
        P.single_pass("function(instcombine)") is None and P.single_pass("a,b") is None,
        "a pipeline is not a pass alone",
    )
    f.check(
        P.run_commands("; RUN: opt < %s \\\n; RUN:   -passes=sccp -S\n") == ["opt < %s     -passes=sccp -S"],
        "a RUN line continued with a backslash is one command",
    )
    f.check("instcombine" in P.ir_passes(), "pass names come from tests/llvm_scope/inventory.json")

    src = (
        "define i8 @a() {\n  ret i8 1\n}\ndefine i8 @b() {\n  %r = call i8 @a()\n  ret i8 %r\n}\n"
        "define i8 @c() {\n  ret i8 0\n}\n"
    )
    tgt = (
        "define i8 @a() {\n  ret i8 2\n}\ndefine i8 @b() {\n  %r = call i8 @a()\n  ret i8 %r\n}\n"
        "define i8 @d() {\n  ret i8 0\n}\n"
    )
    changed, gone = P.instances(src, tgt)
    f.check(
        changed == ["a", "b", "c", "d"] and gone == {"c", "d"},
        "instances are the changed functions, their callers, and those added or removed",
        (changed, gone),
    )

    with tempfile.TemporaryDirectory() as tmp:
        s = bare_scorer(Path(tmp))
        key = "k" * 64
        good = {
            "schema": P.RUN_SCHEMA,
            "key": key,
            "salt": s.salt,
            "instances": {"f": {"status": "candidate", "reason": "replayed", "detail": ""}},
        }

        def entry(e: Any) -> Any:
            (s.runs / f"{key}.json").write_text(e if isinstance(e, str) else json.dumps(e))
            return s.cached(key)

        f.check(entry(good) is not None, "a well-formed entry for this key and salt is used")
        bound = json.loads(json.dumps(good))
        bound["instances"]["f"]["status"] = "bound"
        f.check(entry(bound) is None, "an entry saying bound is ignored: the cache never holds bound")
        legacy = {"instances": {"f": {"status": "certified", "axioms": "..."}}}
        f.check(entry(legacy) is None, "a research scorer entry saying certified is ignored")
        f.check(
            entry({**good, "salt": "t" * 64}) is None, "an entry from another toolchain or scorer is ignored"
        )
        f.check(entry({**good, "key": "j" * 64}) is None, "an entry for another key is ignored")
        f.check(entry("{not json") is None, "an entry that isn't JSON is ignored")
        f.check(s.stats["stale_ignored"] == 5, "each ignored entry is counted as stale_ignored", s.stats)

        run = P.Run("instcombine", Path(tmp) / "t.ll", "instcombine", None, ())
        s.store(
            key,
            run,
            b"x",
            {"instances": {"f": P.result("bound", "replayed", bundle="bundles/x/manifest.json")}},
        )
        stored = json.loads((s.runs / f"{key}.json").read_text())
        f.check(
            stored["instances"]["f"]["status"] == "candidate",
            "a bound instance is stored as a candidate",
            stored,
        )
        (s.runs / f"{key}.json").unlink()
        s.store(key, run, b"x", {"instances": {"f": P.result("error", "tool_failed")}})
        f.check(not (s.runs / f"{key}.json").exists(), "a run with an error isn't stored")

        passed = {m[0]: {"f": {"status": "failed", "reason": "proof_not_found"}} for m in P.MUTANTS}
        record = s.work / "selfcheck" / f"{s.salt}.json"
        record.parent.mkdir(parents=True, exist_ok=True)

        def selfcheck(e: Any) -> Any:
            record.write_text(json.dumps(e))
            return P.mutants_passed(s)

        good_check = {"schema": P.SELFCHECK_SCHEMA, "salt": s.salt, "mutants": passed}
        f.check(
            selfcheck(good_check) == passed, "a self-check every mutant failed is reused with the same salt"
        )
        proved = json.loads(json.dumps(good_check))
        proved["mutants"]["off by one"]["f"]["status"] = "candidate"
        f.check(selfcheck(proved) is None, "a stored self-check where a mutant was proved is ignored")
        missing = json.loads(json.dumps(good_check))
        del missing["mutants"]["loops forever"]
        f.check(selfcheck(missing) is None, "a stored self-check missing a mutant is ignored")
        f.check(
            selfcheck({**good_check, "salt": "t" * 64}) is None, "a self-check from another salt is ignored"
        )
        record.unlink()

        manifest = s.bundles / "x" / "manifest.json"
        manifest.parent.mkdir()
        s.toolchain = {"lean_version": "test"}
        s.bins = {"opt": "opt"}
        test = P.Run("instcombine", Path(tmp) / "t.ll", "instcombine", None, ())
        input_ll = b"define i8 @f() {\n  ret i8 0\n}\n"

        def bundle(function: str = "f", data: bytes = input_ll, passes: str = "instcombine") -> dict:
            """The parts of a manifest the scorer reads, written where the scorer will read them."""
            m = {
                "claim": {"kind": "ir_instance_equivalence", "function": function},
                "transform": {"passes": passes, "mtriple": None},
                "artifacts": {"input": {"sha256": P.hashlib.sha256(data).hexdigest()}},
            }
            manifest.write_text(json.dumps(m))
            return m

        def key(m: dict) -> str:
            return B.sha256(
                B.canonical({"verdict": B.VERDICT_SCHEMA, "manifest": m, "toolchain": s.toolchain})
            )

        fake: dict[str, Any] = {}
        real_run = P.run

        def answer(code: int, out: Any, limit: str | None = None, err: str = "") -> None:
            fake.update(code=code, out=out if isinstance(out, str) else json.dumps(out), limit=limit, err=err)

        commands: list[list[str]] = []

        def fake_run(command: list[str], **_: Any) -> Any:
            commands.append(command)
            return P.Ran(fake["code"], fake["out"], fake["err"], fake["limit"])

        P.run = fake_run
        try:
            verdict = {
                "schema": B.VERDICT_SCHEMA,
                "status": "bound",
                "reason": "replayed",
                "exit_code": 0,
                "manifest": str(manifest),
                "claim": {"kind": "ir_instance_equivalence"},
                "cache": "miss",
                "key": key(bundle()),
            }
            answer(0, verdict)
            f.check(
                s.verify(manifest, test, input_ll, "f")["status"] == "bound",
                "a bound verdict with exit code 0, about this instance's manifest, is bound",
            )
            f.check(
                commands[-1][2] == "verify" and "--cache" not in commands[-1],
                "tools/binding.py verify runs without its cache, so a bound instance is replayed in full",
                commands[-1],
            )
            cases: list[tuple[str, int, Any, str | None, str]] = [
                ("a bound verdict with exit code 1", 1, verdict, None, "error"),
                ("a verdict of another schema", 0, {**verdict, "schema": "other/1"}, None, "error"),
                ("a verdict about another manifest", 0, {**verdict, "manifest": "/elsewhere"}, None, "error"),
                (
                    "a bound verdict about another claim kind",
                    0,
                    {**verdict, "claim": {"kind": "ir_instance_refinement"}},
                    None,
                    "error",
                ),
                (
                    "a verdict whose exit_code isn't the process's",
                    0,
                    {**verdict, "exit_code": 4},
                    None,
                    "error",
                ),
                ("output that isn't JSON", 0, "bound", None, "error"),
                (
                    "a status tools/binding.py doesn't have",
                    0,
                    {**verdict, "status": "certified"},
                    None,
                    "error",
                ),
                ("verify stopped by the wall clock", 0, verdict, "took more than 9 s", "unknown"),
                (
                    "an unknown verdict",
                    4,
                    {**verdict, "status": "unknown", "reason": "time_limit", "exit_code": 4},
                    None,
                    "unknown",
                ),
                (
                    "a refused verdict",
                    1,
                    {**verdict, "status": "refused", "reason": "artifact_hash_mismatch", "exit_code": 1},
                    None,
                    "refused",
                ),
                (
                    "a bound verdict whose key isn't the manifest read here",
                    0,
                    {**verdict, "key": "0" * 64},
                    None,
                    "refused",
                ),
            ]
            for what, code, out, limit, want in cases:
                answer(code, out, limit)
                got = s.verify(manifest, test, input_ll, "f")
                f.check(got["status"] == want, f"{what} is {want}", got)
            others: list[tuple[str, Callable[[], dict]]] = [
                ("another function", lambda: bundle(function="g")),
                ("another input", lambda: bundle(data=b"; another test\n")),
                ("another pass spec", lambda: bundle(passes="sccp")),
            ]
            for what, write in others:
                # The manifest on disk is this case's, and the verdict's key matches it, so only the field
                # that differs can refuse it.
                answer(0, {**verdict, "key": key(write())})
                got = s.verify(manifest, test, input_ll, "f")
                f.check(
                    (got["status"], got["reason"]) == ("refused", "instance_mismatch")
                    and got["detail"].startswith("the bundle is about"),
                    f"a valid bundle about {what}, at this instance's path, is refused",
                    got,
                )

            answer(1, "", err="record failed: time_limit: opt took more than 5 s")
            got = s.bind(test, "k" * 64, input_ll, "f", "-- certificate", "P")
            f.check(
                (got["status"], got["reason"]) == ("unknown", "time_limit"),
                "a limit tools/binding.py record reports is unknown, not an error",
                got,
            )
            answer(-9, "", limit="took more than 120 s")
            found = s.fresh(test, input_ll, "k" * 64)
            counts, _ = P.tally([(test, found)], Path(tmp), Path(tmp))
            f.check(
                found.get("skipped") == "opt_limit"
                and counts["per_pass"]["instcombine"] == {"unknown_runs": 1},
                "opt stopped by a limit makes the run unknown, which keeps the pass from L2",
                (found, counts),
            )
        finally:
            P.run = real_run

    scopes(f)
    r = subprocess.run(
        [*SCORER, "--kind", "ir_instance_refinement", "--work", str(Path(tempfile.gettempdir()) / "unused")],
        capture_output=True,
        text=True,
        check=False,
    )
    f.check(
        r.returncode == 1 and "proves only ir_instance_equivalence" in r.stderr,
        "a full run with a claim kind the automation can't prove is refused before it starts",
        (r.returncode, r.stderr[-300:]),
    )


def scopes(f: Failures) -> None:
    """Only a scope holding a process given this tools/binding.py process's token is killed, not one of
    another process that had the same pid."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        procs = {
            name: subprocess.Popen(["sleep", "60"], env={**P.os.environ, P.OWNER_ENV: token})
            for name, token in (("mine", "tok"), ("other", "someone-else"))
        }
        try:
            made = {}
            for name, pid, proc in (
                ("mine", 123, "mine"),
                ("other", 123, "other"),
                ("elsewhere", 124, "mine"),
            ):
                d = root / "app.slice" / f"ir-lean-binding-{pid}-{name}.scope"
                d.mkdir(parents=True)
                (d / "cgroup.procs").write_text(f"{procs[proc].pid}\n")
                made[name] = d
            killed = P.kill_binding_scopes(123, "tok", root)
            f.check(
                killed == [made["mine"]]
                and (made["mine"] / "cgroup.kill").read_text() == "1"
                and not (made["other"] / "cgroup.kill").exists()
                and not (made["elsewhere"] / "cgroup.kill").exists(),
                "only scopes named for that pid and holding its token are killed",
                killed,
            )
        finally:
            for p in procs.values():
                p.kill()
                p.wait()


# ------------------------------------------------------------------------------------------------------------
# Live


def score(work: Path, *extra: str) -> tuple[int, dict, list[dict], str]:
    """Runs the scorer on the fixtures. Its exit code, score.json, the instance records, and what it said."""
    r = subprocess.run(
        [*SCORER, "--files", *FIXTURES, "--only", "instcombine", "--work", str(work), *LIMITS, *extra],
        capture_output=True,
        text=True,
        check=False,
    )
    path = work / "score.json"
    if r.returncode != 0 or not path.exists():
        return r.returncode, {}, [], r.stdout + r.stderr
    s = json.loads(path.read_text())
    records = json.loads(Path(s["instance_records"]).read_text())
    path.unlink()
    return r.returncode, s, records, r.stdout + r.stderr


def by_function(records: list[dict]) -> dict[str, dict]:
    return {r["function"]: r for r in records}


def live(f: Failures, keep: bool) -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    work = WORK / "main"

    code, s, records, said = score(work)
    f.check(code == 0 and s.get("schema") == P.SCORE_SCHEMA, "the scorer runs on the fixtures", said[-2000:])
    if code != 0:
        return
    check = s["self_check"]
    f.check(
        check["ok"] and set(check["mutants"]) == {m[0] for m in P.MUTANTS},
        "every known-wrong rewrite fails to prove, and the control is bound",
        check,
    )
    f.check(
        all(v["status"] in ("failed", "unknown") for m in check["mutants"].values() for v in m.values()),
        "no mutant is anything but failed or unknown",
        check["mutants"],
    )
    got = by_function(records)
    want = {
        "guarded": ("bound", "replayed"),
        "round_trip": ("bound", "replayed"),
        "loads": ("unsupported", "memory_unsupported"),
        "maybe_undef": ("unsupported", "undef_argument"),
    }
    f.check(
        {k: (v["status"], v["reason"]) for k, v in got.items()} == want,
        "two functions are bound, and memory and undef arguments are unsupported",
        got,
    )
    f.check(
        all(set(r) == INSTANCE_KEYS and r["schema"] == P.INSTANCE_SCHEMA for r in records),
        "every instance record has exactly the contract's keys",
        records[:1],
    )
    f.check(
        s["per_pass"]["instcombine"].get("unsupported_runs") == 1,
        "a RUN line with an option a bundle can't hold is an unsupported run",
        s["per_pass"],
    )
    f.check(
        s["done"] == 0 and s["ladder"]["L3"] == 0 and s["ladder"]["L4"] == 0 and s["ladder"]["L2"] == 0,
        "nothing is done, and a pass with unsupported instances isn't L2",
        s["ladder"],
    )
    f.check(s["cache"]["fresh"] == 3 and s["cache"]["reused"] == 0, "the first run is fresh", s["cache"])
    if got.get("guarded", {}).get("status") != "bound":
        return
    manifest = work / got["guarded"]["bundle"]

    r = subprocess.run([*BINDING, "verify", str(manifest)], capture_output=True, text=True, check=False)
    verdict = json.loads(r.stdout) if r.stdout.startswith("{") else {}
    f.check(
        r.returncode == 0 and verdict.get("status") == "bound" and verdict.get("cache") == "disabled",
        "the bundle is bound again by tools/binding.py alone, without any cache",
        r.stdout[-1500:] + r.stderr,
    )
    f.check("guarded" in verdict.get("statement", ""), "the statement is about the function", verdict)

    code, s, records, said = score(work)
    got = by_function(records)
    f.check(
        code == 0
        and got["guarded"]["status"] == "bound"
        and got["guarded"]["source"] == "cache"
        and got["guarded"]["binding_cache"] == "disabled",
        "a second run verifies the cached candidates again, from scratch",
        (said[-800:], got.get("guarded")),
    )
    f.check(
        s.get("cache", {}).get("rechecked") == 3,
        "every bound instance, the control's too, is rechecked",
        s.get("cache"),
    )
    check = s.get("self_check", {})
    f.check(
        check.get("mutants_from_cache") is True
        and check.get("control", {}).get("f", {}).get("status") == "bound",
        "the mutants' results are reused with the same salt, and the control is bound again",
        check,
    )

    cert = manifest.parent / "Cert.lean"
    cert.write_text(cert.read_text() + "\n-- changed after it was bound\n")
    code, s, records, said = score(work)
    got = by_function(records)
    f.check(
        code == 0
        and (got["guarded"]["status"], got["guarded"]["reason"]) == ("refused", "artifact_hash_mismatch")
        and got["round_trip"]["status"] == "bound",
        "a changed certificate is refused, not taken from cache",
        (said[-800:], got),
    )

    entries = [p for p in (work / "runs").glob("*.json") if "round_trip" in p.read_text()]
    forged = json.loads(entries[0].read_text())
    forged["instances"]["round_trip"]["status"] = "bound"
    forged["instances"]["guarded"]["status"] = "bound"
    entries[0].write_text(json.dumps(forged))
    code, s, records, said = score(work)
    got = by_function(records)
    f.check(
        code == 0
        and s["cache"]["stale_ignored"] == 1
        and got["guarded"]["status"] == "refused"
        and got["round_trip"]["source"] == "fresh",
        "a cache entry saying bound is ignored, and the run done again",
        (s.get("cache"), got),
    )

    # The control's bundle is valid, and bound on its own, but about another test and function.
    target = work / got["round_trip"]["bundle"]
    control = next(
        p.parent
        for p in (work / "bundles").glob("*/manifest.json")
        if json.loads(p.read_text())["claim"]["function"] == "f"
    )
    shutil.rmtree(target.parent)
    shutil.copytree(control, target.parent)
    code, s, records, said = score(work)
    got = by_function(records)
    f.check(
        code == 0
        and (got["round_trip"]["status"], got["round_trip"]["reason"]) == ("refused", "instance_mismatch"),
        "a valid bundle for another instance, where this one's should be, is refused",
        (said[-800:], got.get("round_trip")),
    )

    refinement = ["--work", str(WORK / "refinement"), "--memory", "6000", "--kind", "ir_instance_refinement"]
    r = subprocess.run(
        [*SCORER, "--debug", FIXTURES[0], "instcombine", "", *refinement],
        capture_output=True,
        text=True,
        check=False,
    )
    try:
        judged = {
            n: v for n, v in json.loads(r.stdout)["instances"].items() if n in ("guarded", "round_trip")
        }
    except (ValueError, KeyError):
        judged = {}
    f.check(
        len(judged) == 2
        and all((v["status"], v["reason"]) == ("failed", "no_automation") for v in judged.values()),
        "with IRLean.Refines on main, a refinement instance nothing here proves is failed, never bound",
        (judged, r.stderr[-500:]),
    )

    stopped(f, WORK / "limits", SLOW, ["--timeout", "5"], {"distributes"}, "time_limit", "a 5 s wall clock")
    stopped(
        f,
        WORK / "limits-memory",
        FIXTURES[0],
        ["--lean-memory", "64"],
        {"guarded", "round_trip"},
        "resource_limit",
        "Lean's -M of 64 MB",
    )
    if not keep:
        shutil.rmtree(WORK, ignore_errors=True)


INSTANCE_KEYS = {
    "schema",
    "pass",
    "test",
    "spec",
    "mtriple",
    "options",
    "function",
    "status",
    "reason",
    "detail",
    "bundle",
    "verdict",
    "binding_cache",
    "source",
}


def stopped(
    f: Failures, work: Path, test: str, limits: list[str], judge: set[str], reason: str, what: str
) -> None:
    """With a limit too small to finish, every instance in `judge` is unknown for that reason, never failed,
    refused or bound."""
    r = subprocess.run(
        [*SCORER, "--debug", test, "instcombine", "", "--work", str(work), "--memory", "6000", *limits],
        capture_output=True,
        text=True,
        check=False,
    )
    try:
        found = json.loads(r.stdout)["instances"]
    except (ValueError, KeyError):
        f.check(False, f"{what} stops a step as unknown", r.stdout[-800:] + r.stderr[-800:])
        return
    judged = {n: v for n, v in found.items() if n in judge}
    f.check(
        set(judged) == judge
        and all((v["status"], v["reason"]) == ("unknown", reason) for v in judged.values()),
        f"{what} stops a step as unknown, {reason}, never failed, refused or bound",
        judged,
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tier", choices=["static", "live", "all"], default="all")
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()
    f = Failures()
    tiers: list[Callable[[], None]] = []
    if args.tier in ("static", "all"):
        tiers.append(lambda: static(f))
    if args.tier in ("live", "all"):
        tiers.append(lambda: live(f, args.keep))
    for t in tiers:
        t()
    print(f"{f.passed} passed, {len(f.items)} failed")
    return 1 if f.items else 0


if __name__ == "__main__":
    sys.exit(main())
