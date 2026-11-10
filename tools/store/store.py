#!/usr/bin/env python3
"""The lemma store: checked lemmas that later proofs, the superoptimizer and proof tests can find and reuse.

docs/lemma-store.md says what's in it, the bar a lemma meets, and what each answer means. In short, a lemma is

  admitted   it meets all four rules of the roadmap's bar, and the rest of the admission checks
  candidate  it meets all but the fourth: fewer than two proofs use it yet
  refused    it fails a check, and `reasons` says which, by a stable code

The store is store/index.json, the Lean modules it names, and the counterexamples in store/LemmaStore/Counter.
`lake build` builds them. Nothing in the store is trusted: a lemma is checked again wherever it's used.

usage: tools/store/store.py check [--write] [--json] [--pretty]
       tools/store/store.py lookup --statement TEXT [--import MODULE ...] [--json] [--pretty]
       tools/store/store.py add FILE.lean --family NAME --provenance TEXT [--dry-run] [--json] [--pretty]
       tools/store/store.py add --existing NAME ... [--import MODULE ...] --family NAME --provenance TEXT
                                [--dry-run] [--json]
       tools/store/store.py forget NAME --reason TEXT
       tools/store/store.py report [--json] [--pretty]
       tools/store/store.py capabilities [--pretty]

Exit codes: 0 when everything asked for holds (a check passes, a lookup finds something, an addition is
admitted or a candidate), 2 when a lemma is refused or a check fails, 3 when a lookup finds nothing, and 1 for
an error, which decides nothing.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import datetime
import json
import os
import re
import shutil
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, NoReturn

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, proc, schemas  # noqa: E402
from irlean import lean as leanlib  # noqa: E402
from irlean import verdict as core  # noqa: E402

STORE = ROOT / "store"
# The `Peephole` library, whose theorems prove chunk 1's rewrites, each named `Peephole.<ID>` after the
# inventory's ID: its proofs count as uses, and its family lemma files hold their own counterexamples.
PEEPHOLE = ROOT / "tests" / "passes-proofs" / "peephole"
REWRITES = ROOT / "tests" / "llvm_scope" / "rewrites"
INDEX = STORE / "index.json"
ROOT_MODULE = STORE / "LemmaStore.lean"
OWNED = STORE / "LemmaStore" / "Lemmas"
LIB = ROOT / ".lake" / "build" / "lib" / "lean"
WORK = ROOT / "build" / "store"
CHECK_AXIOMS = ROOT / "tests" / "check_axioms.lean"

SCHEMA = schemas.STORE
LOOKUP_SCHEMA = schemas.STORE_LOOKUP
ADMISSION_SCHEMA = schemas.STORE_ADMISSION
INDEX_SCHEMA = schemas.STORE_INDEX
COUNTER_PREFIX = "LemmaStore.Counter"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# A lemma the kernel takes longer than this to check again should be cut into smaller ones.
REPLAY_LIMIT_MS = 1000.0
# What each tactic tried on a lemma may spend, in thousands of heartbeats, as `maxHeartbeats` counts.
TRIVIALITY_HEARTBEATS = 20000
LEAN_MB = int(os.environ.get("LEMMA_STORE_LEAN_MB", "4000"))
LEAN_TIMEOUT = int(os.environ.get("LEMMA_STORE_TIMEOUT", "600"))
EXIT = {"ok": 0, "error": 1, "refused": 2, "not_found": 3}

# Every reason a lemma is refused, the rule of the bar it enforces, and what it means. A new one goes at the
# end, and keeps its meaning. Rules 1 to 4 are the roadmap's; "admission" are the other checks
# docs/lemma-store.md lists.
REASONS: dict[str, tuple[str, str]] = {
    "not_found": ("1", "No declaration has that name"),
    "not_a_theorem": ("1", "It isn't a theorem"),
    "does_not_check": ("1", "Lean rejects its module, with an error that isn't a resource limit"),
    "sorry": ("1", "It rests on `sorryAx`"),
    "nonstandard_axiom": (
        "1",
        "It rests on an axiom beyond the standard three, such as one `bv_decide` adds",
    ),
    "compiled_code": ("1", "Its module, or one it imports, uses `implemented_by` or `extern`"),
    "replay_failed": ("1", "`leanchecker`'s replay through the kernel rejects its module"),
    "fixed_width": ("2", "It's stated at a width written as a number other than 1, with no reason recorded"),
    "hypothesis_unwitnessed": (
        "3",
        "A hypothesis has no counterexample showing it's needed, or it states something else",
    ),
    "hypotheses_unsatisfiable": (
        "3",
        "No witness shows its hypotheses can all hold, or the witness states something else",
    ),
    "not_normal": ("admission", "What a use site matches against a goal isn't in the normalizer's form"),
    "duplicate": (
        "admission",
        "Another stored lemma has the same key: the same statement after normalization",
    ),
    "subsumed": (
        "admission",
        "Another stored lemma proves it by being applied, with every side condition closed",
    ),
    "trivial": ("admission", "`simp`, `bv_normalize`, `grind` or `decide` closes it alone"),
    "slow": ("admission", f"The kernel takes more than {REPLAY_LIMIT_MS:.0f} ms to check it again"),
    "unlifted_constant": ("admission", "It has a bit-vector constant other than 0 or 1 written as a number"),
    "no_provenance": ("admission", "Its entry doesn't say where it came from"),
    "statement_changed": ("admission", "Its key isn't the one the index records, so its statement changed"),
}
STATUSES = {
    "admitted": "Meets all four rules of the bar, and the other admission checks",
    "candidate": "Meets all but the fourth rule: fewer than two proofs use it yet",
    "refused": "Fails a check. `reasons` says which",
}
# Lean errors that say it ran out of something, which never count as the lemma being wrong.
RESOURCE = leanlib.LIMIT


class StoreError(Exception):
    """Something kept a check from deciding anything."""

    def __init__(self, reason: str, detail: str) -> None:
        super().__init__(detail)
        self.reason = reason
        self.detail = detail


# ------------------------------------------------------------------------------------------------------------
# Running Lean


def lean_env(*paths: Path) -> dict[str, str]:
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in (*paths, LIB))
    return env


def run(cmd: list[str], env: dict[str, str] | None = None, timeout: int = LEAN_TIMEOUT) -> tuple[int, str]:
    """Runs `cmd` from the repo's root, and returns its exit code and what it printed, both streams
    together. Past `timeout`, it and everything it started are killed, and it says so as Lean would."""
    try:
        r = proc.run(cmd, cwd=ROOT, env=env, timeout=timeout)
    except FileNotFoundError as e:
        raise StoreError("toolchain_missing", f"{cmd[0]} isn't on PATH") from e
    if r.limit is not None:
        return 124, r.out + f"\n(deterministic) timeout: {cmd[0]} ran past {timeout} s"
    return r.exit, r.out + r.err


def lean(args: list[str], env: dict[str, str]) -> tuple[int, str]:
    return run(["lean", "-M", str(LEAN_MB), *args], env)


def lean_errors(out: str) -> list[str]:
    return [line for line in out.splitlines() if ": error" in line or "error:" in line]


def json_line(out: str) -> Any:
    for line in out.splitlines():
        if line.startswith("STORE-JSON "):
            return json.loads(line[len("STORE-JSON ") :])
    raise StoreError("tool_failed", "the checker printed no result:\n" + out[-4000:])


def lake_built(targets: list[str]) -> core.Step:
    """That `lake build` has nothing left to do for `targets`, so the modules read are the sources' own."""
    code, out = run(["lake", "build", "--no-build", *targets])
    if code != 0:
        raise StoreError(
            "store_not_built",
            f"lake has {', '.join(targets)} to build first: run `lake build`\n{out[-2000:]}",
        )
    return core.Step("lake build --no-build", code, None, out)


# ------------------------------------------------------------------------------------------------------------
# The index and the modules it names


def read_index() -> dict[str, Any]:
    data = json.loads(INDEX.read_text())
    if data.get("schema") != INDEX_SCHEMA:
        raise StoreError("index_invalid", f"{INDEX} has schema {data.get('schema')!r}, not {INDEX_SCHEMA}")
    return data


def write_index(data: dict[str, Any]) -> None:
    INDEX.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def module_file(module: str) -> Path | None:
    """Where a module of this repo's libraries is, if it's one."""
    parts = module.split(".")
    if parts[0] == "IRLean":
        return ROOT.joinpath(*parts).with_suffix(".lean")
    if parts[0] == "LemmaStore":
        return STORE.joinpath(*parts).with_suffix(".lean")
    if parts[0] == "StoreTool":
        return ROOT / "tools" / "store" / "StoreTool.lean"
    if parts[0] == "Peephole":
        return PEEPHOLE.joinpath(*parts).with_suffix(".lean")
    return None


def peephole_modules(src: Path = PEEPHOLE) -> list[str]:
    """Every module of the `Peephole` library, as `lake build Peephole` builds them."""
    return sorted(
        ".".join(p.relative_to(src).with_suffix("").parts) for p in (src / "Peephole").rglob("*.lean")
    )


def peephole_cycles(src: Path = PEEPHOLE) -> list[str]:
    """Each module of the `Peephole` library that imports the store. `LemmaStore` imports the library's lemma
    files once their lemmas are stored, so one that imported it back would make a cycle."""
    return [
        f"{m} imports {i}"
        for m in peephole_modules(src)
        for i in imports_of(src.joinpath(*m.split(".")).with_suffix(".lean"))
        if i == "LemmaStore" or i.startswith("LemmaStore.")
    ]


def site_theorems() -> list[str]:
    """The name a theorem proving each rewrite in the inventory has: `Peephole.<ID>`."""
    return sorted(
        f"Peephole.{r['id']}"
        for f in sorted(REWRITES.glob("*.json"))
        for r in schemas.read(f, schemas.REWRITES)["rewrites"]
    )


def peephole_imports() -> list[str]:
    """The `Peephole` library's modules, for counting uses, once it's checked not to import the store."""
    if cycles := peephole_cycles():
        raise StoreError("import_cycle", "the Peephole library can't import the store: " + "; ".join(cycles))
    return peephole_modules()


def imports_of(path: Path) -> list[str]:
    return re.findall(r"^import\s+(\S+)", path.read_text(), re.M)


def closure(modules: list[str]) -> list[str]:
    """The modules of this repo that `modules` import, themselves included, in a fixed order."""
    seen: set[str] = set()
    todo = list(modules)
    while todo:
        m = todo.pop()
        f = module_file(m)
        if m in seen or f is None or not f.exists():
            continue
        seen.add(m)
        todo.extend(imports_of(f))
    return sorted(seen)


toolchain = leanlib.toolchain


def sources_hash(modules: list[str]) -> str:
    """What the store's validity depends on, as Mathlib's cache hashes it: the toolchain and the sources of
    every module the store imports from this repo."""
    h = hashing.new(toolchain().encode())
    for m in closure(modules):
        f = module_file(m)
        assert f is not None
        h.update(f"\0{m}\0".encode())
        h.update(f.read_bytes())
    return h.hexdigest()


def key_of(key_text: str) -> str:
    return hashing.sha256_text(key_text)[:20]


def counter_modules() -> list[str]:
    return ["LemmaStore.Counter", *imports_of(STORE / "LemmaStore" / "Counter.lean")]


def lemma_modules(index: dict[str, Any]) -> list[str]:
    return sorted({e["module"] for e in index["lemmas"]})


def generated_root(index: dict[str, Any]) -> str:
    """store/LemmaStore.lean, as the index says it should be."""
    imports = "\n".join(f"import {m}" for m in lemma_modules(index))
    names = ",\n".join(f"  ``{e['name']}" for e in index["lemmas"])
    return (
        f"{imports}\n\n"
        "/-! # The lemma store\n\n"
        "Importing this imports every stored lemma. `catalog` names them, in `store/index.json`'s order,\n"
        "and `tools/store/store.py` writes this file from that index: change the store with `store.py add`\n"
        "and `store.py forget`, never by hand. `docs/lemma-store.md` says what a stored lemma has to\n"
        "meet.\n\n"
        "`LemmaStore.Select` finds lemmas here for a goal, and `LemmaStore.Counter` holds the\n"
        "counterexamples that show each hypothesis is needed. -/\n\n"
        "namespace LemmaStore\n\n"
        "/-- Every stored lemma, admitted or a candidate. -/\n"
        f"def catalog : Array Lean.Name := #[\n{names}]\n\n"
        "end LemmaStore\n"
    )


def consumers(index: dict[str, Any]) -> list[dict[str, str]]:
    return index.get("consumers", [])


def build_consumers(index: dict[str, Any], work: Path) -> None:
    """Compiles each module whose proofs count as uses, which `lake build` doesn't, into `work`. One is
    compiled again only when its source, what it imports from this repo, or the toolchain changed."""
    work.mkdir(parents=True, exist_ok=True)
    for c in consumers(index):
        f = ROOT / c["file"]
        olean, stamp = work / f"{c['module']}.olean", work / f"{c['module']}.key"
        h = hashing.new(f.read_bytes())
        h.update(sources_hash(imports_of(f)).encode())
        key = h.hexdigest()
        if olean.exists() and stamp.exists() and stamp.read_text() == key:
            continue
        code, out = lean(["-o", str(olean), c["file"]], lean_env(work))
        if code != 0:
            raise StoreError("consumer_failed", f"{c['file']} doesn't compile:\n{out[-3000:]}")
        stamp.write_text(key)


# ------------------------------------------------------------------------------------------------------------
# The checks that make a module trusted, read as data


def axiom_check(module: str, env: dict[str, str]) -> tuple[str | None, str, core.Step]:
    """`tests/check_axioms.lean` on `module`, which reads it and everything it imports as data. Returns the
    refusal it gives, if any, and what it said. A module holding stored lemmas may rest on nothing beyond the
    standard three, so even `bv_decide`'s axioms, which that check allows, are refused here."""
    code, out = lean([str(CHECK_AXIOMS)], {**env, "IRLEAN_CHECK_MODULE": module})
    step = core.Step("check_axioms", code, None, out)
    said = (out.strip().splitlines() or [""])[-1]
    if code != 0:
        if code < 0 or code >= 128:
            # A signal death or a crash exit code (SIGKILL, SIGABRT, SIGSEGV, 134, 137...): the audit produced
            # no verdict, so nothing is known about the module's axioms. Decided before any refusal text in
            # the output is read -- a crashed process that happened to print "not an allowed axiom" mustn't be
            # read as a refusal of the lemma. An error, never a refusal.
            raise StoreError("tool_failed", f"checking {module}'s axioms was killed (exit {code}): {said}")
        if RESOURCE.search(out):
            raise StoreError("resource_limit", f"checking {module}'s axioms ran out: {said}")
        m = re.search(r"not an allowed axiom: (\S+)", out)
        if m:
            return (
                ("sorry" if m.group(1) == "sorryAx" else "nonstandard_axiom"),
                f"{module}: {m.group(0)}",
                step,
            )
        if "implemented_by" in out or "extern" in out:
            return "compiled_code", f"{module}: {said}", step
        return "nonstandard_axiom", f"{module}: {out.strip()[-500:]}", step
    m = re.search(r"and (\d+) from bv_decide", out)
    if not m:
        raise StoreError("tool_failed", f"tests/check_axioms.lean said something else about {module}: {out}")
    if m.group(1) != "0":
        return "nonstandard_axiom", f"{module}: {m.group(1)} of bv_decide's axioms", step
    return None, f"{module}: {said}", step


def replay_check(module: str, env: dict[str, str]) -> tuple[str | None, str, core.Step]:
    code, out = run(["leanchecker", module], env)
    step = core.Step("leanchecker", code, None, out)
    if code != 0:
        if RESOURCE.search(out):
            raise StoreError("resource_limit", f"replaying {module} ran out: {out[-300:]}")
        if code < 0 or code >= 128:
            # leanchecker killed by a signal or a crash exit code: it replayed nothing, so this decides
            # nothing about the module. An error, not a refusal of the lemma.
            raise StoreError("tool_failed", f"leanchecker on {module} was killed (exit {code})")
        return "replay_failed", f"{module}: {out.strip()[-500:]}", step
    return None, f"{module}: replayed", step


# Each module's axiom audit and kernel replay, as trust_checks ran them, for irlean.verdict.
type Steps = dict[str, dict[str, core.Step]]
# Each module's refusals, as codes and details.
type Refusals = dict[str, list[tuple[str, str]]]


def trust_checks(modules: list[str], env: dict[str, str]) -> tuple[Refusals, Steps]:
    """Each module's axioms and kernel replay, a few at a time. Maps a module to the refusals it earned, and
    to how each check's process ended."""
    found: Refusals = {m: [] for m in modules}
    steps: Steps = {m: {} for m in modules}
    jobs = int(os.environ.get("LEAN_JOBS", "2"))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, min(jobs, 4))) as pool:
        futures = {pool.submit(fn, m, env): m for m in modules for fn in (axiom_check, replay_check)}
        for f in concurrent.futures.as_completed(futures):
            reason, detail, step = f.result()
            steps[futures[f]][step.name] = step
            if reason:
                found[futures[f]].append((reason, detail))
    return found, steps


def proved(result: dict[str, Any], compiled: core.Step, steps: Steps) -> None:
    """That irlean.verdict calls a lemma the bar didn't refuse proved: its module compiled, passed the axiom
    audit and was replayed by the kernel. It always should: anything else is a bug here."""
    if result["status"] == "refused":
        return
    ran = steps.get(result.get("module") or "", {})
    decision = core.decide(
        core.Verdict.PROVED,
        core.Evidence(
            lean=compiled,
            replay=ran.get("leanchecker"),
            axioms=ran.get("check_axioms"),
            checks={"admission": not result["reasons"]},
        ),
    )
    if not decision.granted:
        raise StoreError("tool_failed", f"{result['name']} met the bar, and isn't proved: {decision.detail}")


# ------------------------------------------------------------------------------------------------------------
# The facts Lean computes about each lemma, and the verdict on them


def lean_facts(
    lemmas: list[str],
    catalog: list[str],
    imports: list[str],
    paths: list[Path],
    modules: list[str] | None = None,
    catalog_keys: bool = False,
    sites: list[str] | None = None,
) -> dict[str, Any]:
    """What `StoreTool.check` finds about each lemma, in a Lean process that imports `imports`: `lemmas`, the
    facts about each, with the theorems among `sites` that use it, and `catalog`, each stored lemma's key, if
    asked for."""
    WORK.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=WORK) as tmp:
        req = Path(tmp) / "request.json"
        req.write_text(
            json.dumps(
                {
                    "lemmas": lemmas,
                    "catalog": catalog,
                    "modules": modules or [],
                    "counterPrefix": COUNTER_PREFIX,
                    "heartbeats": TRIVIALITY_HEARTBEATS,
                    "triviality": True,
                    "catalogKeys": catalog_keys,
                    "sites": sites or [],
                }
            )
        )
        driver = Path(tmp) / "Check.lean"
        driver.write_text(
            "".join(f"import {m}\n" for m in ["StoreTool", *imports]) + "\nrun_meta StoreTool.check\n"
        )
        code, out = lean([str(driver)], {**lean_env(*paths), "LEMMA_STORE_REQUEST": str(req)})
        if code != 0:
            raise StoreError(
                "resource_limit" if RESOURCE.search(out) else "tool_failed",
                f"the checker failed:\n{out[-4000:]}",
            )
        return json_line(out)


def verdict(fact: dict[str, Any], entry: dict[str, Any], keys: dict[str, str]) -> dict[str, Any]:
    """The status and reasons for one lemma, from its facts, its index entry and the keys of the lemmas before
    it."""
    reasons: list[dict[str, str]] = []

    def refuse(code: str, detail: str) -> None:
        reasons.append({"code": code, "rule": REASONS[code][0], "detail": detail})

    name = fact["name"]
    if fact.get("limit"):
        raise StoreError("resource_limit", f"checking {name} ran out, which decides nothing: {fact['limit']}")
    if not fact.get("found"):
        refuse("not_found", name)
        return {"name": name, "status": "refused", "reasons": reasons}
    if fact["kind"] != "theorem":
        refuse("not_a_theorem", f"{name} is a {fact['kind']}")
    extra = [a for a in fact["axioms"] if a not in STANDARD_AXIOMS]
    if "sorryAx" in extra:
        refuse("sorry", "rests on sorryAx")
    elif extra:
        refuse("nonstandard_axiom", "rests on " + ", ".join(extra))
    wide = [w for w in fact["literal_widths"] if w != 1]
    if wide and not entry.get("fixed_width_reason"):
        refuse("fixed_width", "stated at width " + ", ".join(map(str, wide)))
    for h in fact["hypotheses"]:
        if h["status"] not in ("ok", "typing"):
            refuse(
                "hypothesis_unwitnessed",
                f"{h['binder']} ({h['statement']}): {h['status']} {h['counterexample']}, which has to state: "
                f"{h['expected']}",
            )
    w = fact.get("witness")
    if w and w["status"] != "ok":
        refuse("hypotheses_unsatisfiable", f"{w['status']} {w['name']}, which has to state: {w['expected']}")
    if fact["normal_form"] is not None:
        refuse("not_normal", f"the normalizer makes it {fact['normal_form']}")
    key = key_of(fact["key_text"])
    if key in keys and keys[key] != name:
        refuse("duplicate", f"the same key as {keys[key]}")
    swapped = fact.get("swapped_key_text")
    if swapped and key_of(swapped) in keys and keys[key_of(swapped)] != name:
        refuse("duplicate", f"the same key, the other way round, as {keys[key_of(swapped)]}")
    if fact["subsumed_by"]:
        refuse("subsumed", "an instance of " + ", ".join(fact["subsumed_by"]))
    if fact["closed_by"]:
        refuse("trivial", "closed by " + ", ".join(fact["closed_by"]))
    if fact["replay_ms"] is None:
        refuse("replay_failed", "the kernel rejected it, checked again under a fresh name")
    elif fact["replay_ms"] > REPLAY_LIMIT_MS:
        refuse("slow", f"{fact['replay_ms']:.0f} ms")
    if fact["literal_constants"] and not entry.get("constant_reason"):
        refuse("unlifted_constant", ", ".join(fact["literal_constants"]))
    if not entry.get("provenance"):
        refuse("no_provenance", "no provenance recorded")
    if entry.get("key") and entry["key"] != key:
        refuse("statement_changed", f"recorded {entry['key']}, now {key}")
    users = sorted({u["theorem"] for u in fact["used_by"]})
    status = "refused" if reasons else ("admitted" if len(users) >= 2 else "candidate")
    return {
        "name": name,
        "module": fact.get("module"),
        "status": status,
        "reasons": reasons,
        "key": key,
        "statement": fact["statement"],
        "hypotheses": [
            {
                "binder": h["binder"],
                "statement": h["statement"],
                "counterexample": h["counterexample"],
                "status": h["status"],
            }
            for h in fact["hypotheses"]
        ],
        "witness": (fact["witness"] or {}).get("name"),
        "widths": "fixed" if wide else "every",
        "used_by": users,
        # The rewrites, by the inventory's ID, whose theorems in the `Peephole` library use it.
        "rewrites": sorted(t.removeprefix("Peephole.") for t in fact.get("rewrites", [])),
        "replay_ms": fact["replay_ms"],
        "axioms": fact["axioms"],
    }


def module_refusals(
    result: dict[str, Any], trust: dict[str, list[tuple[str, str]]], counter_trust: list[tuple[str, str]]
) -> None:
    """Adds the refusals of a lemma's module, and of the counterexamples' modules, to its result."""
    extra = trust.get(result.get("module") or "", []) + counter_trust
    for code, detail in extra:
        result["reasons"].append({"code": code, "rule": REASONS[code][0], "detail": detail})
    if extra:
        result["status"] = "refused"


# ------------------------------------------------------------------------------------------------------------
# Commands


def store_version(index: dict[str, Any]) -> dict[str, Any]:
    return {
        "lean": toolchain(),
        "normalizer": index["version"]["normalizer"],
        "sources": sources_hash(lemma_modules(index) + counter_modules()),
    }


def check(write: bool) -> tuple[dict[str, Any], int]:
    started = time.monotonic()
    index = read_index()
    timings: dict[str, float] = {}
    peephole = peephole_imports()
    if write:
        ROOT_MODULE.write_text(generated_root(index))
        code, out = run(["lake", "build", "LemmaStore", "StoreTool", "Peephole"])
        if code != 0:
            raise StoreError("does_not_check", f"lake build failed:\n{out[-4000:]}")
    elif ROOT_MODULE.read_text() != generated_root(index):
        raise StoreError(
            "index_invalid",
            f"{ROOT_MODULE} doesn't list what {INDEX} does: run `tools/store/store.py check --write`",
        )
    built = lake_built(["LemmaStore", "StoreTool", "Peephole"])
    timings["build_seconds"] = time.monotonic() - started

    t = time.monotonic()
    consumer_dir = WORK / "consumers"
    build_consumers(index, consumer_dir)
    timings["consumers_seconds"] = time.monotonic() - t

    t = time.monotonic()
    env = lean_env(consumer_dir)
    held = lemma_modules(index)
    counters = counter_modules()
    trust, steps = trust_checks(held + counters, env)
    counter_trust = [r for m in counters for r in trust[m]]
    timings["trust_seconds"] = time.monotonic() - t

    t = time.monotonic()
    names = [e["name"] for e in index["lemmas"]]
    facts = lean_facts(
        names,
        names,
        ["LemmaStore", "LemmaStore.Counter", *[c["module"] for c in consumers(index)], *peephole],
        [consumer_dir],
        sites=site_theorems(),
    )["lemmas"]
    timings["facts_seconds"] = time.monotonic() - t

    keys: dict[str, str] = {}
    results = []
    by_name = {e["name"]: e for e in index["lemmas"]}
    for fact in facts:
        entry = by_name[fact["name"]]
        # Writing the index is how a changed statement, or a new normalizer, gets its key recorded.
        r = verdict(fact, {**entry, "key": None} if write else entry, keys)
        module_refusals(r, trust, counter_trust)
        proved(r, built, steps)
        r["family"] = entry.get("family")
        r["provenance"] = entry.get("provenance")
        if r.get("key"):
            keys.setdefault(r["key"], r["name"])
        results.append(r)

    version = store_version(index)
    drift = []
    for r in results:
        entry = by_name[r["name"]]
        if r["status"] != "refused" and entry.get("status") != r["status"]:
            drift.append(f"{r['name']}: the index says {entry.get('status')}, and it's {r['status']}")
    if write:
        for r in results:
            entry = by_name[r["name"]]
            if r["status"] == "refused":
                continue
            entry.update(
                {
                    "module": r["module"],
                    "key": r["key"],
                    "status": r["status"],
                    "widths": r["widths"],
                    "hypotheses": [h["counterexample"] for h in r["hypotheses"] if h["status"] == "ok"],
                    "witness": r["witness"],
                    "used_by": r["used_by"],
                }
            )
            set_rewrites(entry, r["rewrites"])
        index["version"] = version
        write_index(index)
        drift = []

    refused = [r for r in results if r["status"] == "refused"]
    timings["total_seconds"] = time.monotonic() - started
    report = {
        "schema": SCHEMA,
        "status": "refused" if refused or drift else "ok",
        "store": {
            "version": version,
            "recorded_version": index["version"],
            "index": str(INDEX.relative_to(ROOT)),
        },
        "counts": counts(results),
        "drift": drift,
        "lemmas": results,
        "timings": {k: round(v, 2) for k, v in timings.items()},
    }
    WORK.mkdir(parents=True, exist_ok=True)
    (WORK / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    return report, EXIT["refused"] if refused or drift else EXIT["ok"]


def set_rewrites(entry: dict[str, Any], rewrites: list[str]) -> None:
    """An entry's optional `rewrites`: the rewrites whose theorems use the lemma, only when there are some."""
    if rewrites:
        entry["rewrites"] = rewrites
    else:
        entry.pop("rewrites", None)


def counts(results: list[dict[str, Any]]) -> dict[str, Any]:
    by_status = {s: sum(1 for r in results if r["status"] == s) for s in STATUSES}
    by_family: dict[str, dict[str, int]] = {}
    for r in results:
        fam = by_family.setdefault(r.get("family") or "", dict.fromkeys(STATUSES, 0))
        fam[r["status"]] += 1
    reasons: dict[str, int] = {}
    for r in results:
        for code in {x["code"] for x in r["reasons"]}:
            reasons[code] = reasons.get(code, 0) + 1
    return {
        **by_status,
        "lemmas": len(results),
        "hypotheses_witnessed": sum(
            1 for r in results for h in r.get("hypotheses", []) if h["status"] == "ok"
        ),
        "by_family": by_family,
        "refusals": reasons,
    }


def lookup(statement: str, imports: list[str]) -> tuple[dict[str, Any], int]:
    started = time.monotonic()
    lake_built(["LemmaStore", "StoreTool"])
    index = read_index()
    status_of = {e["name"]: e.get("status") for e in index["lemmas"]}
    WORK.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=WORK) as tmp:
        driver = Path(tmp) / "Lookup.lean"
        driver.write_text(
            "".join(f"import {m}\n" for m in ["StoreTool", "LemmaStore.Select", *imports])
            + "\nopen IRLean\n\n"
            + f"def StoreQuery.statement : Prop :=\n  {statement}\n\n"
            + "run_meta StoreTool.lookup ``StoreQuery.statement\n"
        )
        code, out = lean([str(driver)], lean_env())
    if code != 0:
        if RESOURCE.search(out):
            raise StoreError("resource_limit", out[-2000:])
        if code < 0 or code >= 128:
            raise StoreError("tool_failed", f"the lookup driver was killed (exit {code}): {out[-2000:]}")
        errors = [e.split("error:", 1)[-1].strip() for e in lean_errors(out)]
        raise StoreError("statement_invalid", "; ".join(errors) or out[-2000:])
    found = json_line(out)
    for m in found["exact"] + found["instances"]:
        m["status"] = status_of.get(m["name"])
        if "side_conditions" in m:
            m["closes"] = m["free_variables"] == 0 and all(s["closed_by"] for s in m["side_conditions"])
    status = "exact" if found["exact"] else "instance" if found["instances"] else "none"
    result = {
        "schema": LOOKUP_SCHEMA,
        "status": status,
        "query": {"statement": found["statement"], "key": key_of(found["key_text"])},
        "store": {"version": index["version"], "lemmas": len(index["lemmas"])},
        "exact": found["exact"],
        "instances": found["instances"],
        "elapsed_seconds": round(time.monotonic() - started, 2),
    }
    return result, EXIT["ok"] if status != "none" else EXIT["not_found"]


def add(
    file: Path | None,
    existing: list[str],
    family: str,
    provenance: str,
    dry_run: bool,
    extra_imports: list[str] | None = None,
) -> tuple[dict[str, Any], int]:
    """Judges new lemmas against the store, and adds them if they're admitted or candidates."""
    started = time.monotonic()
    peephole = peephole_imports()
    built = lake_built(["LemmaStore", "StoreTool", "Peephole"])
    index = read_index()
    catalog = [e["name"] for e in index["lemmas"]]
    WORK.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(dir=WORK, prefix="add-"))
    try:
        consumer_dir = WORK / "consumers"
        build_consumers(index, consumer_dir)
        paths = [work, consumer_dir]
        imports = [
            "LemmaStore",
            "LemmaStore.Counter",
            *[c["module"] for c in consumers(index)],
            *peephole,
            *(extra_imports or []),
        ]
        modules: list[str] = []
        candidate = built
        if file is not None:
            if not file.exists():
                raise StoreError("input_not_found", f"{file} doesn't exist")
            bad = [
                m
                for m in imports_of(file)
                if m == "LemmaStore" or m.startswith(("LemmaStore.Select", "LemmaStore.Counter"))
            ]
            if bad:
                raise StoreError(
                    "invalid_request",
                    f"{file} imports {', '.join(bad)}, which would import it back once stored",
                )
            code, out = lean(["-o", str(work / "StoreCandidate.olean"), str(file)], lean_env(*paths))
            candidate = core.Step("lean", code, None, out)
            if code != 0:
                if RESOURCE.search(out):
                    raise StoreError("resource_limit", out[-2000:])
                if code < 0 or code >= 128:
                    raise StoreError(
                        "tool_failed", f"compiling the candidate was killed (exit {code}): {out[-2000:]}"
                    )
                errors = lean_errors(out)
                result = {
                    "schema": ADMISSION_SCHEMA,
                    "status": "refused",
                    "lemmas": [],
                    "reasons": [
                        {
                            "code": "does_not_check",
                            "rule": "1",
                            "detail": "\n".join(errors)[:2000] or out[-2000:],
                        }
                    ],
                    "elapsed_seconds": round(time.monotonic() - started, 2),
                }
                return result, EXIT["refused"]
            modules = ["StoreCandidate"]
            imports.append("StoreCandidate")
        found = lean_facts(
            existing, catalog, imports, paths, modules=modules, catalog_keys=True, sites=site_theorems()
        )
        # Each new lemma's module, read as data and replayed, as `check` does for every stored lemma's.
        held = sorted(
            {
                f["module"]
                for f in found["lemmas"]
                if f.get("module") and not f.get("limit") and f["name"] not in catalog
            }
        )
        module_reasons, steps = trust_checks(held, lean_env(*paths))
        keys: dict[str, str] = {}
        for p in found["catalog"]:
            keys.setdefault(key_of(p["key_text"]), p["name"])
            if p["swapped_key_text"]:
                keys.setdefault(key_of(p["swapped_key_text"]), p["name"])
        results = []
        for fact in found["lemmas"]:
            if fact["name"] in catalog:
                continue
            entry = {"provenance": provenance, "family": family}
            r = verdict(fact, entry, keys)
            for code, detail in module_reasons.get(fact.get("module") or "", []):
                r["reasons"].append({"code": code, "rule": REASONS[code][0], "detail": detail})
                r["status"] = "refused"
            proved(r, candidate if fact.get("module") == "StoreCandidate" else built, steps)
            if r.get("key"):
                keys.setdefault(r["key"], r["name"])
            results.append(r)
        if not results:
            raise StoreError(
                "invalid_request", "nothing to add: no theorem outside the counterexamples' namespace"
            )
        refused = [r for r in results if r["status"] == "refused"]
        stored = False
        if not refused and not dry_run:
            store_lemmas(file, results, family, provenance, index)
            stored = True
        result = {
            "schema": ADMISSION_SCHEMA,
            "status": "refused" if refused else "accepted",
            "stored": stored,
            "lemmas": results,
            "elapsed_seconds": round(time.monotonic() - started, 2),
        }
        return result, EXIT["refused"] if refused else EXIT["ok"]
    finally:
        shutil.rmtree(work, ignore_errors=True)


def store_lemmas(
    file: Path | None, results: list[dict[str, Any]], family: str, provenance: str, index: dict[str, Any]
) -> None:
    """Writes accepted lemmas into the store: a file becomes a module of its own,
    `LemmaStore.Lemmas.<name>`."""
    module = None
    if file is not None:
        OWNED.mkdir(parents=True, exist_ok=True)
        target = OWNED / file.name
        if target.exists():
            raise StoreError("invalid_request", f"{target} already exists")
        shutil.copyfile(file, target)
        module = "LemmaStore.Lemmas." + file.stem
    for r in results:
        index["lemmas"].append(
            {
                "name": r["name"],
                "module": module or r["module"],
                "family": family,
                "provenance": provenance,
                "key": r["key"],
                "status": r["status"],
                "widths": r["widths"],
                "hypotheses": [h["counterexample"] for h in r["hypotheses"] if h["status"] == "ok"],
                "witness": r["witness"],
                "used_by": r["used_by"],
            }
        )
        set_rewrites(index["lemmas"][-1], r["rewrites"])
    write_index(index)
    ROOT_MODULE.write_text(generated_root(index))
    code, out = run(["lake", "build", "LemmaStore", "StoreTool"])
    if code != 0:
        raise StoreError("does_not_check", f"the store doesn't build with them:\n{out[-4000:]}")


def forget(name: str, reason: str) -> tuple[dict[str, Any], int]:
    """Takes a lemma out of the store, and records why. A lemma the store owns loses its module too, if
    nothing else stored is in it; one proved elsewhere, such as in `IRLean`, stays there and only leaves the
    catalog."""
    index = read_index()
    entry = next((e for e in index["lemmas"] if e["name"] == name), None)
    if entry is None:
        raise StoreError("not_found", f"{name} isn't in the store")
    index["lemmas"].remove(entry)
    removed = None
    module = entry["module"]
    if module.startswith("LemmaStore.Lemmas.") and not any(e["module"] == module for e in index["lemmas"]):
        f = module_file(module)
        if f is not None and f.exists():
            f.unlink()
            removed = str(f.relative_to(ROOT))
    index.setdefault("forgotten", []).append(
        {
            "name": name,
            "key": entry.get("key"),
            "status": entry.get("status"),
            "reason": reason,
            "date": datetime.date.today().isoformat(),
        }
    )
    write_index(index)
    ROOT_MODULE.write_text(generated_root(index))
    return {"schema": SCHEMA, "status": "ok", "forgotten": name, "removed_module": removed}, EXIT["ok"]


def capabilities() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "schemas": {"check": SCHEMA, "lookup": LOOKUP_SCHEMA, "add": ADMISSION_SCHEMA, "index": INDEX_SCHEMA},
        "statuses": STATUSES,
        "reasons": {k: {"rule": v[0], "meaning": v[1]} for k, v in REASONS.items()},
        "lookup_tiers": {
            "exact": "The statement's key, after normalization, is a stored lemma's, either way round",
            "instance": "A stored lemma's conclusion, instantiated, is the statement's, with its hypotheses "
            "left as side conditions. `closes` says whether `decide` closes every one and no variable is "
            "left free",
        },
        "exit_codes": EXIT,
        "limits": {"replay_ms": REPLAY_LIMIT_MS, "triviality_heartbeats": TRIVIALITY_HEARTBEATS},
    }


def emit(result: dict[str, Any], as_json: bool, pretty: bool) -> None:
    if as_json or pretty:
        print(json.dumps(result, indent=2 if pretty else None, ensure_ascii=False))
        return
    if result.get("schema") == SCHEMA and "counts" in result:
        c = result["counts"]
        for r in result["lemmas"]:
            mark = {"admitted": "ok  ", "candidate": "cand", "refused": "FAIL"}[r["status"]]
            why = "; ".join(f"{x['code']}: {x['detail']}" for x in r["reasons"])
            print(f"{mark}  {r['name']}" + (f"  {why}" if why else f"  ({len(r['used_by'])} uses)"))
        for d in result["drift"]:
            print(f"FAIL  {d}: run `tools/store/store.py check --write`")
        print(
            f"{c['lemmas']} lemmas: {c['admitted']} admitted, {c['candidate']} candidates, "
            f"{c['refused']} refused, in {result['timings']['total_seconds']} s"
        )
        return
    print(json.dumps(result, indent=2, ensure_ascii=False))


def fail(reason: str, detail: str, as_json: bool) -> NoReturn:
    result = {"schema": SCHEMA, "status": "error", "reason": reason, "detail": detail}
    if as_json:
        print(json.dumps(result))
    else:
        print(f"error: {reason}: {detail}", file=sys.stderr)
    sys.exit(EXIT["error"])


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("check", help="check every stored lemma against the bar")
    p.add_argument("--write", action="store_true", help="write what's computed into the index, and rebuild")
    p = sub.add_parser("lookup", help="find stored lemmas that prove a statement")
    p.add_argument("--statement", required=True, help="a closed proposition, elaborated with `open IRLean`")
    p.add_argument(
        "--import", dest="imports", action="append", default=[], help="a module the statement needs"
    )
    p = sub.add_parser("add", help="judge new lemmas, and store them if they pass")
    p.add_argument("file", nargs="?", type=Path, help="a Lean file of lemmas and their counterexamples")
    p.add_argument("--existing", nargs="+", default=[], help="lemmas already proved in an imported module")
    p.add_argument(
        "--import", dest="imports", action="append", default=[], help="a module holding an --existing lemma"
    )
    p.add_argument("--family", required=True)
    p.add_argument("--provenance", required=True, help="where it came from: a pull request, file or tool run")
    p.add_argument("--dry-run", action="store_true", help="judge only, and change nothing")
    p = sub.add_parser("forget", help="take a lemma out of the store, and record why")
    p.add_argument("name")
    p.add_argument("--reason", required=True)
    p = sub.add_parser("report", help="the last check's numbers")
    sub.add_parser("capabilities", help="the schemas, statuses and reasons, as JSON")
    for p in sub.choices.values():
        p.add_argument("--json", action="store_true", help="answer in JSON")
        p.add_argument("--pretty", action="store_true", help="answer in indented JSON")
    args = parser.parse_args()
    as_json = args.json or args.pretty
    try:
        if args.command == "check":
            result, code = check(args.write)
        elif args.command == "lookup":
            result, code = lookup(args.statement, args.imports)
        elif args.command == "add":
            if (args.file is None) == (not args.existing):
                fail("invalid_request", "give a file or --existing, not both or neither", as_json)
            result, code = add(
                args.file, args.existing, args.family, args.provenance, args.dry_run, args.imports
            )
        elif args.command == "forget":
            result, code = forget(args.name, args.reason)
        elif args.command == "report":
            path = WORK / "report.json"
            if not path.exists():
                fail("no_report", f"{path} doesn't exist: run `tools/store/store.py check` first", as_json)
            report = json.loads(path.read_text())
            result = {k: report[k] for k in ("schema", "status", "store", "counts", "timings")}
            # Candidates the fewest proofs use first: the ones to look at before forgetting any.
            result["candidates"] = sorted(
                (
                    {"name": r["name"], "uses": len(r["used_by"])}
                    for r in report["lemmas"]
                    if r["status"] == "candidate"
                ),
                key=lambda c: (c["uses"], c["name"]),
            )
            code = EXIT["ok"]
        else:
            result, code = capabilities(), EXIT["ok"]
    except StoreError as e:
        fail(e.reason, e.detail, as_json)
    with contextlib.suppress(BrokenPipeError):
        emit(result, args.json, args.pretty)
    sys.exit(code)


if __name__ == "__main__":
    main()
