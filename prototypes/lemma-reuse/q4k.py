#!/usr/bin/env python3
"""Splits each theorem that proves llama.cpp's q4_K kernels rewritten with VNNI into lemmas the 34 places
share, saves them, and continues each theorem with them.

A prototype, for research only, like lemmas.py next to it, and docs/lemma-reuse.md says what it found. The
q4_K proof is on the branch feat/prove-llvm-optimization-1, which isn't merged, so this runs against a
checkout of it, built, in its dev shell. From that checkout's pinned llama.cpp, it compiles the kernels,
rewrites them and cuts out the 34 places as tests/llama.py does, and checks every slice against the branch's
committed manifest. Then for each place, in order:

1. It checks the theorem as tests/llama.py writes it, with `vnni_slice`, for comparison.
2. It reads both slices' Lean. What both compute in the same words is how the operands are built from loads
   and arguments, and what differs is the rewrite. The values the differing part reads from the shared one are
   the frontier, the cut.
3. It states the differing part as a core lemma about any values at the frontier, and for each frontier
   value, each fact in a small vocabulary as a lemma about how it's computed, from only the arguments it uses.
   Each is named by a hash of its statement, so the same lemma from any place has the same name.
4. It looks for each in the store, and checks the rest in modules of their own: the facts with `vnni_facts`,
   and the core with what `vnni_slice` does after running both slices, with the facts that checked as
   hypotheses.
5. It continues the place's theorem: it runs both slices as `vnni_slice` does, then applies the core lemma to
   the facts.
6. It checks the theorem's axioms with the branch's tests/check_axioms.lean, and replays it and its lemmas
   through leanchecker.

usage: prototypes/lemma-reuse/q4k.py --repo CHECKOUT [PLACE ...] [--store DIR] [--fresh] [--report FILE]

Run it in the checkout's dev shell, after `lake build` and building build/ir-lean there.
"""

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import platform
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import lemmas  # noqa: E402
from lemmas import Lean, Lemma, Store  # noqa: E402

STORE = HERE / "q4k" / "store"
PROOFS = HERE / "q4k" / "proofs"
LET = re.compile(r"^    let (\w+) := (.*)$")
NAME = re.compile(r"\b(v\w+|vnni_\w+)\b")
# What a frontier value can be said to be, by element width, as tests/llama/Vnni.lean defines it.
VOCABULARY = {8: "Nibbles", 16: "Pairs"}
# A failed fact or core, or one run past this, says nothing more.
OPEN = "IRLean Llama.Vnni"


@dataclass
class Slice:
    """A slice's generated Lean: its `let`s in order, what it returns, and its parameters."""

    lets: dict[str, str]
    order: list[str]
    ret: str
    signature: str
    params: dict[str, str]


def read_slice(path: Path, function: str) -> Slice:
    text = path.read_text()
    lets: dict[str, str] = {}
    order: list[str] = []
    ret = ""
    for line in text.splitlines():
        if m := LET.match(line):
            lets[m.group(1)] = m.group(2)
            order.append(m.group(1))
        elif line.strip().startswith("ret "):
            ret = line.strip()[4:]
    m = re.search(rf"noncomputable def {function} (.*?) : Outcome", text)
    if m is None:
        raise ValueError(f"no {function} in {path.name}")
    params = dict(re.findall(r"\((\w+) : (.*?)\)(?= \(|$)", m.group(1)))
    return Slice(lets, order, ret, m.group(1), params)


def ir_types(ll: Path) -> dict[str, str]:
    """Each vector value's Lean type, from the instruction that defines it."""
    types = {}
    for line in ll.read_text().splitlines():
        m = re.match(r"\s*%([\w.]+) = (.*)$", line)
        if not m:
            continue
        rest = m.group(2)
        if (c := re.search(r" to (<\d+ x i\d+>)\s*$", rest)) and re.match(
            r"(bitcast|zext|sext|trunc) ", rest
        ):
            t = c.group(1)
        elif rest.startswith("shufflevector"):
            elem = re.search(r"<\d+ x (i\d+)> ", rest)
            lanes = re.findall(r"<(\d+) x i32> (?:<|zeroinitializer|splat)", rest)
            t = f"<{lanes[-1]} x {elem.group(1)}>" if elem and lanes else None
        elif (c := re.match(r"(?:tail )?call (<\d+ x i\d+>) @", rest)) or (
            c := re.match(r"\w+(?: \w+)* (<\d+ x i\d+>) ", rest)
        ):
            t = c.group(1)
        else:
            t = None
        if t and (v := re.fullmatch(r"<(\d+) x i(\d+)>", t)):
            types[re.sub(r"\W", "_", m.group(1))] = f"Vec {v.group(1)} {v.group(2)}"
    return types


def inline(lets: dict[str, str], expr: str, stop: dict[str, str]) -> str:
    """`expr` with each `let` it reads written out, down to the names in `stop`, which become what they map
    to."""

    def sub(m: re.Match[str]) -> str:
        name = m.group(1)
        if name in stop:
            return stop[name]
        if name in lets:
            text = inline(lets, lets[name], stop)
            return text if re.fullmatch(r"\w+", text) else f"({text})"
        return name

    return NAME.sub(sub, expr)


def escape(text: str) -> str:
    """Lean text, safe to put in a statement that `str.format` fills in later."""
    return text.replace("{", "{{").replace("}", "}}")


def canonical(names: list[str], prefix: str) -> dict[str, str]:
    return {n: f"{prefix}{i}" for i, n in enumerate(dict.fromkeys(names))}


@dataclass
class Split:
    """Where a place's proof is cut: the frontier, each value's type, and the two sides above it."""

    frontier: list[str]
    types: dict[str, str]
    src: Slice
    tgt: Slice


def cut(src: Slice, tgt: Slice, types: dict[str, str]) -> Split:
    shared = {n for n in src.lets if tgt.lets.get(n) == src.lets[n]} | set(src.params)
    differ = [(src, n) for n in src.order if n not in shared] + [
        (tgt, n) for n in tgt.order if n not in shared
    ]
    frontier = []
    for side, name in differ:
        frontier += [r for r in NAME.findall(side.lets[name]) if r in shared]
    for side in (src, tgt):
        frontier += [r for r in NAME.findall(side.ret) if r in shared]
    frontier = list(dict.fromkeys(frontier))
    missing = [n for n in frontier if n not in types and n not in src.params]
    if missing:
        raise ValueError(f"no type for {missing}")
    return Split(frontier, {**types, **src.params}, src, tgt)


def fact_lemma(split: Split, value: str, predicate: str, place: str) -> tuple[Lemma, list[str]]:
    """That `value` has `predicate`, from how the shared part computes it, over only the arguments it reads.
    Returns the lemma and the arguments to apply it to."""
    expr = inline(split.src.lets, split.src.lets[value], {})
    params = [p for p in NAME.findall(expr) if p in split.src.params]
    names = canonical(params, "p")
    text = NAME.sub(lambda m: names.get(m.group(1), m.group(1)), expr)
    binders = " ".join(f"({names[p]} : {split.src.params[p]})" for p in names)
    lemma = Lemma(
        "fact",
        f"theorem {{name}} {escape(binders)} :\n    {predicate} ({escape(text)})",
        "  vnni_facts",
        imports=("Vnni",),
        opens=OPEN,
        tool="q4k.py",
        doc=f"{predicate}, of how {place}'s `{value}` is computed.",
    )
    return lemma, list(names)


def core_lemma(split: Split, facts: list[tuple[int, str]], place: str) -> Lemma:
    """The rewrite agrees with clang's code on any values at the frontier with the facts given, as `(index,
    predicate)`."""
    names = canonical(split.frontier, "x")
    lhs = inline(split.tgt.lets, split.tgt.ret, names)
    rhs = inline(split.src.lets, split.src.ret, names)
    binders = " ".join(f"({names[n]} : {split.types[n]})" for n in split.frontier)
    hyps = " ".join(f"(h{i} : {p} x{i})" for i, p in facts)
    return Lemma(
        "core",
        f"theorem {{name}} {escape(binders)}\n    {hyps} :\n    {escape(lhs)} =\n      {escape(rhs)}",
        "  refine final (k := 8) ?_ (by decide) ?_ ?_\n  vnni_inv\n"
        "  all_goals first | assumption | vnni_facts",
        imports=("Vnni",),
        opens=OPEN,
        tool="q4k.py",
        doc=f"What {place}'s rewrite computes from its operands is what clang's code does, given the facts.",
    )


def original(name: str, sig: str, args: str) -> tuple[str, str]:
    """The theorem tests/llama.py writes for a place, and the first steps of its proof, which run both
    slices."""
    up = name.upper()
    statement = f"theorem {name}_same {sig} :\n    {up}Tgt.{name}_tgt {args} = {up}Src.{name}_src {args}"
    head = (
        f"  unfold {up}Tgt.{name}_tgt {up}Src.{name}_src\n  rw [run, run]\n"
        f"  simp only [{up}Tgt.{name}_tgt.step, {up}Src.{name}_src.step, ret, Outcome.ok]\n"
        "  refine congrArg (fun x => some (Except.ok x)) ?_\n"
    )
    return statement, head


# ------------------------------------------------------------------------------------------------------------
# The branch's pipeline, up to the generated Lean.


def run(args: list, env: dict | None = None, cwd: Path | None = None) -> str:
    r = subprocess.run([str(a) for a in args], env=env, cwd=cwd, capture_output=True, text=True, check=False)
    if r.returncode != 0:
        raise RuntimeError(f"{' '.join(map(str, args))}\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
    return r.stdout


def cross_flags(work: Path) -> list[str]:
    """What clang needs to compile for x86-64 Linux here, as the branch did on a Ryzen. On a Mac, the dev
    shell's libc++ turns on Apple's availability markup, which has no meaning for Linux, so a copy of its
    configuration turns it off."""
    if platform.system() == "Linux" and platform.machine() == "x86_64":
        return []
    flags = [f.replace("-isystem", "-idirafter") for f in os.environ["PROOF_CFLAGS"].split()]
    probe = subprocess.run(
        ["clang++", "-x", "c++", "-E", "-v", "-"], input="", capture_output=True, text=True, check=False
    )
    found = [
        Path(d)
        for d in re.findall(r"(/[^\s\"]*/include/c\+\+/v1)", probe.stderr)
        if Path(d, "__config_site").exists()
    ]
    if found:
        overlay = work / "libcxx-overlay"
        overlay.mkdir(parents=True, exist_ok=True)
        config = (found[0] / "__config_site").read_text()
        (overlay / "__config_site").write_text(
            config.replace(
                "#define _LIBCPP_HAS_VENDOR_AVAILABILITY_ANNOTATIONS 1",
                "#define _LIBCPP_HAS_VENDOR_AVAILABILITY_ANNOTATIONS 0",
            )
        )
        flags = ["-isystem", str(overlay), *flags]
    return flags


def prepare(repo: Path, work: Path, lean: Lean) -> tuple[list[dict], dict[str, Any]]:
    """The 34 slice pairs, as the branch makes them, translated and compiled. Returns the slices' index, and
    how they compare with the branch's manifest."""
    # The branch's tests/llama.py, which this checkout doesn't have.
    spec = importlib.util.spec_from_file_location("llama", repo / "tests" / "llama.py")
    assert spec is not None and spec.loader is not None
    llama = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(llama)

    src = Path(os.environ["LLAMA_CPP_SRC"])
    work.mkdir(parents=True, exist_ok=True)
    ll, rw, report = work / "repack.ll", work / "repack.rw.ll", work / "report.json"
    base = [
        "clang++",
        *cross_flags(work),
        *[f"-D{d}" for d in llama.DEFINES],
        *[f"-I{src / i}" for i in llama.INCLUDES],
        *llama.FLAGS,
    ]
    env = {**os.environ, "NIX_HARDENING_ENABLE": ""}
    run([*base, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", ll, src / llama.SOURCE], env)
    llama.rewrite(ll, rw, report)
    slices = work / "slices"
    run([sys.executable, repo / "tests" / "llama" / "slices.py", ll, rw, report, slices])
    index = json.loads((slices / "slices.json").read_text())
    manifest = json.loads(run(["git", "-C", repo, "show", "HEAD:docs/data/llama-manifest.json"]))
    ours = {p.name: llama.sha256(p) for p in slices.glob("*.ll")}
    same = sum(ours.get(k) == v for k, v in manifest["slices_sha256"].items())
    tool = repo / "build" / "ir-lean"
    jobs = []
    for entry in index:
        name = entry["name"]
        for kind, module in (("src", f"{name.upper()}Src"), ("tgt", f"{name.upper()}Tgt")):
            out = work / f"{module}.gen.lean"
            run([tool, slices / f"{name}.{kind}.ll", "--namespace", module, "--no-code", "-o", out])
            jobs.append((module, out.read_text()))
    # As tests/llama.py compiles them: the generated modules leniently, and the proof's library strictly.
    failed = [m for (m, _), c in zip(jobs, lean.map(jobs, strict=False), strict=True) if not c.ok]
    vnni = lean.compile("Vnni", (repo / "tests" / "llama" / "Vnni.lean").read_text())
    if failed or not vnni.ok:
        raise RuntimeError(f"didn't compile: {failed}{'' if vnni.ok else ' Vnni'}")
    return index, {
        "slices_matching_manifest": f"{same} of {len(manifest['slices_sha256'])}",
        "ir_sha256": llama.sha256(ll),
        "manifest_ir_sha256": manifest["ir_sha256"],
    }


# ------------------------------------------------------------------------------------------------------------
# Each place.


def prove_place(
    entry: dict, work: Path, lean: Lean, store: Store, unproved: dict[str, Any], args: Any
) -> dict[str, Any]:
    name = entry["name"]
    # A lemma's .olean is kept for the Vnni.lean it was checked against.
    library = hashlib.sha256((lean.build / "Vnni.lean").read_bytes()).hexdigest()
    up = name.upper()
    report: dict[str, Any] = {
        "place": name,
        "function": entry["function"],
        "value": entry["value"],
        "gaps": [],
    }
    src = read_slice(lean.build / f"{up}Src.lean", f"{name}_src")
    tgt = read_slice(lean.build / f"{up}Tgt.lean", f"{name}_tgt")
    arguments = " ".join(src.params)
    statement, head = original(name, src.signature, arguments)

    started = time.monotonic()
    split = cut(src, tgt, ir_types(work / "slices" / f"{name}.src.ll"))
    report["frontier"] = len(split.frontier)

    # Facts first: the core's hypotheses are the ones that check.
    candidates = []
    for i, value in enumerate(split.frontier):
        if value in src.lets and (width := int(split.types[value].split()[-1])) in VOCABULARY:
            lemma, applied = fact_lemma(split, value, VOCABULARY[width], name)
            candidates.append((i, VOCABULARY[width], lemma, applied))
    # Each lemma once, though two values here may need the same one.
    distinct = {lemma.key: lemma for _, _, lemma, _ in candidates}
    stored = [k for k, lemma in distinct.items() if store.find(lemma) is not None]
    fresh = [k for k in distinct if k not in stored and k not in unproved]
    jobs = [(distinct[k].module, (store.path / f"{distinct[k].module}.lean").read_text()) for k in stored]
    jobs += [(distinct[k].module, distinct[k].source()) for k in fresh]
    results = dict(zip(stored + fresh, lean.map(jobs, extra=library), strict=True))
    mined: list[float] = []
    failed: list[float] = []
    origin = {}
    for k in stored:
        if results[k].ok:
            origin[k] = "store"
            store.used(k, name)
        else:
            report["gaps"].append(f"{distinct[k].module} is in the store but didn't check")
    for k in fresh:
        lemma = distinct[k]
        if results[k].ok:
            store.add(lemma, None, results[k].seconds, name)
            origin[k] = "mined"
            mined.append(results[k].seconds)
        else:
            unproved[k] = {"statement": lemma.statement.format(name=lemma.name, bound=None), "place": name}
            failed.append(results[k].seconds)
    uses = [
        (i, p, lemma, applied, origin[lemma.key])
        for i, p, lemma, applied in candidates
        if lemma.key in origin
    ]

    core = core_lemma(split, [(i, p) for i, p, _, _, _ in uses], name)
    if store.find(core) is not None:
        result = lean.compile(core.module, (store.path / f"{core.module}.lean").read_text(), extra=library)
        store.used(core.key, name)
        core_origin = "store"
    else:
        result = lean.compile(core.module, core.source(), extra=library)
        core_origin = "mined"
        if result.ok:
            store.add(core, None, result.seconds, name)
            mined.append(result.seconds)
    if not result.ok:
        report["gaps"].append(f"the core lemma didn't check: {lemmas.first_error(result.output)}")
    report["lemmas"] = [
        {"lemma": core.full, "kind": "core", "source": core_origin, "check_seconds": round(result.seconds, 2)}
    ] + [
        {"lemma": lemma.full, "kind": f"fact, {predicate}", "source": origin}
        for _, predicate, lemma, _, origin in uses
    ]
    report["facts_tried"] = len(candidates)
    report["facts_proved"] = len(uses)
    report["mined"] = len(mined)
    report["mined_check_seconds"] = round(sum(mined), 2)
    # Facts that don't follow, such as activations being nibbles, cost a check each, once.
    report["failed_fact_seconds"] = round(sum(failed), 2)
    report["lemma_seconds"] = round(time.monotonic() - started, 2)
    if report["gaps"]:
        return report

    holes = " ".join("_" for _ in split.frontier)
    facts = " ".join(f"({lemma.full} {' '.join(applied)})" for _, _, lemma, applied, _ in uses)
    module = f"Split{name}"
    text = (
        "".join(
            f"import {m}\n"
            for m in dict.fromkeys(
                ["Vnni", f"{up}Src", f"{up}Tgt", core.module, *(u[2].module for u in uses)]
            )
        )
        + f"\nopen {OPEN}\n\n/-- {entry['value']} of `{entry['function']}`, rewritten, is what clang's IR "
        + "computes. "
        + "The proof tests/llama.py writes for it, continued with lemmas from the store. -/\n"
        + f"{statement} := by\n{head}  exact {core.full} {holes} {facts}\n"
    )
    result = lean.compile(module, text, fresh=True)
    report["proof"] = {"status": result.status, "seconds": round(result.seconds, 2)}
    if not result.ok:
        report["gaps"].append(f"the continued proof didn't check: {lemmas.first_error(result.output)}")
        return report
    args.proofs.mkdir(parents=True, exist_ok=True)
    (args.proofs / f"{module}.lean").write_text(text)
    return report


def audit(repo: Path, lean: Lean, modules: list[str]) -> dict[str, Any]:
    """Each module's axioms, with the branch's own check, and a replay of each through the kernel."""
    check = (repo / "tests" / "check_axioms.lean").read_text()

    def one(module: str) -> tuple[str, str]:
        r = subprocess.run(
            ["lean", "--stdin"],
            input=check.replace("MODULE", module),
            cwd=repo,
            env=lean.env,
            capture_output=True,
            text=True,
            check=False,
        )
        replay = subprocess.run(
            ["leanchecker", module], cwd=repo, env=lean.env, capture_output=True, text=True, check=False
        )
        if r.returncode != 0 or replay.returncode != 0:
            return (
                module,
                f"FAIL {r.stdout[-500:]}{r.stderr[-300:]}{replay.stdout[-300:]}{replay.stderr[-300:]}",
            )
        return module, r.stdout.strip()

    with concurrent.futures.ThreadPoolExecutor(lean.jobs) as pool:
        return dict(pool.map(one, modules))


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("places", nargs="*", help="places such as s00, in this order. All 34 by default")
    parser.add_argument(
        "--repo", type=Path, required=True, help="a built checkout of the q4_K proof's branch"
    )
    parser.add_argument("--store", type=Path, default=STORE)
    parser.add_argument("--proofs", type=Path, default=PROOFS)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--fresh", action="store_true", help="check the store's lemmas again")
    args = parser.parse_args()
    repo = args.repo.resolve()
    work = repo / "build" / "lemma-reuse-q4k"
    lean = Lean(work / "lean", repo)
    lean.build.mkdir(parents=True, exist_ok=True)
    if args.fresh:
        for stale in lean.build.glob("Lemma_*"):
            stale.unlink()
    started = time.monotonic()
    index, provenance = prepare(repo, work, lean)
    prepared = time.monotonic() - started
    places = [e for e in index if not args.places or e["name"] in args.places]
    if args.places:
        places.sort(key=lambda e: args.places.index(e["name"]))

    # The theorems as tests/llama.py writes them, to compare with.
    originals = []
    for entry in places:
        src = read_slice(lean.build / f"{entry['name'].upper()}Src.lean", f"{entry['name']}_src")
        up = entry["name"].upper()
        statement, _ = original(entry["name"], src.signature, " ".join(src.params))
        tgt, src = f"{up}Tgt.{entry['name']}_tgt", f"{up}Src.{entry['name']}_src"
        tactic = f"  vnni_slice {tgt} {src} {tgt}.step {src}.step\n"
        text = f"import Vnni\nimport {up}Src\nimport {up}Tgt\n\nopen {OPEN}\n\n{statement} := by\n{tactic}"
        originals.append((f"Orig{entry['name']}", text))
    # One at a time, as each continued proof below is checked, so the times compare.
    checked = lean.map(originals, fresh=True, workers=1)
    baseline = {m[4:]: c for m, c in zip([m for m, _ in originals], checked, strict=True)}

    store = Store(args.store.resolve())
    unproved = store.index.setdefault("unproved", {})
    reports = []
    for entry in places:
        r = prove_place(entry, work, lean, store, unproved, args)
        b = baseline[entry["name"]]
        r["original"] = {"status": b.status, "seconds": round(b.seconds, 2)}
        reports.append(r)
        mark = "ok  " if "proof" in r and r["proof"]["status"] == "proved" and not r["gaps"] else "FAIL"
        distinct = {u["lemma"]: u["source"] for u in r.get("lemmas", [])}
        r["distinct_lemmas"] = len(distinct)
        r["from_store"] = sum(s == "store" for s in distinct.values())
        print(
            f"{mark} {r['place']} {r['function'][5:9]} {r['value']:>6}: {len(r.get('lemmas', []))} uses of "
            f"{len(distinct)} lemmas, {r['from_store']} from the store, {r.get('mined', 0)} new "
            f"({r.get('mined_check_seconds', 0)}s), "
            f"continued proof {r.get('proof', {}).get('seconds', '-')}s, original {r['original']['seconds']}s"
            + "".join(f"\n     gap: {g}" for g in r["gaps"]),
            flush=True,
        )
    store.save()

    proved = [r for r in reports if "proof" in r and r["proof"]["status"] == "proved" and not r["gaps"]]
    used = sorted({u["lemma"].split(".")[-1] for r in proved for u in r["lemmas"]})
    axioms = audit(repo, lean, [f"Split{r['place']}" for r in proved] + [f"Lemma_{n}" for n in used])
    bad = {m: a for m, a in axioms.items() if a.startswith("FAIL")}
    summary = {
        "provenance": provenance,
        "prepare_seconds": round(prepared, 1),
        "places": len(places),
        "proved": len(proved),
        "lemmas_in_store": len(store.index["lemmas"]),
        "lemmas_used": len(used),
        "unproved_facts": len(unproved),
        "original_seconds_sum": round(sum(r["original"]["seconds"] for r in reports), 2),
        "continued_proofs_seconds_sum": round(sum(r.get("proof", {}).get("seconds", 0) for r in reports), 2),
        "split_seconds_sum": round(
            sum(
                r.get("mined_check_seconds", 0)
                + r.get("failed_fact_seconds", 0)
                + r.get("proof", {}).get("seconds", 0)
                for r in reports
            ),
            2,
        ),
        "axioms": sorted(set(axioms.values())),
        "axioms_by_module": axioms,
        "audit_failures": bad,
    }
    print(json.dumps({k: v for k, v in summary.items() if not k.startswith("axioms")}, indent=1))
    print("axioms:", "; ".join(summary["axioms"]))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({"summary": summary, "places": reports}, indent=2) + "\n")
    return 0 if len(proved) == len(places) and not bad else 1


if __name__ == "__main__":
    sys.exit(main())
