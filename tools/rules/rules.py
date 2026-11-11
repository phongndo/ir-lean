#!/usr/bin/env python3
"""Rules: rewrites of LLVM IR proved for every input, from one declarative source each, and the search over
them.

docs/rules.md has the format, what a rule's statement claims and how each application is certified, and
docs/rule-search.md the search.

usage: tools/rules/rules.py gen [--check]
       tools/rules/rules.py check [--out FILE]
       tools/rules/rules.py certify CHAIN.json [--out DIR]
       tools/rules/rules.py search INPUT.ll [--function NAME] [--out DIR] [options]
       tools/rules/rules.py survey INPUT.ll... [--out DIR] [options]

  gen      Writes rules/Rules/Statements.lean, each rule's Lean statement, from rules/src/*.json. With
  --check,
           fails if the file isn't what the source generates.
  check    Says which rules are proved: each one's theorem, its type and its axioms, from the compiled
  library.
           Fails if a rule in the source isn't.
  certify  Has Lean prove a chain of rule applications again, and answers certified or not. Exit 0 only if it
  is. search   Looks for rewrites of a module's functions by proved rules, and certifies what it finds. survey
  The search over many inputs, and what it found and cost in all. Fails if a kept rewrite isn't certified.

  --depth N, --steps N, --states N   how deep a cut goes, the longest chain, and how many terms a cut's search
  reaches --mcpu CPU                         the processor llvm-mca counts uOps for --baseline O3|none
  what both sides go through before llvm-mca: `opt -O3` and `llc`, or `llc` alone --keep fewer|all
  certify only what llvm-mca gives fewer uOps, or everything found, labeled --no-whole
  don't try the whole function
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))

import certify  # noqa: E402
import gen  # noqa: E402
import ir  # noqa: E402
import lang  # noqa: E402
import proved  # noqa: E402
import search  # noqa: E402
from irlean import schemas  # noqa: E402


def cmd_gen(args: argparse.Namespace) -> int:
    text = gen.statements_text(gen.load_all())
    if args.check:
        if not gen.STATEMENTS.exists() or gen.STATEMENTS.read_text() != text:
            print("FAIL  rules/Rules/Statements.lean isn't what rules/src generates: run `rules.py gen`")
            return 1
        count = text.count("@[reducible] def ")
        print(f"ok    rules/Rules/Statements.lean is what rules/src generates, {count} rules")
        return 0
    gen.STATEMENTS.write_text(text)
    print(f"wrote {gen.STATEMENTS.relative_to(ROOT)}, {text.count('@[reducible] def ')} rules")
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    record = proved.check()
    out = Path(args.out)
    schemas.write(out, record, schemas.RULES_PROVED, indent=1, ensure_ascii=False)
    bad = [e for e in record["rules"] if not e["proved"]]
    for e in bad:
        print(f"FAIL  {e['name']}: {e['reason']}: {e['detail']}")
    print(f"{len(record['rules']) - len(bad)} of {len(record['rules'])} rules proved, in {out}")
    return 1 if bad else 0


def cmd_certify(args: argparse.Namespace) -> int:
    by_name = {r.name: r for r in gen.load_all()}
    missing = [name for name in args.rule if name not in by_name]
    if missing:
        raise lang.RuleError(f"no rule named {', '.join(missing)}")
    verdict = certify.check(
        Path(args.states).read_text(), [by_name[n] for n in args.rule], Path(args.out), args.scope
    )
    print(json.dumps(verdict, indent=1, ensure_ascii=False))
    return 0 if verdict["status"] == "certified" else 1


def cmd_search(args: argparse.Namespace) -> int:
    rules, record = proved.proved_rules()
    refused = [e for e in record["rules"] if not e["proved"]]
    for e in refused:
        print(f"not used, not proved: {e['name']}: {e['reason']}")
    options = search.Options(
        depth=args.depth,
        steps=args.steps,
        states=args.states,
        mcpu=args.mcpu,
        baseline=args.baseline,
        keep=args.keep,
        whole=not args.no_whole,
    )
    found = search.search(Path(args.input), args.function, rules, options, Path(args.out))
    bad = 0
    for f in found["functions"]:
        for r in f["results"]:
            chain = " then ".join(step["rule"] for step in r["chain"])
            mca = r["llvm_mca"]
            line = (
                f"@{f['function']} {r['root']}: {chain}, {r['instructions']['before']} instructions to "
                f"{r['instructions']['after']}, llvm-mca {mca['uops_before']} uOps to {mca['uops_after']}"
            )
            if not r["kept"]:
                print(f"dropped  {line}")
                continue
            tiers = [f"slice {r['slice']['status']}"]
            if r["function"]["status"] != "not attempted":
                tiers.append(f"whole function {r['function']['status']}")
            print(f"found    {line}: {', '.join(tiers)}")
            bad += r["slice"]["status"] != "certified"
    roots = sum(f["roots"] for f in found["functions"])
    candidates = sum(f["candidates"] for f in found["functions"])
    results = sum(len(f["results"]) for f in found["functions"])
    print(
        f"{roots} instructions looked at, {candidates} with a rewrite, {results} rewrites that aren't part "
        f"of another, in {args.out}/results.json"
    )
    if bad:
        print(f"FAIL  {bad} kept candidates have no certificate")
    return 1 if bad else 0


def cmd_survey(args: argparse.Namespace) -> int:
    """The search over many inputs, with one check of the rules, and what it found and cost in all."""
    rules, _ = proved.proved_rules()
    options = search.Options(
        depth=args.depth,
        steps=args.steps,
        states=args.states,
        mcpu=args.mcpu,
        baseline=args.baseline,
        keep=args.keep,
        whole=not args.no_whole,
    )
    out = Path(args.out)
    rows: list[dict[str, Any]] = []
    unread = []
    times: dict[str, list[float]] = {
        "search_s": [],
        "llvm_mca_s": [],
        "certify_slice_s": [],
        "certify_function_s": [],
    }
    for i, name in enumerate(args.inputs):
        path = Path(name)
        directory = out / f"{i:04d}-{path.stem}"
        try:
            found = search.search(path, None, rules, options, directory)
        except ir.IRError as error:
            unread.append({"input": name, "reason": " ".join(str(error).split())[:200]})
            continue
        results = [r for f in found["functions"] for r in f["results"]]
        kept = [r for r in results if r["kept"]]
        whole = [r for r in kept if r["function"]["status"] != "not attempted"]
        rows.append(
            {
                "input": name,
                "functions": len(found["functions"]),
                "instructions": sum(f["roots"] for f in found["functions"]),
                "with_a_rewrite": sum(f["candidates"] for f in found["functions"]),
                "rewrites": len(results),
                "longest_chain": max((len(r["chain"]) for r in results), default=0),
                "fewer_uops": sum(r["llvm_mca"]["verdict"] == "fewer" for r in results),
                "kept": len(kept),
                "slices_certified": sum(r["slice"]["status"] == "certified" for r in kept),
                "slices_not_certified": [
                    {"root": r["root"], "status": r["slice"]["status"], "reason": r["slice"]["reason"]}
                    for r in kept
                    if r["slice"]["status"] != "certified"
                ],
                "functions_tried": len(whole),
                "functions_certified": sum(r["function"]["status"] == "certified" for r in whole),
                "rules": sorted({s["rule"] for r in results for s in r["chain"]}),
            }
        )
        for f in json.loads((directory / "timing.json").read_text()):
            for root in f["roots"]:
                for key, values in times.items():
                    if key in root:
                        values.append(root[key])

    def middle(values: list[float]) -> float | None:
        return sorted(values)[len(values) // 2] if values else None

    total = {
        key: sum(r[key] for r in rows)
        for key in (
            "functions",
            "instructions",
            "with_a_rewrite",
            "rewrites",
            "fewer_uops",
            "kept",
            "slices_certified",
            "functions_tried",
            "functions_certified",
        )
    }
    summary = {
        "inputs": len(args.inputs),
        "read": len(rows),
        "unread": unread,
        "total": total,
        "slices_not_certified": [
            dict(input=r["input"], **s) for r in rows for s in r["slices_not_certified"]
        ],
        "rules_used": sorted({name for r in rows for name in r["rules"]}),
        "seconds": {
            key: {"count": len(v), "median": middle(v), "max": max(v, default=None), "sum": round(sum(v), 2)}
            for key, v in times.items()
        },
        "rows": rows,
    }
    out.mkdir(parents=True, exist_ok=True)
    (out / "survey.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(
        json.dumps(
            {k: summary[k] for k in ("inputs", "read", "total", "slices_not_certified", "seconds")}, indent=1
        )
    )
    print(f"{len(summary['rules_used'])} rules used: {' '.join(summary['rules_used'])}")
    print(f"{len(unread)} inputs opt doesn't read as they are; everything is in {out}/survey.json")
    return 1 if summary["slices_not_certified"] else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("gen")
    p.add_argument("--check", action="store_true")
    p.set_defaults(run=cmd_gen)
    p = sub.add_parser("check")
    p.add_argument("--out", default=str(ROOT / "build" / "rules" / "proved.json"))
    p.set_defaults(run=cmd_check)
    p = sub.add_parser("certify")
    p.add_argument("states", help="a module whose functions @s0 to @sk are the chain's states")
    p.add_argument("--rule", action="append", required=True, help="the rule applied at each step, in order")
    p.add_argument("--scope", choices=("slice", "function"), default="slice")
    p.add_argument("--out", default=str(ROOT / "build" / "rules" / "certify"))
    p.set_defaults(run=cmd_certify)
    p = sub.add_parser("search")
    p.add_argument("input")
    p.add_argument("--function")
    p.add_argument("--out", default=str(ROOT / "build" / "rule-search" / "out"))
    p.set_defaults(run=cmd_search)
    p = sub.add_parser("survey")
    p.add_argument("inputs", nargs="+")
    p.add_argument("--out", default=str(ROOT / "build" / "rule-search" / "survey"))
    p.set_defaults(run=cmd_survey)
    for p in (sub.choices["search"], sub.choices["survey"]):
        p.add_argument("--depth", type=int, default=search.Options.depth)
        p.add_argument("--steps", type=int, default=search.Options.steps)
        p.add_argument("--states", type=int, default=search.Options.states)
        p.add_argument("--mcpu", default=search.Options.mcpu)
        p.add_argument("--baseline", choices=("O3", "none"), default=search.Options.baseline)
        p.add_argument("--keep", choices=("fewer", "all"), default=search.Options.keep)
        p.add_argument("--no-whole", action="store_true")
    args = parser.parse_args(argv)
    try:
        return args.run(args)
    except (lang.RuleError, proved.ToolError, schemas.SchemaError, ir.IRError, OSError) as error:
        print(json.dumps({"status": "error", "detail": str(error)}))
        return 1


if __name__ == "__main__":
    sys.exit(main())
