"""The rule search: rewrites of real IR by rules already proved for every input.

For each integer instruction of a function, in the function's order, it cuts out what the instruction reads
within a few instructions, as a term, and looks for a cheaper term the proved rules reach from it: breadth
first, a rule a step, at any instruction of the term. A rule is a refinement, which goes one way, so a state
is a term and a step is a rewrite: nothing is merged as an equality. What it finds is a chain of rules, and
certify mode has Lean prove the chain again, as a slice, the cut as a function of its inputs, and, where the
function is one block of instructions the certifier follows, as the whole function.

It calls no model and draws no random number. Every loop runs in the function's, the term's or the rule file's
order, so one input gives one output, byte for byte. `llvm-mca` filters what it found: both sides of a slice
go through `opt -O3` and `llc -O3`, and a candidate is kept only if it takes fewer uOps there.
docs/rule-search.md.
"""

from __future__ import annotations

import json
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import certify
import ir
import lang
import proved

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))

from irlean import hashing, schemas  # noqa: E402

TRIPLE = "x86_64-unknown-linux-gnu"


@dataclass(frozen=True)
class Options:
    depth: int = 4  # how many instructions deep a cut goes
    steps: int = 4  # the longest chain
    states: int = 2000  # how many terms one cut's search may reach
    mcpu: str = "x86-64-v3"
    baseline: str = "O3"  # what both sides go through before llvm-mca counts: `O3`, or `none`
    keep: str = "fewer"  # `fewer`: only candidates llvm-mca gives fewer uOps. `all`: every candidate, labeled
    whole: bool = True  # also certify the whole function, where it's one block


def usable(rules: list[lang.Rule]) -> list[lang.Rule]:
    """The rules a search can apply: those whose application the certifier can follow."""
    return [r for r in rules if not r.divides]


def best_chain(
    root: ir.Term, rules: list[lang.Rule], options: Options
) -> tuple[list[certify.Step], ir.Term, int]:
    """The cheapest term the rules reach from `root` in at most `options.steps` steps, with the chain that
    reaches it, the shortest and first found among the cheapest. And how many terms it looked at."""
    best: tuple[int, list[certify.Step], ir.Term] = (ir.size(root), [], root)
    seen = {root}
    frontier: list[tuple[ir.Term, list[certify.Step]]] = [(root, [])]
    for _ in range(options.steps):
        following: list[tuple[ir.Term, list[certify.Step]]] = []
        for state, chain in frontier:
            for sub in ir.subterms(state):
                for rule in rules:
                    new = rule.apply(sub)
                    if new is None or new == sub:
                        continue
                    reached = ir.replace(state, sub, new)
                    if reached in seen:
                        continue
                    seen.add(reached)
                    step = [*chain, certify.Step(rule, sub, new)]
                    if ir.size(reached) < best[0]:
                        best = (ir.size(reached), step, reached)
                    following.append((reached, step))
                    if len(seen) >= options.states:
                        return best[1], best[2], len(seen)
        frontier = following
    return best[1], best[2], len(seen)


# ------------------------------------------------------------------------------------------------------------
# llvm-mca

UOPS = re.compile(r"^Total uOps:\s+(\d+)", re.M)
ITERATIONS = re.compile(r"^Iterations:\s+(\d+)", re.M)


def uops(module: str, options: Options) -> float | None:
    """What `llvm-mca` says one run of a module's code takes, in uOps, after `opt -O3` if that's the baseline,
    and `llc -O3`. None if a tool fails."""
    text = module
    if options.baseline == "O3":
        ran = proved.run(["opt", "-O3", "-S", f"-mtriple={TRIPLE}", f"-mcpu={options.mcpu}"], stdin=text)
        if ran.exit != 0:
            return None
        text = ran.out
    ran = proved.run(["llc", "-O3", f"-mtriple={TRIPLE}", f"-mcpu={options.mcpu}", "-o", "-"], stdin=text)
    if ran.exit != 0:
        return None
    ran = proved.run(["llvm-mca", f"-mtriple={TRIPLE}", f"-mcpu={options.mcpu}"], stdin=ran.out)
    total, iterations = UOPS.search(ran.out), ITERATIONS.search(ran.out)
    if ran.exit != 0 or not total or not iterations:
        return None
    return int(total[1]) / int(iterations[1])


# ------------------------------------------------------------------------------------------------------------
# One function


def normalize(module: str) -> str:
    """The module as `opt -S -passes=instnamer` prints it: every value named, so instructions can be added and
    removed."""
    ran = proved.run(["opt", "-S", "-passes=instnamer"], stdin=module)
    if ran.exit != 0:
        raise ir.IRError(f"opt doesn't read the input: {ran.err[-600:]}")
    return ran.out


def spliced(module: str, name: str, text: str, declares: list[str]) -> str:
    """`module` with function `name` replaced by `text`, and any declaration it needs that the module
    lacks."""
    lines = module.splitlines()
    start = next(i for i, line in enumerate(lines) if (m := ir.DEFINE.match(line)) and m[1] == name)
    end = next(i for i in range(start, len(lines)) if lines[i] == "}")
    missing = [d for d in declares if d.split("(")[0] not in module]
    out = [*lines[:start], *text.rstrip("\n").splitlines(), *lines[end + 1 :], *missing]
    return "\n".join(out) + "\n"


def tree_size(f: ir.Function, token: str, memo: dict[str, int]) -> int:
    """How many nodes an operand has once every instruction it reads is written out where it's used."""
    if token not in f.defs or not ir.followed(f.defs[token]):
        return 1
    if token not in memo:
        memo[token] = 1 + sum(tree_size(f, t, memo) for t, _ in f.defs[token].operands)
    return memo[token]


def search_function(
    module: str, f: ir.Function, rules: list[lang.Rule], options: Options, out: Path
) -> dict[str, Any]:
    """Every rewrite the search finds in `f`, each certified, and what it cost."""
    preamble = ir.preamble(module)
    timing: list[dict[str, Any]] = []
    looked = 0
    # First, what the rules reach from each instruction's cut.
    found: list[dict[str, Any]] = []
    for inst in f.lines:
        if not ir.followed(inst):
            continue
        assert inst.name is not None
        started = time.monotonic()
        cut = ir.members(f, inst.name, options.depth)
        root = ir.term(f, inst.name, inst.width, cut)
        chain, final, states = best_chain(root, rules, options)
        looked += 1
        clock = {"root": inst.name, "states": states, "search_s": round(time.monotonic() - started, 4)}
        timing.append(clock)
        if not chain:
            continue
        # Where each step applied, by the function's own instruction where there is one, so the same rewrite
        # seen through a wider cut is known for the same.
        by_term = {
            ir.term(f, name, f.defs[name].width, cut): name for name in sorted(cut, key=lambda n: -cut[n])
        }
        sites = [by_term.get(step.old, f"{inst.name}, step {i}") for i, step in enumerate(chain)]
        key = frozenset((step.rule.name, site) for step, site in zip(chain, sites, strict=True))
        found.append(
            {
                "inst": inst,
                "cut": cut,
                "root": root,
                "chain": chain,
                "final": final,
                "sites": sites,
                "key": key,
                "clock": clock,
            }
        )
    # A rewrite that's part of a longer one found around another instruction isn't reported again: only the
    # longest, and of two with the same steps, the first.
    kept = [
        c
        for i, c in enumerate(found)
        if not any(
            c["key"] < other["key"] or (c["key"] == other["key"] and j < i) for j, other in enumerate(found)
        )
    ]
    results: list[dict[str, Any]] = []
    whole = ir.one_block(f) if options.whole else None
    for c in kept:
        inst, cut, root, chain, final, clock = (
            c["inst"],
            c["cut"],
            c["root"],
            c["chain"],
            c["final"],
            c["clock"],
        )
        terms = certify.states(root, chain)
        params = ir.leaves(root)
        first = ir.verbatim("s0", params, f, cut, inst.name)
        texts = [first, *(ir.state(f"s{i}", params, t) for i, t in enumerate(terms) if i)]
        chain_ll = certify.chain_module(preamble, texts)
        before_slice = certify.chain_module(preamble, [first])
        after_slice = certify.chain_module(preamble, [ir.state("s0", params, final)])
        started = time.monotonic()
        counted = (uops(before_slice, options), uops(after_slice, options))
        clock["llvm_mca_s"] = round(time.monotonic() - started, 4)
        if counted[0] is None or counted[1] is None:
            verdict = "not measured"
        else:
            verdict = "fewer" if counted[1] < counted[0] else "same" if counted[1] == counted[0] else "more"
        entry: dict[str, Any] = {
            "root": inst.name,
            "chain": [
                {
                    "rule": step.rule.name,
                    "match": lang.show(step.rule.pattern),
                    "replace": lang.show(step.rule.replacement),
                    "at": site,
                }
                for step, site in zip(chain, c["sites"], strict=True)
            ],
            "instructions": {"before": ir.size(root), "after": ir.size(final)},
            "llvm_mca": {"uops_before": counted[0], "uops_after": counted[1], "verdict": verdict},
            "kept": verdict == "fewer" or options.keep == "all",
        }
        results.append(entry)
        if not entry["kept"]:
            continue
        directory = out / f"{len(results) - 1:03d}-{re.sub(r'[^-a-zA-Z0-9_.]', '_', inst.name[1:])}"
        directory.mkdir(parents=True, exist_ok=True)
        rewritten = ir.rewritten(f, inst.name, cut, final)
        after = spliced(module, f.name, rewritten, [d for text in texts for d in text[1]])
        checked = proved.run(["opt", "-S", "-passes=verify"], stdin=after)
        if checked.exit != 0:
            raise ir.IRError(f"the rewritten @{f.name} isn't valid IR: {checked.err[-800:]}")
        written = {
            "before.ll": module,
            "after.ll": checked.out,
            "slice-before.ll": before_slice,
            "slice-after.ll": after_slice,
        }
        for name, text in written.items():
            (directory / name).write_text(text)
        entry["files"] = {name: hashing.sha256_text(text) for name, text in written.items()}
        entry["directory"] = f"{out.name}/{directory.name}"
        verdict_slice = certify.check(chain_ll, [s.rule for s in chain], directory / "slice", "slice")
        entry["slice"] = summary(verdict_slice)
        clock["certify_slice_s"] = verdict_slice["seconds"]
        entry["function"] = {
            "status": "not attempted",
            "reason": "the function isn't one block of integer instructions, so only the slice is certified",
        }
        if whole is not None:
            attempt = whole_function(preamble, f, chain, directory / "function")
            entry["function"] = summary(attempt) if "schema" in attempt else attempt
            if "seconds" in attempt:
                clock["certify_function_s"] = attempt["seconds"]
    return {
        "function": f.name,
        "roots": looked,
        "candidates": len(found),
        "results": results,
        "timing": timing,
    }


def summary(verdict: dict[str, Any]) -> dict[str, Any]:
    """A certificate's verdict, without how long it took."""
    keys = ("status", "reason", "claim", "tier", "rules_used", "axioms", "files")
    out = {k: verdict[k] for k in keys}
    if verdict["status"] != "certified":
        out["detail"] = verdict["detail"]
    return out


def whole_function(preamble: str, f: ir.Function, chain: list[certify.Step], out: Path) -> dict[str, Any]:
    """The same chain, about the whole function: its states are the function with each step applied, under the
    function's own `define` line."""
    returned = ir.one_block(f)
    assert returned is not None
    token, width = returned
    if tree_size(f, token, {}) > certify.MAX_PROOF_NODES:
        return {"status": "not attempted", "reason": "the function is too large to write a proof along"}
    everything = ir.members(f, token, None)
    full = {name: ir.term(f, name, f.defs[name].width, everything) for name in everything}
    state = ir.term(f, token, width, everything)
    terms = [state]
    for step in chain:
        old, new = ir.substitute(step.old, full), ir.substitute(step.new, full)
        if step.rule.apply(old) != new:
            return {
                "status": "not attempted",
                "reason": f"{step.rule.name} doesn't apply the same way in the function",
            }
        state = ir.replace(state, old, new)
        if state == terms[-1]:
            return {
                "status": "not attempted",
                "reason": "what was rewritten doesn't reach what the function returns",
            }
        terms.append(state)
    texts: list[tuple[str, list[str]]] = []
    for i, t in enumerate(terms):
        header = ir.renamed(f.header, f.name, f"s{i}")
        if i == 0:
            lines = [inst.text for inst in f.lines]
            declares = ir.declarations(f, [inst.name for inst in f.lines if inst.name])
        else:
            lines, value, declares = ir.body(t)
            lines = [*lines, f"ret i{width} {value}"]
        texts.append((header + "\n" + "".join(f"  {line}\n" for line in lines) + "}\n", declares))
    return certify.check(certify.chain_module(preamble, texts), [s.rule for s in chain], out, "function")


def search(
    path: Path, function: str | None, rules: list[lang.Rule], options: Options, out: Path
) -> dict[str, Any]:
    """Searches one module's functions, or one of them, and writes what it found to `out`. Returns the record,
    schema RULE_SEARCH, which has no time, path or host in it: one input, one record."""
    source = path.read_text()
    module = normalize(source)
    found = [f for f in ir.functions(module) if function is None or f.name == function]
    if not found:
        raise ir.IRError(f"{path.name} has no function {function}")
    out.mkdir(parents=True, exist_ok=True)
    functions = []
    timing = []
    for f in found:
        got = search_function(
            module, f, usable(rules), options, out / re.sub(r"[^-a-zA-Z0-9_.]", "_", f.name)
        )
        timing.append({"function": f.name, "roots": got.pop("timing")})
        functions.append(got)
    record = {
        "schema": schemas.RULE_SEARCH,
        "input": {
            "name": path.name,
            "sha256": hashing.sha256_text(source),
            "normalized_sha256": hashing.sha256_text(module),
        },
        "options": {
            "depth": options.depth,
            "steps": options.steps,
            "states": options.states,
            "mcpu": options.mcpu,
            "baseline": options.baseline,
            "keep": options.keep,
        },
        "rules": {"usable": len(usable(rules)), "proved": len(rules)},
        "functions": functions,
    }
    schemas.write(
        out / "results.json", record, schemas.RULE_SEARCH, indent=1, ensure_ascii=False, sort_keys=True
    )
    (out / "timing.json").write_text(json.dumps(timing, indent=1) + "\n")
    return record
