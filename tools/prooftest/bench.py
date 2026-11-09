#!/usr/bin/env python3
"""Measures tier-1 proof tests on injected bugs: milestone T1 in docs/roadmap.md. docs/proof-tests.md has the
results.

Each item is a property, the statement of a theorem this repo proves, and a function with a bug injected into
its source. Tier 1 should answer `counterexample` for each bug it can run, and `unknown` for each it can't. It
also runs every property on the function without a bug, where any counterexample would be a false alarm, since
the theorem is proved.

The sets:

- `llvm`: every mutant in tests/llvm/targets.toml, which tests/llvm.py requires to stop its proof.
- `variants`: tools/prooftest/variants.toml, more bugs in each compiler-rt builtin, from
  `--generate-variants`.
- `proofs_sh`: the 16 bugs tests/proofs.sh injects, from tools/prooftest/t1.toml.
- `negative`: the cases in tests/verification_negative, with the claim each pins.

`--check-equivalent` runs each bug tier 1 misses against the theorem's own proof, as tests/llvm.py does. A
proof that still checks shows the bug changes nothing the theorem says: it's equivalent, and not a miss.

usage: tools/prooftest/bench.py [--tool build/ir-lean] [--sets llvm,variants,proofs_sh,negative]
                                [--only MODULE ...]
                                [--workers N] [--max-inputs N] [--out DIR] [--check-equivalent]
       tools/prooftest/bench.py --generate-variants [--per-target 3] [--seed 0] [--workers N]
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "tests"))
import llvm  # noqa: E402
import verify_negative  # noqa: E402


def load_prooftest() -> Any:
    """tools/prooftest/prooftest.py, by path: tests/prooftest/ is a directory of the same name."""
    spec = importlib.util.spec_from_file_location("prooftest_tool", HERE / "prooftest.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


prooftest: Any = load_prooftest()

VARIANTS = HERE / "variants.toml"
T1 = HERE / "t1.toml"
NEGATIVE = ROOT / "tests" / "verification_negative" / "cases"
OUT = ROOT / "build" / "prooftest" / "bench"
# Reasons that say tier 1 couldn't run the property at all, as opposed to running it and not deciding.
CANT_RUN = {
    "binder_unsupported",
    "statement_invalid",
    "statement_unsupported",
    "statement_not_about_target",
    "undecidable",
    "function_unsupported",
    "function_not_found",
}


def theorem_statement(proof: Path, name: str) -> str:
    """A theorem's header as one proposition: `theorem n (a : A) (h : H) : T` becomes
    `∀ (a : A) (h : H), T`."""
    text = proof.read_text()
    match = re.search(rf"^theorem {re.escape(name)}\b(.*?):=", text, re.S | re.M)
    if match is None:
        raise RuntimeError(f"no theorem {name} in {proof}")
    head, depth = match.group(1), 0
    for i, ch in enumerate(head):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0:
            binders, conclusion = " ".join(head[:i].split()), " ".join(head[i + 1 :].split())
            return f"∀ {binders}, {conclusion}" if binders else conclusion
    raise RuntimeError(f"can't read the header of {name} in {proof}")


# Variants: more bugs in each compiler-rt builtin, from simple operators on its source


def code_mask(text: str) -> str:
    """The text with comments, string and character literals, and preprocessor lines blanked, so operators
    only match code. Positions are unchanged."""
    out = list(text)
    i, n = 0, len(text)
    line_start = True
    while i < n:
        if line_start and text[i:].lstrip(" \t").startswith("#"):
            end = i
            while end < n and (text[end] != "\n" or text[end - 1] == "\\"):
                end += 1
            for k in range(i, end):
                out[k] = " "
            i = end
            continue
        ch = text[i]
        line_start = ch == "\n"
        if text.startswith("//", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            end = n if end < 0 else end + 2
            for k in range(i, end):
                if out[k] != "\n":
                    out[k] = " "
            i = end
        elif ch in "\"'":
            end = i + 1
            while end < n and text[end] != ch:
                end += 2 if text[end] == "\\" else 1
            out[i : end + 1] = " " * (end + 1 - i)
            i = end + 1
        else:
            i += 1
    return "".join(out)


def function_body(text: str, mask: str, name: str) -> tuple[int, int]:
    """Where the body of the function `name` is defined: from its opening brace to its closing one."""
    for match in re.finditer(rf"\b{re.escape(name)}\s*\(", mask):
        brace = mask.find("{", match.end())
        semicolon = mask.find(";", match.end())
        if brace < 0 or (0 <= semicolon < brace):
            continue
        depth = 0
        for k in range(brace, len(mask)):
            depth += {"{": 1, "}": -1}.get(mask[k], 0)
            if depth == 0:
                return brace, k + 1
    raise RuntimeError(f"no definition of {name}")


OPERATORS: list[tuple[str, str, Callable[[str], str] | str]] = [
    ("relational", r"(?<![<>=!])<(?![<=])", "<="),
    ("relational", r"(?<![<>=\-])>(?![>=])", ">="),
    ("relational", r"(?<!<)<=", "<"),
    ("relational", r"(?<!>)>=", ">"),
    ("relational", r"==", "!="),
    ("relational", r"!=", "=="),
    ("logical", r"&&", "||"),
    ("logical", r"\|\|", "&&"),
    ("logical", r"!(?!=)", ""),
    ("bitwise", r"(?<= )&(?= )", "|"),
    ("bitwise", r"(?<= )\|(?= )", "&"),
    ("bitwise", r"(?<= )\^(?= )", "|"),
    ("bitwise", r"~", ""),
    ("arithmetic", r"(?<= )\+(?= )", "-"),
    ("arithmetic", r"(?<= )-(?= )", "+"),
    ("shift", r"(?<= )<<(?= )", ">>"),
    ("shift", r"(?<= )>>(?= )", "<<"),
    ("assignment", r"(?<= )\+=(?= )", "-="),
    ("assignment", r"(?<= )-=(?= )", "+="),
    ("assignment", r"(?<= )\^=(?= )", "|="),
    ("assignment", r"(?<= )>>=(?= )", "<<="),
    ("assignment", r"(?<= )<<=(?= )", ">>="),
    ("constant", r"(?<![\w.])(?:0[xX][0-9a-fA-F]+|\d+)(?=[uUlL]*(?![\w.]))", lambda s: str(int(s, 0) + 1)),
    (
        "constant",
        r"(?<![\w.])(?:0[xX][0-9a-fA-F]*[1-9a-fA-F][0-9a-fA-F]*|[1-9]\d*)(?=[uUlL]*(?![\w.]))",
        lambda s: str(int(s, 0) - 1),
    ),
]


def replacement(text: str, start: int, end: int, new: str) -> tuple[str, str]:
    """`from` and `to` for a change at [start, end): whole lines, with as many lines before as make `from`
    unique."""
    first = text.rfind("\n", 0, start) + 1
    last = text.find("\n", end)
    last = len(text) if last < 0 else last
    while text.count(text[first:last]) > 1 and first > 0:
        first = text.rfind("\n", 0, first - 1) + 1
    old = text[first:last]
    return old, text[first:start] + new + text[end:last]


def candidates(text: str, name: str) -> list[dict[str, str]]:
    mask = code_mask(text)
    start, end = function_body(text, mask, name)
    out: list[dict[str, Any]] = []
    for operator, pattern, new in OPERATORS:
        for match in re.finditer(pattern, mask[start:end]):
            a, b = start + match.start(), start + match.end()
            to = new if isinstance(new, str) else new(text[a:b])
            old_text, new_text = replacement(text, a, b, to)
            out.append(
                {"operator": operator, "at": a, "old": text[a:b], "new": to, "from": old_text, "to": new_text}
            )
    return sorted(out, key=lambda c: (c["at"], c["operator"]))


def variant_source(target: dict[str, Any], symbol: str) -> tuple[str, str]:
    """The file to mutate, and the function in it: the builtin, or for division, the routine it includes."""
    if target["source"].endswith(("udivsi3.c", "udivdi3.c")):
        return "compiler-rt/lib/builtins/int_div_impl.inc", "__udivXi3"
    if target["source"].endswith(("umodsi3.c", "umoddi3.c")):
        return "compiler-rt/lib/builtins/int_div_impl.inc", "__umodXi3"
    return target["source"], symbol


def position_of(text: str, at: int) -> str:
    """A position as line:column, both from 1, which names a change uniquely."""
    line = text.count("\n", 0, at) + 1
    return f"{line}:{at - text.rfind(chr(10), 0, at)}"


def strip_ir(ir: str) -> str:
    return llvm.strip_paths(ir)


def generate_variants(tool: Path, per_target: int, seed: int, workers: int) -> int:
    config = tomllib.loads((llvm.PROOFS / "targets.toml").read_text())
    targets = [
        t
        for t in config["target"]
        if t["flags"] == "compiler_rt" and not any(d.get("memory") for d in t["functions"].values())
    ]
    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        pipeline = llvm.Pipeline(tool.resolve(), work, config)

        def compile_ir(target: dict[str, Any], mutant: dict[str, str] | None, where: Path) -> str | None:
            where.mkdir(parents=True)
            overlay = None
            if mutant is not None:
                overlay = where / "overlay"
                for path in {mutant["file"], target["source"]}:
                    (overlay / path).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy(pipeline.src / path, overlay / path)
                    (overlay / path).chmod(0o644)
                text = (overlay / mutant["file"]).read_text()
                (overlay / mutant["file"]).write_text(text.replace(mutant["from"], mutant["to"], 1))
            ll = where / "out.ll"
            try:
                llvm.run(pipeline.clang_command(target, overlay, ll))
            except RuntimeError:
                return None
            return strip_ir(ll.read_text())

        def for_target(index: int, target: dict[str, Any]) -> list[dict[str, Any]]:
            ((function, details),) = target["functions"].items()
            symbol = details.get("symbol", function)
            file, name = variant_source(target, symbol)
            text = (pipeline.src / file).read_text()
            original = compile_ir(target, None, work / f"t{index}" / "original")
            existing = {(m["from"], m["to"]) for m in target.get("mutants", []) + details.get("mutants", [])}
            kept, seen_ir = [], {original}
            for k, c in enumerate(candidates(text, name)):
                if (c["from"], c["to"]) in existing:
                    continue
                ir = compile_ir(target, {**c, "file": file}, work / f"t{index}" / f"m{k}")
                if ir is None or ir in seen_ir:
                    continue
                seen_ir.add(ir)
                kept.append({**c, "file": file})
            rng = random.Random(f"{seed}:{target['module']}")
            chosen = sorted(rng.sample(kept, min(per_target, len(kept))), key=lambda c: c["at"])
            return [
                {
                    "module": target["module"],
                    "function": function,
                    "name": f"{c['operator']} `{c['old']}` to `{c['new']}` at "
                    f"{file.rsplit('/', 1)[-1]}:{position_of(text, c['at'])}",
                    "file": file,
                    "from": c["from"],
                    "to": c["to"],
                    "candidates": len(kept),
                }
                for c in chosen
            ]

        with ThreadPoolExecutor(workers) as pool:
            chosen = [v for vs in pool.map(for_target, range(len(targets)), targets) for v in vs]
    lines = [
        "# More bugs in each compiler-rt builtin tests/llvm/targets.toml proves, for",
        "# tools/prooftest/bench.py. Made by `tools/prooftest/bench.py --generate-variants",
        f"# --per-target {per_target} --seed {seed}`: every simple operator change in the builtin's body",
        "# (relational, logical, bitwise, arithmetic, shift, compound assignment, and a constant one more",
        "# or one less), each compiled as tests/llvm.py compiles the builtin. Of those that change the IR,",
        "# each to IR no other one gives, it picks this many at random, with the seed. `candidates` is how",
        "# many there were. Some may be equivalent: bench.py's --check-equivalent says which, with the",
        "# builtin's proof.",
        "",
    ]
    for v in chosen:
        lines.append("[[variant]]")
        for key in ("module", "function", "name", "file", "from", "to", "candidates"):
            lines.append(f"{key} = {json.dumps(v[key], ensure_ascii=False)}")
        lines.append("")
    VARIANTS.write_text("\n".join(lines))
    print(f"wrote {len(chosen)} variants of {len(targets)} builtins to {VARIANTS.relative_to(ROOT)}")
    return 0


# What's measured


@dataclass
class Item:
    set: str
    label: str
    module: str
    namespace: str
    function: str
    statement: str
    # Makes the input, in a scratch directory: {"ir": path} or {"c": path}.
    prepare: Callable[[Path], dict[str, Any]]
    mutant: str | None = None
    expect: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)


def mutate(text: str, old: str, new: str, first: bool) -> str:
    if old not in text:
        raise RuntimeError(f"{old!r} isn't in the source")
    return text.replace(old, new, 1) if first else text.replace(old, new)


def llvm_items(
    config: dict[str, Any],
    pipeline: llvm.Pipeline,
    variants: list[dict[str, Any]],
    sets: set[str],
    only: set[str] | None,
) -> list[Item]:
    items = []
    for target in config["target"]:
        if only and target["module"] not in only:
            continue
        proof = llvm.PROOFS / f"{target['proof']}.lean"
        for function, details in target["functions"].items():
            symbol = details.get("symbol", function)
            short = details["theorem"].rsplit(".", 1)[-1]
            try:
                statement = theorem_statement(proof, short)
            except RuntimeError as error:
                statement = f"-- {error}"
            bugs = details.get("mutants", []) + (
                target.get("mutants", []) if len(target["functions"]) == 1 else []
            )
            mine = [v for v in variants if v["module"] == target["module"] and v["function"] == function]

            def prepare(
                where: Path, target: dict[str, Any] = target, mutant: dict[str, Any] | None = None
            ) -> dict[str, Any]:
                overlay = None
                if mutant is not None:
                    overlay = where / "overlay"
                    file = mutant.get("file", target["source"])
                    for path in {file} if target.get("wrapper") else {file, target["source"]}:
                        (overlay / path).parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy(pipeline.src / path, overlay / path)
                        (overlay / path).chmod(0o644)
                    text = (overlay / file).read_text()
                    (overlay / file).write_text(mutate(text, mutant["from"], mutant["to"], True))
                ll = where / f"{target['module']}.ll"
                llvm.run(pipeline.clang_command(target, overlay, ll))
                return {"ir": str(ll)}

            base: dict[str, Any] = {
                "module": target["module"],
                "namespace": target["module"],
                "function": symbol,
                "statement": statement,
                "extra": {"function_name": function, "memory": bool(details.get("memory"))},
            }
            if "llvm" in sets or "variants" in sets:
                items.append(
                    Item(set="original", label=f"{function}", prepare=prepare, expect="passed_tier1", **base)
                )
            if "llvm" in sets:
                for bug in bugs:
                    items.append(
                        Item(
                            set="llvm",
                            label=f"{function}: {bug['name']}",
                            prepare=lambda w, m=bug, p=prepare: p(w, mutant=m),
                            mutant=bug["name"],
                            expect="counterexample",
                            **base,
                        )
                    )
            if "variants" in sets:
                for bug in mine:
                    items.append(
                        Item(
                            set="variants",
                            label=f"{function}: {bug['name']}",
                            prepare=lambda w, m=bug, p=prepare: p(w, mutant=m),
                            mutant=bug["name"],
                            expect="counterexample",
                            **base,
                        )
                    )
    return items


def zlib_source(where: Path) -> Path:
    tarball = (
        os.environ.get("ZLIB_SRC")
        or subprocess.run(
            [
                "nix",
                "build",
                "--inputs-from",
                str(ROOT),
                "--no-link",
                "--print-out-paths",
                "nixpkgs#zlib.src",
            ],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )
    directory = where / "zlib"
    if not directory.exists():
        directory.mkdir(parents=True)
        with tarfile.open(tarball) as archive:
            for member in archive.getmembers():
                parts = Path(member.name).parts[1:]
                if not parts or member.issym() or member.islnk() or ".." in parts:
                    continue
                member.name = str(Path(*parts))
                archive.extract(member, directory, filter="data")
    return directory


def proofs_sh_items(scratch: Path) -> list[Item]:
    items = []
    for bug in tomllib.loads(T1.read_text())["proofs_sh"]:
        if "statement" in bug:
            statement = bug["statement"]
        else:
            path, name = bug["theorem"].split(":")
            statement = theorem_statement(ROOT / path, name)

        def prepare(where: Path, bug: dict[str, Any] = bug, mutated: bool = True) -> dict[str, Any]:
            source = bug["source"]
            if source.startswith("zlib:"):
                origin = zlib_source(scratch)
                name = source.removeprefix("zlib:")
            else:
                origin = (ROOT / source).parent
                name = Path(source).name
            copy = where / "src"
            shutil.copytree(origin, copy)
            if mutated:
                file = copy / bug.get("file", name)
                file.write_text(mutate(file.read_text(), bug["from"], bug["to"], bug.get("first", False)))
            # As tests/proofs.sh compiles it. tools/verify.py would compile a copy of the one file, away from
            # the headers next to it.
            ll = where / f"{bug['namespace']}.ll"
            llvm.run(
                [
                    "clang",
                    *os.environ["PROOF_CFLAGS"].split(),
                    "-O2",
                    "-fno-strict-aliasing",
                    "-S",
                    "-emit-llvm",
                    "-fno-discard-value-names",
                    "-D_LARGEFILE64_SOURCE=1",
                    "-o",
                    str(ll),
                    str(copy / name),
                ]
            )
            return {"ir": str(ll)}

        base: dict[str, Any] = {
            "module": bug["namespace"],
            "namespace": bug["namespace"],
            "function": bug["function"],
            "statement": statement,
        }
        items.append(
            Item(
                set="proofs_sh",
                label=bug["name"],
                prepare=prepare,
                mutant=bug["name"],
                expect="counterexample",
                **base,
            )
        )
    return items


def negative_items() -> list[Item]:
    items = []
    for directory in sorted(NEGATIVE.iterdir()):
        manifest = json.loads((directory / "case.json").read_text())
        claim, override = manifest.get("claim"), manifest.get("pin_override")
        if override is not None and override.get("statement"):
            statement = override["statement"]
        elif claim:
            statement = verify_negative.canonical(claim)
        else:
            continue
        request = manifest["request"]
        source = directory / request["input"]["ir"]
        items.append(
            Item(
                set="negative",
                label=directory.name,
                module="Opt",
                namespace=request.get("namespace", "Opt"),
                function=request["function"],
                statement=statement,
                prepare=lambda where, s=source: {"ir": str(s)},
                mutant=directory.name,
                expect=None,
                extra={
                    "category": manifest["category"],
                    "llvm_verdict": manifest.get("llvm_verdict"),
                    "verify_expects": manifest["expect"]["verify"],
                },
            )
        )
    return items


def run_item(
    index: int, item: Item, out: Path, max_inputs: int, tool: Path, verify_confirm: str
) -> dict[str, Any]:
    slug = hashlib.sha256(f"{item.set}:{item.label}:{item.module}".encode()).hexdigest()[:8]
    where = out / "runs" / f"{index:04d}-{slug}"
    shutil.rmtree(where, ignore_errors=True)
    (where / "input").mkdir(parents=True)
    record: dict[str, Any] = {
        "set": item.set,
        "label": item.label,
        "module": item.module,
        "function": item.function,
        "mutant": item.mutant,
        "expect": item.expect,
        **item.extra,
    }
    try:
        source = item.prepare(where / "input")
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        record.update(status="not_run", reason="prepare_failed", detail=str(error)[:2000])
        return record
    request = {
        "input": source,
        "function": item.function,
        "namespace": item.namespace,
        "statement": item.statement,
        "max_inputs": max_inputs,
        "store": None,
        "verify_confirm": verify_confirm,
        "limits": {"timeout_seconds": 300, "memory_mb": 4000, "input_timeout_seconds": 5},
    }
    result = prooftest.prooftest(request, ROOT, tool, where / "run")
    counterexample = result.get("counterexample") or {}
    found = counterexample.get("found") or {}
    timing = result["timing"]
    record.update(
        status=result["status"],
        reason=result["reason"],
        detail=result["detail"][:600],
        evidence=counterexample.get("evidence"),
        shown=counterexample.get("shown"),
        found_phase=found.get("phase"),
        found_index=found.get("index"),
        shrink_steps=counterexample.get("shrink_steps"),
        tried=result["inputs"]["tried"],
        satisfied=result["inputs"]["satisfied"],
        exhaustive=result["inputs"]["exhaustive"],
        search_ms=timing.get("search_ms"),
        search_wall_ms=timing.get("search_wall_ms"),
        shrink_ms=timing.get("shrink_ms"),
        kernel_ms=timing.get("kernel_ms"),
        to_counterexample_ms=timing.get("to_counterexample_ms"),
        setup_seconds=round(
            timing.get("verify_setup_seconds", 0) + timing.get("harness_start_seconds", 0), 3
        ),
        verify_confirm_seconds=timing.get("verify_confirm_seconds"),
        total_seconds=timing.get("total_seconds"),
        kernel=(counterexample.get("kernel") or {}).get("ok"),
        kernel_detail=None
        if (counterexample.get("kernel") or {}).get("ok")
        else str((counterexample.get("kernel") or {}).get("detail", ""))[:300],
        # Whether tools/verify.py, asked too, found the same: True, False if it found the statement true
        # there, and None if it wasn't asked or decided nothing, such as running out of time.
        verify_agrees=None
        if not counterexample.get("verify")
        else True
        if counterexample["verify"]["result"] == "fails"
        else False
        if counterexample["verify"]["result"] == "holds"
        else None,
        verify_answer=None
        if not counterexample.get("verify")
        else f"{counterexample['verify']['status']}/{counterexample['verify']['reason']}",
        axioms=(counterexample.get("kernel") or {}).get("axioms"),
        work=str(where / "run"),
    )
    return record


def check_equivalent(
    config: dict[str, Any],
    tool: Path,
    records: list[dict[str, Any]],
    variants: list[dict[str, Any]],
    workers: int,
) -> None:
    """Runs each missed bug against the theorem's own proof, as tests/llvm.py does."""
    missed = [r for r in records if r["set"] in ("llvm", "variants") and r["status"] == "passed_tier1"]
    if not missed:
        return
    targets = {t["module"]: t for t in config["target"]}
    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        pipeline = llvm.Pipeline(tool.resolve(), work, config)
        (work / "support").mkdir()
        for module in config.get("support", []):
            pipeline.compile_lean(work, llvm.PROOFS / f"{module}.lean", llvm.PROOFS)
            shutil.copy(work / f"{module}.olean", work / "support")
        for module in {r["module"] for r in missed}:
            pipeline.generate(targets[module], work)

        def one(record: dict[str, Any]) -> None:
            target = targets[record["module"]]
            details = target["functions"][record["function_name"]]
            pool = (
                details.get("mutants", [])
                + target.get("mutants", [])
                + [v for v in variants if v["module"] == record["module"]]
            )
            mutant = next(m for m in pool if m["name"] == record["mutant"])
            failure, stopped_by = pipeline.check_mutant(target, mutant, details["theorem"])
            # A proof that stops says the proof depends on the code, not that the bug changes what it does.
            if failure is None:
                record["equivalence"] = {"verdict": "proof_stops", "proof_stopped_by": stopped_by}
            elif "the proof still checks" in failure:
                record["equivalence"] = {"verdict": "equivalent", "why": "the theorem's proof still checks"}
            else:
                record["equivalence"] = {"verdict": "unknown", "why": failure[:600]}

        with ThreadPoolExecutor(workers) as pool:
            list(pool.map(one, missed))


def deep_check(records: list[dict[str, Any]], tool: Path, inputs: int, workers: int) -> None:
    """Runs each bug tier 1 missed again, on many more inputs, to tell a bug it can't find from one that
    isn't there."""
    missed = [r for r in records if r["set"] in ("llvm", "variants") and r["status"] == "passed_tier1"]

    def one(record: dict[str, Any]) -> None:
        first = Path(record["work"])
        request = json.loads((first / "request.json").read_text())
        request.update(max_inputs=inputs, store=None, verify_confirm="never")
        request["limits"] = {**request["limits"], "timeout_seconds": 900}
        work = first.parent / "deep"
        shutil.rmtree(work, ignore_errors=True)
        result = prooftest.prooftest(request, ROOT, tool, work)
        counterexample = result.get("counterexample") or {}
        record["deep"] = {
            "max_inputs": inputs,
            "status": result["status"],
            "reason": result["reason"],
            "tried": result["inputs"]["tried"],
            "found_index": (counterexample.get("found") or {}).get("index"),
            "found_phase": (counterexample.get("found") or {}).get("phase"),
            "shown": counterexample.get("shown"),
            "seconds": result["timing"].get("total_seconds"),
        }

    with ThreadPoolExecutor(workers) as pool:
        list(pool.map(one, missed))


def percentile(values: list[float], p: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    k = (len(ordered) - 1) * p
    lo, hi = int(k), min(int(k) + 1, len(ordered) - 1)
    return round(ordered[lo] + (ordered[hi] - ordered[lo]) * (k - lo), 3)


def summarize(records: list[dict[str, Any]]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for name in ("original", "llvm", "variants", "proofs_sh", "negative"):
        rows = [r for r in records if r["set"] == name]
        if not rows:
            continue
        outcomes: dict[str, int] = {}
        for r in rows:
            key = f"{r['status']}/{r.get('reason')}"
            outcomes[key] = outcomes.get(key, 0) + 1
        caught = [r for r in rows if r["status"] == "counterexample"]
        cant = [r for r in rows if r["status"] == "unknown" and r.get("reason") in CANT_RUN]
        to_cex = [r["to_counterexample_ms"] for r in caught if r.get("to_counterexample_ms") is not None]
        search = [r["search_ms"] for r in caught if r.get("search_ms") is not None]
        setup = [r["setup_seconds"] for r in rows if r.get("setup_seconds")]
        entry: dict[str, Any] = {
            "items": len(rows),
            "outcomes": dict(sorted(outcomes.items())),
            "counterexamples": len(caught),
            "kernel_confirmed": sum(1 for r in caught if "kernel" in (r.get("evidence") or [])),
            "cant_run": len(cant),
            "ran": len(rows) - len(cant),
            "to_counterexample_ms": {
                "median": percentile(to_cex, 0.5),
                "p90": percentile(to_cex, 0.9),
                "max": max(to_cex) if to_cex else None,
            },
            "search_ms": {
                "median": percentile(search, 0.5),
                "p90": percentile(search, 0.9),
                "max": max(search) if search else None,
            },
            "setup_seconds": {"median": percentile(setup, 0.5), "p90": percentile(setup, 0.9)},
            "found_within": {
                str(n): sum(1 for r in caught if r.get("found_index") is not None and r["found_index"] < n)
                for n in (1, 10, 100, 1000)
            },
            "verify_agrees": sum(1 for r in caught if r.get("verify_agrees")),
            "verify_disagrees": sum(1 for r in caught if r.get("verify_agrees") is False),
            "verify_undecided": sorted(
                f"{r['label']}: {r['verify_answer']}"
                for r in caught
                if r.get("verify_answer") and r.get("verify_agrees") is None
            ),
        }
        if name == "original":
            entry["false_alarms"] = [r["label"] for r in caught]
        else:
            entry["missed"] = [
                {
                    "label": r["label"],
                    "status": r["status"],
                    "reason": r.get("reason"),
                    "equivalence": (r.get("equivalence") or {}).get("verdict"),
                    "deep": r.get("deep"),
                }
                for r in rows
                if r["status"] != "counterexample" and r.get("reason") not in CANT_RUN
            ]
            entry["cant_run_by_reason"] = {
                reason: sum(1 for r in cant if r.get("reason") == reason)
                for reason in sorted({r["reason"] for r in cant})
            }
        summary[name] = entry
    return summary


def t1_expected(record: dict[str, Any]) -> set[str]:
    """What tier 1 may answer on a case of milestone T1's set. A negative case's comes from the verdict
    tools/verify.py is expected to give it: a true claim is never a counterexample, and a false one never a
    pass."""
    if record["set"] == "proofs_sh":
        return {"unknown"} if record.get("reason") in CANT_RUN else {"counterexample"}
    # A claim tier 1 can't run, such as one about a `freeze`, quantifying over how a run chooses, is unknown.
    if record["status"] == "unknown" and record.get("reason") in CANT_RUN:
        return {"unknown"}
    expects = record.get("verify_expects") or []
    if "counterexample/witness_falsifies" in expects:
        return {"counterexample"}
    if "proved/kernel_checked" in expects:
        return {"passed_tier1", "vacuous"}
    if any(e.startswith("unsupported/") for e in expects):
        return {"unknown"}
    if record.get("llvm_verdict") == "invalid":
        return {"counterexample", "unknown"}
    return {"passed_tier1", "vacuous"}


# T1's threshold, in docs/roadmap.md: the median time to a counterexample.
T1_MEDIAN_MS = 100.0


def check_t1(records: list[dict[str, Any]]) -> list[str]:
    """Milestone T1: each bug it can run refuted, each it can't unknown, and a median under 100 ms."""
    failures = []
    rows = [r for r in records if r["set"] in ("proofs_sh", "negative")]
    for r in rows:
        expected = t1_expected(r)
        if r["status"] not in expected:
            failures.append(
                f"{r['set']} {r['label']}: {r['status']}/{r.get('reason')}, where T1 needs "
                f"{' or '.join(sorted(expected))}: {r.get('detail', '')[:300]}"
            )
    times = [r["to_counterexample_ms"] for r in rows if r.get("to_counterexample_ms") is not None]
    median = percentile(times, 0.5)
    if median is None or median >= T1_MEDIAN_MS:
        failures.append(f"the median time to a counterexample is {median} ms, not under {T1_MEDIAN_MS} ms")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--tool", type=Path, default=ROOT / "build" / "ir-lean")
    parser.add_argument("--sets", default="llvm,variants,proofs_sh,negative")
    parser.add_argument(
        "--only", nargs="*", default=None, help="only these modules of tests/llvm/targets.toml"
    )
    parser.add_argument("--workers", type=int, default=int(os.environ.get("LEAN_JOBS", "4")))
    parser.add_argument("--max-inputs", type=int, default=prooftest.DEFAULTS["max_inputs"])
    parser.add_argument("--out", type=Path, default=OUT)
    parser.add_argument("--check-equivalent", action="store_true")
    parser.add_argument(
        "--check-t1", action="store_true", help="fail unless milestone T1's criterion holds on what ran"
    )
    parser.add_argument(
        "--deep", type=int, default=0, help="run each missed bug again on this many inputs, such as 1000000"
    )
    parser.add_argument(
        "--verify-confirm",
        choices=["auto", "always", "never"],
        default="auto",
        help="always: have tools/verify.py confirm every counterexample, as well as the kernel",
    )
    parser.add_argument("--generate-variants", action="store_true")
    parser.add_argument("--per-target", type=int, default=3)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if args.generate_variants:
        return generate_variants(args.tool, args.per_target, args.seed, args.workers)

    sets = set(args.sets.split(","))
    config = tomllib.loads((llvm.PROOFS / "targets.toml").read_text())
    variants = tomllib.loads(VARIANTS.read_text()).get("variant", []) if VARIANTS.exists() else []
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    scratch = out / "scratch"
    scratch.mkdir(exist_ok=True)
    pipeline = llvm.Pipeline(args.tool.resolve(), scratch, config)
    items: list[Item] = []
    if sets & {"llvm", "variants"}:
        items += llvm_items(config, pipeline, variants, sets, set(args.only) if args.only else None)
    if "proofs_sh" in sets:
        zlib_source(scratch)
        items += proofs_sh_items(scratch)
    if "negative" in sets:
        items += negative_items()
    started = time.monotonic()
    print(f"{len(items)} items, {args.workers} at a time, at most {args.max_inputs} inputs each", flush=True)
    with ThreadPoolExecutor(args.workers) as pool:
        records = list(
            pool.map(
                lambda i: run_item(i, items[i], out, args.max_inputs, args.tool, args.verify_confirm),
                range(len(items)),
            )
        )
    if args.check_equivalent:
        check_equivalent(config, args.tool, records, variants, args.workers)
    if args.deep:
        deep_check(records, args.tool, args.deep, args.workers)
    summary = summarize(records)
    report = {
        "schema": "ir-lean.prooftest.bench/1",
        "max_inputs": args.max_inputs,
        "deep": args.deep,
        "verify_confirm": args.verify_confirm,
        "workers": args.workers,
        "seconds": round(time.monotonic() - started, 1),
        "machine": {"cpus": os.cpu_count(), "platform": sys.platform},
        "summary": summary,
        "records": records,
    }
    (out / "results.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    print(f"wrote {out / 'results.json'} in {report['seconds']} s")
    alarms = [r for r in records if r["set"] == "original" and r["status"] == "counterexample"]
    for r in alarms:
        print(f"FAIL  false alarm on {r['label']}: {r['detail']}")
    failures = check_t1(records) if args.check_t1 else []
    for failure in failures:
        print(f"FAIL  {failure}")
    if args.check_t1 and not failures:
        caught = [r for r in records if r["status"] == "counterexample"]
        print(
            f"ok    T1: {len(caught)} refuted, every other case as expected, median under {T1_MEDIAN_MS} ms"
        )
    return 1 if alarms or failures else 0


if __name__ == "__main__":
    sys.exit(main())
