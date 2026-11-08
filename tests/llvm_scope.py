#!/usr/bin/env python3
"""What "every optimization in the pinned LLVM" is, and how much of it is proved.

The denominator comes from the pinned source's pass registries: every name in the new pass manager's `.def`
files, LLVM's and each target's, and every legacy `INITIALIZE_PASS`. It doesn't come from what a pipeline run
happens to show, since a run only lists what one input, CPU and set of options needed. Pipeline runs are
recorded too, as a lower bound on where each pass runs. A name a pipeline shows that no registry has is added,
so nothing seen is left out.

Each pass is tied to the source files that implement it, with their hashes, so a claim about a pass goes stale
when its code changes. The coverage manifest, `tests/llvm_scope/coverage.json`, holds claims about passes, and
a pass is done only when it has complete all-input, code-binding and composition claims, in every context it
runs in, each with evidence whose hash matches. Translation validation on finite examples is recorded and
never counts toward done. A timeout, an unsupported case, an admitted proof or a proof-to-code gap is
unfinished.

usage:
  tests/llvm_scope.py generate                  write inventory.json from $LLVM_PROJECT_SRC, opt and llc
  tests/llvm_scope.py check [--offline]         derive it again and fail if it differs, then check the
                                                manifest and the tasks
  tests/llvm_scope.py summary [--json FILE]     print the measured scope and coverage

`check` and `generate` need the dev shell. `summary`, and `check --offline`, only read the files in the repo.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from collections import Counter, defaultdict
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "llvm_scope"
INVENTORY = HERE / "inventory.json"
COVERAGE = HERE / "coverage.json"
TASKS = ROOT / "docs" / "llvm-verification-tasks.md"
PROBES = ("probe-minimal.ll", "probe-loop.ll")

# The pinned revision. The source in the dev shell is a tarball of this tag, which has no git metadata, so the
# commit is recorded here, from `git ls-remote https://github.com/llvm/llvm-project
# refs/tags/llvmorg-23.1.3^{}`,
# and `check` confirms the version in the source and in the tools is this one.
PIN = {
    "version": "23.1.3",
    "tag": "llvmorg-23.1.3",
    "commit": "0d261d1ca552c95a8f007e061c787ac7132fbcbc",
    "source": "https://github.com/llvm/llvm-project/archive/llvmorg-23.1.3.tar.gz",
    "nixpkgs": "1d060086d60cb76a40cf37109f979d88a5bd6396",
}
OPT_PHASES = ("default", "thinlto-pre-link", "thinlto", "lto-pre-link", "lto")
LEVELS = ("O0", "O1", "O2", "O3", "Os", "Oz")
LLC_LEVELS = ("O0", "O1", "O2", "O3")
TIMEOUT = 120

# --- Reading the source -------------------------------------------------------------------------------------

MACRO = re.compile(r"^[ \t]*([A-Z][A-Z0-9_]*(?:PASS|ANALYSIS)[A-Z0-9_]*)\(", re.M)
STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')
INIT = re.compile(r"\bINITIALIZE_PASS(?:_BEGIN)?\(")
DEFINE = re.compile(r'^[ \t]*#[ \t]*define[ \t]+(\w+)[ \t]+"((?:[^"\\]|\\.)*)"', re.M)
CONST = re.compile(r'\b(?:const|constexpr)\b[^;=\n]*?\b(\w+)(?:\[\])?\s*=\s*"((?:[^"\\]|\\.)*)"\s*;')
RUN_DEF = re.compile(r"\b([A-Za-z_]\w*)(?:<[^<>;{}]*>)?::run\s*\(")
CLASS_DEF = re.compile(
    r"^\s*(?:class|struct)\s+(?:LLVM_\w+\s+)?([A-Za-z_]\w*)(?:\s+final)?\s*(?::|\{|$)", re.M
)
BUILDER_DEF = re.compile(r"\bPassBuilder::(build\w+)\s*\(")
CREATED = re.compile(r"\b(build\w+|\w+(?:Pass|Analysis|AA|Printer|Wrapper))\s*[(<]")
CL_OPT = re.compile(r"\bcl::(?:opt|list|bits)\s*<")
LEADING_CLASS = re.compile(r"\s*(?:::)?(?:[A-Za-z_]\w*::)*([A-Za-z_]\w*)\s*[({<]")


def call_args(text: str, start: int) -> tuple[list[str], int]:
    """The top-level arguments of the call whose `(` is at `start`, and the index after its `)`."""
    depth, args, cur, i, quote = 0, [], [], start, False
    while i < len(text):
        ch = text[i]
        if quote:
            cur.append(ch)
            if ch == "\\":
                cur.append(text[i + 1])
                i += 1
            elif ch == '"':
                quote = False
        elif ch == '"':
            quote = True
            cur.append(ch)
        elif ch in "([{":
            depth += 1
            if depth > 1:
                cur.append(ch)
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                args.append("".join(cur).strip())
                return args, i + 1
            cur.append(ch)
        elif ch == "," and depth == 1:
            args.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
        i += 1
    raise ValueError(f"unbalanced call at {start}")


def literal(arg: str) -> str | None:
    """The value of a string literal argument, joining adjacent literals, or None if it isn't one."""
    arg = re.sub(r"//[^\n]*", "", arg).strip()
    if not arg.startswith('"'):
        return None
    parts = STRING.findall(arg)
    if not parts or STRING.sub("", arg).strip():
        return None
    return "".join(parts)


def line_of(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def target_of(rel: str) -> str | None:
    m = re.match(r"llvm/lib/Target/([^/]+)/", rel)
    return m.group(1) if m else None


def unit_of(macro: str) -> str:
    for unit in ("MACHINE_FUNCTION", "MACHINE_MODULE", "LOOPNEST", "LOOP", "CGSCC", "FUNCTION", "MODULE"):
        if unit in macro:
            return unit.lower().replace("_", "-")
    return "unknown"


def kind_of(macro: str) -> str:
    if "DUMMY" in macro:
        return "dummy"
    return "analysis" if "ANALYSIS" in macro else "transform"


def registry_entries(rel: str, text: str) -> list[tuple[str, dict[str, Any]]]:
    """Every pass a new pass manager `.def` file registers, with a string literal for its name."""
    out = []
    for m in MACRO.finditer(text):
        try:
            args, _ = call_args(text, m.end() - 1)
        except ValueError:
            continue
        name = literal(args[0]) if args else None
        if name is None:
            continue  # A macro's own definition, or a parameter name.
        macro = m.group(1)
        entry: dict[str, Any] = {
            "registry": rel.rsplit("/", 1)[1],
            "macro": macro,
            "unit": unit_of(macro),
            "kind": kind_of(macro),
            "site": f"{rel}:{line_of(text, m.start(1))}",
        }
        if "WITH_PARAMS" in macro and len(args) >= 5:
            create = args[2]
            entry["class"] = literal(args[1]) or ""
            entry["params"] = literal(args[4]) or ""
        elif len(args) >= 2:
            create = args[1]
            cls = LEADING_CLASS.match(create)
            entry["class"] = cls.group(1) if cls else ""
        else:
            create = ""
        # What the registration builds, when its class isn't named plainly: a pipeline builder, or a pass made
        # behind a condition.
        entry["creates"] = sorted(set(CREATED.findall(create)) - {entry.get("class", "")})
        out.append((name, entry))
    return out


def legacy_entries(rel: str, text: str) -> list[tuple[str, dict[str, Any]]]:
    """Every `INITIALIZE_PASS` and `_BEGIN` in a file, resolving a name given as a macro or constant."""
    out = []
    names = {**dict(CONST.findall(text)), **dict(DEFINE.findall(text))}
    for m in INIT.finditer(text):
        # `#define INITIALIZE_PASS(...)` itself, in PassSupport.h.
        start = text.rfind("\n", 0, m.start()) + 1
        if text[start : m.start()].lstrip().startswith("#"):
            continue
        try:
            args, _ = call_args(text, m.end() - 1)
        except ValueError:
            continue
        if len(args) < 5:
            continue
        arg = literal(args[1])
        if arg is None:
            arg = names.get(args[1].strip())
        if arg is None:
            arg = f"?{args[1].strip()}@{rel}"  # Unresolved, and kept, so it still counts.
        out.append(
            (
                arg,
                {
                    "registry": "legacy",
                    "macro": "INITIALIZE_PASS",
                    "unit": "legacy",
                    "kind": "analysis" if args[4].strip() == "true" else "transform",
                    "class": args[0].strip(),
                    "site": f"{rel}:{line_of(text, m.start())}",
                },
            )
        )
    return out


def read_tree(src: Path) -> dict[str, str]:
    """Every C++ source and header under llvm/lib and llvm/include, by path relative to the monorepo."""
    files = {}
    for top in ("llvm/lib", "llvm/include"):
        for p in sorted((src / top).rglob("*")):
            if p.suffix in (".cpp", ".h", ".def", ".inc") and p.is_file():
                files[p.relative_to(src).as_posix()] = p.read_text(errors="replace")
    return files


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def category(name: str, kinds: set[str]) -> str:
    """A rough grouping for the summary only. Every category is in the denominator."""
    if kinds == {"analysis"}:
        return "analysis"
    if name.endswith("asm-printer"):
        return "emission"
    if re.search(r"^print|print$|-print|printer|^dot-|-dot|^view-|^aa-eval|verif|debugify|^no-op|^\?", name):
        return "printer-verifier-debug"
    if re.search(
        r"san\b|san-|^asan|^msan|^tsan|^hwasan|^dfsan|instrprof|^pgo|memprof|ctx-instr|sancov|"
        r"instrument|^gcov|insert-gcov|^cfi|ctx-prof|alloc-token|^nsan|^rtsan|^tysan|xray|patchable",
        name,
    ):
        return "instrumentation"
    return "transform"


def inventory_from_source(src: Path) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    files = read_tree(src)
    regs: list[tuple[str, dict[str, Any]]] = []
    registries = ["llvm/lib/Passes/PassRegistry.def", "llvm/include/llvm/Passes/MachinePassRegistry.def"]
    registries += sorted(r for r in files if re.match(r"llvm/lib/Target/[^/]+/[^/]+PassRegistry\.def$", r))
    for rel in registries:
        regs += registry_entries(rel, files[rel])
    for rel, text in files.items():
        if rel.endswith(".cpp") and "INITIALIZE_PASS" in text and rel.startswith("llvm/lib/"):
            regs += legacy_entries(rel, text)

    # Where each class's `run` is defined, and where each class is declared, for passes whose `run` is inline.
    runs: dict[str, set[str]] = defaultdict(set)
    decls: dict[str, set[str]] = defaultdict(set)
    for rel, text in files.items():
        if rel.endswith(".cpp"):
            for m in RUN_DEF.finditer(text):
                runs[m.group(1)].add(rel)
            for m in BUILDER_DEF.finditer(text):
                runs[m.group(1)].add(rel)
        if rel.endswith((".h", ".cpp")):
            for m in CLASS_DEF.finditer(text):
                decls[m.group(1)].add(rel)

    items: dict[str, dict[str, Any]] = {}
    for name, reg in regs:
        item = items.setdefault(name, {"name": name, "registrations": []})
        item["registrations"].append(reg)
    for item in items.values():
        anchors: set[str] = set()
        unresolved = []
        for reg in item["registrations"]:
            if reg["registry"] == "legacy":
                anchors.add(reg["site"].rsplit(":", 1)[0])
                continue
            cls = reg.get("class", "")
            found = set(runs.get(cls) or decls.get(cls) or ())
            if not found:
                for other in reg.get("creates", []):
                    found |= runs.get(other) or decls.get(other) or set()
            if found:
                anchors |= found
            elif reg["kind"] != "dummy":
                # A dummy has no new pass manager class yet, by design. Its legacy registration is its code.
                unresolved.append(cls or "(none)")
        if not anchors and not unresolved:
            unresolved = sorted({r.get("class") or "(none)" for r in item["registrations"]})
        item["registrations"].sort(key=lambda r: r["site"])
        item["anchors"] = {a: sha(files[a]) for a in sorted(anchors)}
        item["unresolved_classes"] = sorted(set(unresolved))
        item["cl_opts"] = sum(len(CL_OPT.findall(files[a])) for a in anchors)
        kinds = {r["kind"] for r in item["registrations"]}
        item["kinds"] = sorted(kinds)
        item["targets"] = sorted({t for r in item["registrations"] if (t := target_of(r["site"]))})
        item["category"] = category(item["name"], kinds)

    targets_dir = src / "llvm/lib/Target"
    anchor_files = {a for item in items.values() for a in item["anchors"]}
    source = {
        "cl_opts_in_anchor_files": sum(len(CL_OPT.findall(files[a])) for a in anchor_files),
        "llvm_version": llvm_version(src),
        "registries": {r: sha(files[r]) for r in registries},
        "target_dirs": sorted(p.name for p in targets_dir.iterdir() if p.is_dir()),
        "registrations": len(regs),
    }
    return items, source


def llvm_version(src: Path) -> str:
    text = (src / "cmake/Modules/LLVMVersion.cmake").read_text()
    parts = [re.search(rf"set\(LLVM_VERSION_{p} (\d+)\)", text) for p in ("MAJOR", "MINOR", "PATCH")]
    return ".".join(m.group(1) if m else "?" for m in parts)


# --- Reading the tools --------------------------------------------------------------------------------------


def tool(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, capture_output=True, text=True, timeout=TIMEOUT, check=False)


def pipeline_leaves(text: str) -> tuple[list[str], list[str], list[str]]:
    """The passes, adaptors and required analyses in a pipeline `opt -print-pipeline-passes` printed."""
    leaves, adaptors, analyses = [], [], []
    word = re.compile(r"[A-Za-z0-9_.\-]+")
    i = 0
    while i < len(text):
        if text[i] in ",() \n":
            i += 1
            continue
        m = word.match(text, i)
        if not m:
            raise ValueError(f"can't read pipeline at {i}: {text[i : i + 40]!r}")
        name, i = m.group(), m.end()
        params = ""
        if text[i : i + 1] == "<":
            depth, j = 0, i
            while j < len(text):
                depth += {"<": 1, ">": -1}.get(text[j], 0)
                if depth == 0:
                    break
                j += 1
            params, i = text[i + 1 : j], j + 1
        if text[i : i + 1] == "(":
            adaptors.append(name)
        elif name in ("require", "invalidate"):
            analyses.append(params)
        else:
            leaves.append(name)
    return leaves, adaptors, analyses


def opt_pipelines() -> dict[str, dict[str, Any]]:
    out = {}
    for phase in OPT_PHASES:
        for level in LEVELS:
            spec = f"{phase}<{level}>"
            r = subprocess.run(
                ["opt", "-disable-output", f"-passes={spec}", "-print-pipeline-passes"],
                input="",
                capture_output=True,
                text=True,
                timeout=TIMEOUT,
                check=False,
            )
            if r.returncode != 0:
                out[spec] = {
                    "error": r.stderr.strip().splitlines()[-1] if r.stderr.strip() else f"exit {r.returncode}"
                }
                continue
            out[spec] = {"pipeline": r.stdout.strip()}
    return out


def opt_names(p: dict[str, Any]) -> list[str]:
    """The passes and required analyses in one recorded `opt` pipeline, or none if it didn't build."""
    if "pipeline" not in p:
        return []
    leaves, _, analyses = pipeline_leaves(p["pipeline"])
    return sorted(set(leaves) | set(analyses))


def llc_archs() -> list[str]:
    text = tool("llc", "--version").stdout
    section = text.split("Registered Targets:", 1)[1]
    return sorted(m.group(1) for m in re.finditer(r"^\s+(\S+)\s+-", section, re.M))


def llc_passes(arch: str, level: str) -> dict[str, Any]:
    names: set[str] = set()
    errors = []
    for probe in PROBES:
        r = tool(
            "llc", f"-march={arch}", f"-{level}", "-debug-pass=Arguments", "-o", os.devnull, str(HERE / probe)
        )
        args = [line for line in r.stderr.splitlines() if line.startswith("Pass Arguments:")]
        if r.returncode != 0:
            lines = [x for x in r.stderr.strip().splitlines() if not x.startswith("Pass Arguments:")]
            said = [x for x in lines if "LLVM ERROR" in x or "error:" in x or "Assertion" in x]
            crash = [
                f"crash in {m.group(1)}" for x in lines if (m := re.search(r"Running pass '([^']+)'", x))
            ]
            first = re.sub(r"0x[0-9a-f]+", "0x?", (said or crash[-1:] or [f"exit {r.returncode}"])[0])
            errors.append(f"{probe}: {first[:160]}")
        for line in args:
            names |= {w[1:] for w in line.split()[2:] if w.startswith("-")}
    return {"passes": " ".join(sorted(names)), "errors": errors}


def llc_pipelines() -> dict[str, dict[str, Any]]:
    archs = llc_archs()
    jobs = [(a, lv) for a in archs for lv in LLC_LEVELS]
    workers = max(1, min(8, (os.cpu_count() or 1) // 2))
    with ThreadPoolExecutor(workers) as pool:
        results = list(pool.map(lambda j: llc_passes(*j), jobs))
    out: dict[str, dict[str, Any]] = {a: {} for a in archs}
    for (a, lv), res in zip(jobs, results, strict=True):
        out[a][lv] = res
    return out


def tools_versions() -> dict[str, Any]:
    def first(r: subprocess.CompletedProcess[str], pat: str) -> str:
        m = re.search(pat, r.stdout)
        return m.group(1) if m else "?"

    return {
        "opt": first(tool("opt", "--version"), r"LLVM version (\S+)"),
        "llc": first(tool("llc", "--version"), r"LLVM version (\S+)"),
        "targets_built": tool("llvm-config", "--targets-built").stdout.split(),
    }


def generate() -> dict[str, Any]:
    src_env = os.environ.get("LLVM_PROJECT_SRC")
    missing = [t for t in ("opt", "llc", "llvm-config") if shutil.which(t) is None]
    if not src_env or missing:
        raise SystemExit(f"needs the dev shell: LLVM_PROJECT_SRC={src_env!r}, missing tools {missing}")
    src = Path(src_env)
    items, source = inventory_from_source(src)
    versions = tools_versions()
    if not source["llvm_version"] == versions["opt"] == versions["llc"] == PIN["version"]:
        raise SystemExit(
            f"version mismatch: pinned {PIN['version']}, source {source['llvm_version']}, tools {versions}"
        )
    # Every pass opt can run by name has to be one the registries gave, or the reading of them missed
    # something.
    listed = {
        re.sub(r"<.*", "", n) for n in re.findall(r"^  (\S+)", tool("opt", "-print-passes").stdout, re.M)
    }
    missed = sorted(listed - items.keys() - {"require", "invalidate"})
    if missed:
        raise SystemExit(f"opt -print-passes lists passes the registries didn't give: {missed[:20]}")
    opt = opt_pipelines()
    llc = llc_pipelines()

    # Anything a pipeline ran that no registry names is added, with no registration, so it still counts.
    seen = {
        k.removeprefix("pass:"): v for k, v in contexts_of({"pipelines": {"opt": opt, "llc": llc}}).items()
    }
    for name in seen:
        if name not in items:
            items[name] = {
                "name": name,
                "registrations": [],
                "anchors": {},
                "unresolved_classes": ["(not registered)"],
                "cl_opts": 0,
                "kinds": ["unregistered"],
                "targets": [],
                "category": category(name, set()),
            }
    for name, item in items.items():
        item["id"] = f"pass:{name}"
        item["contexts"] = len(seen.get(name, ()))

    return {
        "schema": 1,
        "pin": PIN,
        "source": source,
        "tools": versions,
        "probes": {p: sha((HERE / p).read_text()) for p in PROBES},
        "pipelines": {"opt": opt, "llc": llc},
        "items": [items[k] for k in sorted(items)],
    }


def dump(inv: dict[str, Any]) -> str:
    """JSON with one pass per line, so a change to the inventory reads as a diff of the passes it touched."""
    head = {k: v for k, v in inv.items() if k != "items"}
    text = json.dumps(head, indent=1, sort_keys=True)
    lines = [json.dumps(item, sort_keys=True) for item in inv["items"]]
    return text[:-2] + ',\n "items": [\n  ' + ",\n  ".join(lines) + "\n ]\n}\n"


# --- Coverage -----------------------------------------------------------------------------------------------

DIMENSIONS = ("all-input", "analysis-soundness", "code-binding", "composition", "translation-validation")
STATUSES = ("complete", "partial", "admitted", "timeout", "unsupported", "failed")
EVIDENCE = ("lean-proof", "binding-check", "composition-proof", "tv-run", "test-log")
# What each dimension needs before `complete` means anything.
CLAIM_KEYS = {"item", "dimension", "contexts", "status", "evidence", "anchors", "assumptions", "gaps", "note"}
NEEDS = {
    "all-input": "lean-proof",
    "analysis-soundness": "lean-proof",
    "code-binding": "binding-check",
    "composition": "composition-proof",
}


def contexts_of(inv: dict[str, Any]) -> dict[str, set[str]]:
    seen: dict[str, set[str]] = defaultdict(set)
    for spec, p in inv["pipelines"]["opt"].items():
        for name in opt_names(p):
            seen[f"pass:{name}"].add(f"opt:{spec}")
    for arch, levels in inv["pipelines"]["llc"].items():
        for level, p in levels.items():
            for name in p["passes"].split():
                seen[f"pass:{name}"].add(f"llc:{arch}:{level}")
    return seen


def required(item: dict[str, Any]) -> list[str]:
    """The dimensions a pass needs complete to be done. A pass with both kinds needs both."""
    kinds = set(item["kinds"])
    dims = []
    if kinds - {"analysis"}:
        dims.append("all-input")
    if "analysis" in kinds:
        dims.append("analysis-soundness")
    return [*dims, "code-binding", "composition"]


# A verifier re-checks the evidence of a complete claim on its own: it replays the proof or the binding
# check, and decides whether it covers every context the pass runs in, given the claim, the pass, the
# contexts the inventory saw it in, and the repo. It returns None to accept, or why not. A status and a hash
# are written by whoever makes the claim, so without a verifier a complete claim stays unverified, and the
# pass isn't done. None exists yet: that's BIND-03 in docs/llvm-verification-tasks.md.
Verifier = Callable[[dict[str, Any], dict[str, Any], set[str], Path], "str | None"]
VERIFIERS: dict[str, Verifier] = {}


def evaluate(
    inv: dict[str, Any], cov: dict[str, Any], root: Path = ROOT, verifiers: dict[str, Verifier] | None = None
) -> tuple[list[str], dict[str, Any]]:
    """Errors in the manifest, and each pass's standing. Anything not verified complete is unfinished."""
    verifiers = VERIFIERS if verifiers is None else verifiers
    verified: set[tuple[str, str]] = set()
    errors: list[str] = []
    items = {i["id"]: i for i in inv["items"]}
    contexts = contexts_of(inv)
    if cov.get("schema") != 1:
        errors.append(f"coverage schema {cov.get('schema')!r} isn't 1")
    if cov.get("pin") != inv["pin"]["tag"]:
        errors.append(f"coverage is for {cov.get('pin')!r}, the inventory for {inv['pin']['tag']!r}")
    claims: dict[tuple[str, str], dict[str, Any]] = {}
    for n, c in enumerate(cov.get("claims", [])):
        where = f"claim {n} ({c.get('item')}, {c.get('dimension')})"
        before = len(errors)
        if set(c) - CLAIM_KEYS or not {"item", "dimension", "contexts", "status", "evidence"} <= set(c):
            errors.append(f"{where}: keys must be among {sorted(CLAIM_KEYS)}, with item to evidence required")
            continue
        item = items.get(c.get("item", ""))
        if item is None:
            errors.append(f"{where}: no such pass in the inventory")
            continue
        dim, status = c.get("dimension"), c.get("status")
        if dim not in DIMENSIONS:
            errors.append(f"{where}: dimension must be one of {DIMENSIONS}")
            continue
        if status not in STATUSES:
            errors.append(f"{where}: status must be one of {STATUSES}")
            continue
        if (c["item"], dim) in claims:
            errors.append(f"{where}: a second claim for the same pass and dimension")
            continue
        claims[(c["item"], dim)] = c
        ctx = c.get("contexts")
        if ctx != "all":
            if not isinstance(ctx, list) or not ctx:
                errors.append(f'{where}: contexts must be "all" or a non-empty list')
            else:
                unknown = [x for x in ctx if x not in contexts.get(c["item"], set()) and x != "registered"]
                if unknown:
                    errors.append(f"{where}: contexts the inventory never saw it in: {unknown[:5]}")
        for a in c.get("assumptions", []):
            if not str(a.get("text", "")).strip() or not str(a.get("justification", "")).strip():
                errors.append(f"{where}: every assumption needs text and a justification")
        evidence = c.get("evidence", [])
        for e in evidence:
            if e.get("kind") not in EVIDENCE:
                errors.append(f"{where}: evidence kind {e.get('kind')!r} must be one of {EVIDENCE}")
            path = (root / str(e.get("path", ""))).resolve()
            if not e.get("path") or not path.is_relative_to(root.resolve()) or not path.is_file():
                errors.append(f"{where}: evidence {e.get('path')!r} isn't a file in the repo")
            elif hashlib.sha256(path.read_bytes()).hexdigest() != e.get("sha256"):
                errors.append(f"{where}: evidence {e.get('path')} changed since the claim was made")
        if status != "complete":
            continue
        if not evidence:
            errors.append(f"{where}: complete with no evidence")
        if c.get("gaps"):
            errors.append(f"{where}: complete with gaps listed: {c['gaps']}")
        if dim == "translation-validation":
            errors.append(f"{where}: translation validation is finite, so it can't be complete; use partial")
        elif dim in NEEDS and not any(e.get("kind") == NEEDS[dim] for e in evidence):
            kinds = sorted({e.get("kind") for e in evidence})
            errors.append(f"{where}: complete needs {NEEDS[dim]} evidence, and has only {kinds}")
        if dim == "code-binding" and c.get("anchors") != item["anchors"]:
            errors.append(
                f"{where}: anchors differ from the pinned source's, so the binding is stale or partial"
            )
        if dim == "code-binding" and item["unresolved_classes"]:
            errors.append(f"{where}: the inventory couldn't find code for {item['unresolved_classes']}")
        verify = verifiers.get(NEEDS.get(dim, ""))
        if len(errors) == before and verify is not None:
            refusal = verify(c, item, contexts.get(c["item"], set()), root)
            if refusal:
                errors.append(f"{where}: the verifier refused it: {refusal}")
            else:
                verified.add((c["item"], dim))

    standing: dict[str, Any] = {}
    for iid, item in items.items():
        dims = {}
        for d in required(item):
            c = claims.get((iid, d))
            if c is None:
                dims[d] = "missing"
            elif c["status"] == "complete" and c.get("contexts") != "all":
                dims[d] = "partial"
            elif c["status"] == "complete" and (iid, d) not in verified:
                dims[d] = "unverified"
            else:
                dims[d] = c["status"]
        tv = claims.get((iid, "translation-validation"))
        standing[iid] = {
            "done": all(v == "complete" for v in dims.values()),
            "dimensions": dims,
            "translation_validation": tv["status"] if tv else "missing",
        }
    return errors, standing


# --- Tasks --------------------------------------------------------------------------------------------------

TASK = re.compile(r"^### ([A-Z]+-\d{2}): (.+)$", re.M)
FIELD = re.compile(r"^- \*\*([A-Za-z ]+):\*\* ?(.*)$", re.M)
TASK_FIELDS = ("Lane", "Scope", "Depends on", "Owns", "Acceptance", "Trust gaps", "Status", "Evidence")
TASK_STATUSES = ("not started", "in progress", "in review", "blocked", "complete")
LANES = ("INV", "SEM", "BIND", "AUTO", "PASS", "LOOP", "CG", "NEG")


def parse_tasks(text: str) -> dict[str, dict[str, str]]:
    tasks = {}
    heads = list(TASK.finditer(text))
    for n, h in enumerate(heads):
        body = text[h.end() : heads[n + 1].start() if n + 1 < len(heads) else len(text)]
        body = body.split("\n## ", 1)[0]
        fields = {m.group(1): m.group(2).strip() for m in FIELD.finditer(body)}
        tasks[h.group(1)] = {"title": h.group(2), **fields}
    return tasks


def check_tasks(text: str, root: Path = ROOT) -> list[str]:
    """Each task is whole, its dependencies exist and don't loop, and only evidence makes one complete."""
    errors = []
    tasks = parse_tasks(text)
    ids = [h.group(1) for h in TASK.finditer(text)]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        errors.append(f"{dup}: defined twice")
    deps: dict[str, list[str]] = {}
    for tid, t in tasks.items():
        for f in TASK_FIELDS:
            if not t.get(f):
                errors.append(f"{tid}: no {f}")
        lane = tid.split("-")[0]
        if lane not in LANES or t.get("Lane") != lane:
            errors.append(f"{tid}: lane {t.get('Lane')!r} must be {lane}, one of {LANES}")
        status = t.get("Status", "").split(":")[0].split(" (")[0].strip()
        if status not in TASK_STATUSES:
            errors.append(f"{tid}: status {t.get('Status')!r} must start with one of {TASK_STATUSES}")
        dep_text = t.get("Depends on", "")
        deps[tid] = [] if dep_text == "none" else re.findall(r"\b[A-Z]+-\d{2}\b", dep_text)
        for d in deps[tid]:
            if d not in tasks:
                errors.append(f"{tid}: depends on {d}, which isn't a task")
        if status == "complete":
            cited = re.findall(r"`([^`]+)`", t.get("Evidence", ""))
            real = [c for c in cited if (root / c).exists() or re.fullmatch(r"[0-9a-f]{7,40}", c)]
            if not real:
                errors.append(f"{tid}: complete needs evidence naming a file in the repo or a commit")
    statuses = {tid: t.get("Status", "").split(":")[0].split(" (")[0].strip() for tid, t in tasks.items()}
    for tid, t in tasks.items():
        open_deps = [d for d in deps[tid] if statuses.get(d) != "complete"]
        if statuses[tid] == "complete" and open_deps:
            errors.append(f"{tid}: complete while {open_deps} aren't")
        if statuses[tid] in ("in progress", "in review") and open_deps and not t.get("Gate waiver"):
            errors.append(f"{tid}: started before {open_deps} are complete, with no gate waiver saying why")

    # A loop in the dependencies would mean no task in it could ever start.
    state: dict[str, int] = {}

    def visit(tid: str, path: list[str]) -> None:
        state[tid] = 1
        for d in deps.get(tid, []):
            if state.get(d) == 1:
                errors.append(f"dependency loop: {' -> '.join([*path, tid, d])}")
            elif d in tasks and not state.get(d):
                visit(d, [*path, tid])
        state[tid] = 2

    for tid in tasks:
        if not state.get(tid):
            visit(tid, [])

    # Two tasks being worked on at once can't own the same file.
    owners: dict[str, list[str]] = defaultdict(list)
    for tid, t in tasks.items():
        if statuses[tid] in ("in progress", "in review"):
            for path in re.findall(r"`([^`]+)`", t.get("Owns", "")):
                owners[path].append(tid)
    for path, who in sorted(owners.items()):
        if len(who) > 1:
            errors.append(f"{path} is owned by {who} at once")
    return errors


# --- Summary ------------------------------------------------------------------------------------------------


def summarize(inv: dict[str, Any], standing: dict[str, Any]) -> dict[str, Any]:
    items = inv["items"]
    regs = Counter(r["registry"] for i in items for r in i["registrations"])
    ctx = contexts_of(inv)
    opt_ok = [s for s, p in inv["pipelines"]["opt"].items() if "error" not in p]
    llc = inv["pipelines"]["llc"]
    llc_failed = sorted(f"{a}:{lv}" for a, lvs in llc.items() for lv, p in lvs.items() if p["errors"])
    dims: dict[str, Counter[str]] = defaultdict(Counter)
    for s in standing.values():
        for d, v in s["dimensions"].items():
            dims[d][v] += 1
    built = set(inv["tools"]["targets_built"])
    classes: dict[str, set[str]] = defaultdict(set)
    for i in items:
        for r in i["registrations"]:
            if r.get("class") and r["kind"] != "dummy":
                classes[f"{'legacy' if r['registry'] == 'legacy' else 'new'}:{r['class']}"].add(i["name"])
    return {
        "pin": f"LLVM {inv['pin']['version']} ({inv['pin']['tag']}, {inv['pin']['commit']})",
        # Registration coverage: every name the pinned source registers is listed. It counts names, not
        # semantically distinct optimizations: see the two lists below, and the rewrites inside each pass.
        "registered_names": len(items),
        # Proof coverage: every required dimension complete in every context, and accepted by a verifier.
        "verified_done": sum(s["done"] for s in standing.values()),
        # Complete by the manifest's own say, verified or not. Never a substitute for verified_done.
        "claimed_complete": sum(
            all(v in ("complete", "unverified") for v in s["dimensions"].values()) for s in standing.values()
        ),
        # One name over code in more than one source file: the count is too small by these.
        "names_with_several_implementations": sorted(
            i["name"] for i in items if sum(a.endswith(".cpp") for a in i["anchors"]) > 1
        ),
        # One class under more than one name: the count is too large by these.
        "classes_under_several_names": {k: sorted(v) for k, v in sorted(classes.items()) if len(v) > 1},
        "in_unbuilt_targets": sum(bool(i["targets"]) and not set(i["targets"]) & built for i in items),
        "by_category": dict(sorted(Counter(i["category"] for i in items).items())),
        "by_kind": dict(sorted(Counter("+".join(i["kinds"]) for i in items).items())),
        "generic": sum(not i["targets"] for i in items),
        "by_target": dict(sorted(Counter(t for i in items for t in i["targets"]).items())),
        "registrations": dict(sorted(regs.items())),
        "unregistered": sorted(i["name"] for i in items if not i["registrations"]),
        "unresolved_code": sum(bool(i["unresolved_classes"]) for i in items),
        "anchor_files": len({a for i in items for a in i["anchors"]}),
        "cl_opts_in_anchor_files": inv["source"]["cl_opts_in_anchor_files"],
        "never_seen_in_a_pipeline": sum(not ctx.get(i["id"]) for i in items),
        "opt_pipelines": f"{len(opt_ok)} of {len(inv['pipelines']['opt'])} phase and level pairs build",
        "opt_pipeline_errors": sorted(s for s, p in inv["pipelines"]["opt"].items() if "error" in p),
        "llc": f"{len(llc)} registered targets x {len(LLC_LEVELS)} levels, "
        f"{len(llc_failed)} with a probe failing",
        "targets_built": inv["tools"]["targets_built"],
        "target_dirs_not_built": sorted(
            set(inv["source"]["target_dirs"]) - set(inv["tools"]["targets_built"])
        ),
        "dimensions": {d: dict(sorted(c.items())) for d, c in sorted(dims.items())},
        "translation_validation": dict(
            sorted(Counter(s["translation_validation"] for s in standing.values()).items())
        ),
    }


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("generate")
    chk = sub.add_parser("check")
    chk.add_argument(
        "--offline", action="store_true", help="skip deriving the inventory again, which needs LLVM"
    )
    summ = sub.add_parser("summary")
    summ.add_argument("--json", type=Path)
    args = ap.parse_args()

    if args.cmd == "generate":
        INVENTORY.write_text(dump(generate()))
        print(f"wrote {INVENTORY.relative_to(ROOT)}")
        return 0

    inv = load(INVENTORY)
    errors, standing = evaluate(inv, load(COVERAGE))
    errors += check_tasks(TASKS.read_text())
    if args.cmd == "check" and not args.offline:
        fresh = dump(generate())
        if fresh != INVENTORY.read_text():
            new = json.loads(fresh)
            old_ids = {i["id"]: i for i in inv["items"]}
            new_ids = {i["id"]: i for i in new["items"]}
            changed = sorted(i for i in old_ids.keys() & new_ids.keys() if old_ids[i] != new_ids[i])
            errors.append(
                "inventory.json differs from the pinned source and tools: "
                f"added {sorted(new_ids.keys() - old_ids.keys())[:10]}, "
                f"removed {sorted(old_ids.keys() - new_ids.keys())[:10]}, changed {changed[:10]}, "
                f"other sections differ: {[k for k in new if k != 'items' and new[k] != inv.get(k)]}. "
                "Moving the pin means running `generate` and reviewing the diff in the same commit."
            )
    summary = summarize(inv, standing)
    if args.cmd == "summary":
        if args.json:
            args.json.write_text(
                json.dumps({"summary": summary, "standing": standing}, indent=1, sort_keys=True)
            )
        print(json.dumps(summary, indent=1))
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    print(
        f"verified done {summary['verified_done']}/{summary['registered_names']} registered pass names "
        f"(claimed complete {summary['claimed_complete']}) at {summary['pin']} | "
        f"{len(errors)} manifest or task errors",
        file=sys.stderr,
    )
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
