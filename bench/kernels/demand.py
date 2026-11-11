#!/usr/bin/env python3
"""What the emitter makes today of the kernel corpus's candidates: the demand the coverage and x86 lanes work
from. docs/kernels.md.

For each project in bench/kernels/manifest.toml that has units, this:

1. Fetches its source through Nix, at the commit and hash the manifest pins. Nothing is copied into the repo.
2. Runs the project's own configure step, if the manifest gives one, only for the headers it generates.
3. Compiles each unit to LLVM IR with the dev shell's clang, the pinned one, at the corpus's -O3, with the
   flags the project builds that file with. Twice: as the project builds it, and relaxed, with
   -fno-strict-aliasing added, since the emitter refuses `!tbaa`, which a default build has on nearly every
   load, and with the project's `relax` flags, if the manifest gives any.
4. Runs build/ir-lean --report on each, and counts the functions it translates, and what stops the rest, by
   reason. The emitter gives a function's first reason only, so a function it refuses for one may have more.
5. Counts the intrinsics each unit calls, and gives each its class in tests/llvm_scope/ir-features.json:
   modeled, assumed or refused, and for a refused one, the lane that holds it.

It measures what the code is and what the emitter does with it. It searches for nothing and rewrites nothing.

usage: bench/kernels/demand.py run [--project NAME]... [--jobs N] [--work DIR] [--out FILE]
       bench/kernels/demand.py table [FILE]        the results as the tables docs/kernels.md has
       bench/kernels/demand.py check [--offline]   every unit compiles, and defines the kernels named

`check --offline` exits 77, which ctest takes as a skip, if a project's source isn't in the Nix store already.
"""

from __future__ import annotations

import argparse
import os
import re
import shlex
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
import kernels  # noqa: E402
from irlean import pins, proc, schemas  # noqa: E402

EMITTER = ROOT / "build" / "ir-lean"
FEATURES = ROOT / "tests" / "llvm_scope" / "ir-features.json"
RESULTS = Path(__file__).resolve().parent / "results" / "demand.json"
WORK = ROOT / "build" / "kernels"
SKIP = 77
# `relaxed` isn't how any project is built. It says what stops a function once `!tbaa` doesn't: the same flags
# with -fno-strict-aliasing, and with a project's `relax` flags, which undo flags of its own that the emitter
# refuses.
VARIANTS = ("as-built", "relaxed")
RELAX = ["-fno-strict-aliasing"]

DEFINE = re.compile(r'^define\b.*?@("[^"]+"|[\w.$-]+)\(')
CALLEE = re.compile(r'@(llvm\.[\w.]+|"llvm\.[^"]+")\(')
VECTOR = re.compile(r"<\d+ x [^>]+>")
FLOAT = re.compile(r"\b(half|bfloat|float|double|fp128|x86_fp80)\b")
X86 = "llvm.x86."


def environment() -> dict[str, str]:
    """The dev shell's, with what its compiler wrapper adds that stock clang doesn't turned off, as
    tests/llama.py does."""
    return {**os.environ, "NIX_HARDENING_ENABLE": "", "NIX_ENFORCE_NO_NATIVE": "0"}


def pinned_clang() -> pins.Tool | None:
    """The clang on PATH, if it's the version tests/llvm/targets.toml pins."""
    clang = pins.tool("clang")
    if clang is None or f"clang version {pins.llvm_version()}" not in clang.version:
        return None
    return clang


def features() -> dict[str, dict[str, str]]:
    """Every intrinsic the pinned LLVM has, with its class and, if refused, its lane."""
    items = schemas.read(FEATURES, schemas.IR_FEATURES)["items"]
    return {i["name"]: i for i in items if i["kind"] == "intrinsic"}


def base(callee: str, known: dict[str, dict[str, str]]) -> str:
    """An intrinsic's name without the types it's overloaded on: `llvm.umin.i64` is `llvm.umin`."""
    parts = callee.strip('"').split(".")
    for n in range(len(parts), 1, -1):
        if ".".join(parts[:n]) in known:
            return ".".join(parts[:n])
    return callee.strip('"')


def reason(raw: str, known: dict[str, dict[str, str]]) -> str:
    """A refusal without the names and values it's about, so refusals of one kind count together."""
    cycle = "in a cycle with a function that has "
    if raw.startswith(cycle):
        return "in a cycle with a function refused for: " + reason(raw.removeprefix(cycle), known)
    if raw.startswith("intrinsic llvm."):
        return "intrinsic " + base(raw.split()[1].rstrip(","), known)
    if m := re.match(r"(metadata !\w+)", raw):
        return m[1]
    if raw.startswith("operand") and " asm " in raw.split('"')[0]:
        return "inline assembly"
    if raw.startswith("instruction "):
        # The opcode, and the form of it the emitter names: `load volatile`, `freeze` of a vector.
        words = re.sub(r"^instruction\s+(%[\w.$-]+ = )?", "", raw).split()
        form = " volatile" if words[1:2] == ["volatile"] else ""
        form = " of a vector" if words[0] == "freeze" and words[1:2] and words[1].startswith("<") else form
        return f"instruction {words[0]}{form}"
    if m := re.match(r"llvm\.loop\.mustprogress on .*!llvm\.loop !\d+, (.*)$", raw):
        return "llvm.loop.mustprogress " + m[1]
    if re.match(r"type <\d+ x ptr>", raw):
        return "type: a vector of pointers"
    text = re.sub(r'@("[^"]+"|[\w.$-]+)', "@_", raw)
    text = re.sub(r"%[\w.$-]+", "%_", text)
    text = re.sub(r'("[\w.-]+")="[^"]*"', r"\1", text)
    text = re.sub(r"\(\d+\)", "", text)
    return re.split(r" on %_| on  |: %_ = ", text)[0].strip()


def functions(ll: str) -> dict[str, list[str]]:
    """Each function a module defines, with the lines of its body."""
    out: dict[str, list[str]] = {}
    body: list[str] | None = None
    for line in ll.splitlines():
        if body is None:
            if m := DEFINE.match(line):
                body = out.setdefault(m[1].strip('"'), [])
        elif line == "}":
            body = None
        else:
            body.append(line)
    return out


def instructions(body: list[str]) -> int:
    """How many instructions a body has: its lines, but labels, comments and the cases of a `switch`."""
    return sum(
        1
        for line in body
        if line.startswith("  ") and not line.startswith("    ") and line.strip() != "]" and line.strip()
    )


def describe(body: list[str], known: dict[str, dict[str, str]]) -> dict[str, Any]:
    """What a function's body is made of."""
    text = "\n".join(body)
    return {
        "instructions": instructions(body),
        "vector": bool(VECTOR.search(text)),
        "float": bool(FLOAT.search(text)),
        "intrinsics": dict(sorted(Counter(base(c, known) for c in CALLEE.findall(text)).items())),
    }


def report(ll: Path) -> dict[str, str]:
    """What build/ir-lean --report says of each function in a module: `ok`, or why it's refused."""
    r = proc.run([EMITTER, ll, "--report"], timeout=600)
    if r.exit != 0:
        raise RuntimeError(f"ir-lean on {ll} exited {r.exit}\n{r.output[-2000:]}")
    out: dict[str, str] = {}
    for line in r.out.splitlines():
        fields = line.split("\t")
        if fields[0] == "ok":
            out[fields[1]] = "ok"
        elif fields[0] == "unsupported":
            out[fields[1]] = fields[2]
    return out


def places(
    name: str, project: dict[str, Any], src: Path, build: Path, offline: bool
) -> dict[str, str] | None:
    """What `{src}`, `{build}` and `{dep:NAME}` stand for in a project's paths, or None if `offline` and the
    store lacks one of its dependencies."""
    out = {"src": str(src), "build": str(build)}
    for dep in project.get("dep", []):
        path = kernels.source(f"{name}'s {dep['name']}", dep, offline)
        if path is None:
            return None
        out[f"dep:{dep['name']}"] = str(path)
    return out


def fill(text: str, where: dict[str, str]) -> str:
    for key, value in where.items():
        text = text.replace("{" + key + "}", value)
    return text


def configure(name: str, project: dict[str, Any], src: Path, work: Path) -> Path:
    """Runs a project's configure step, for the headers it generates, and returns where it ran."""
    build = work / "configure"
    if "configure" not in project or (build / ".done").exists():
        return build
    build.mkdir(parents=True, exist_ok=True)
    argv = [a.format(src=src, build=build) for a in project["configure"]]
    r = proc.run(argv, cwd=build, env=environment(), timeout=1800)
    if not r.ok:
        raise RuntimeError(f"{name}: configure failed\n{' '.join(argv)}\n{r.output[-3000:]}")
    (build / ".done").write_text("")
    return build


def command(
    corpus: dict[str, Any], project: dict[str, Any], unit: dict[str, Any], where: dict[str, str], out: Path
) -> list[str]:
    """The compile command for a unit: the project's, with the corpus's level, giving IR."""
    source = Path(where["src"]) / unit["source"]
    compiler = "clang++" if source.suffix in (".cc", ".cpp", ".cxx") else "clang"
    include = [f"-I{fill(i, where)}" for i in project.get("include", [])]
    return [
        compiler,
        corpus["opt"],
        *corpus.get("flags", []),
        *project.get("flags", []),
        *unit.get("flags", []),
        *include,
        # The target and its C headers, so a C unit's IR is the same on any host, as tests/proofs.sh has it. A
        # C++ unit takes the host's, as tests/llama.py does: these flags put the C headers before libstdc++'s.
        *(shlex.split(os.environ.get("PROOF_CFLAGS", "")) if compiler == "clang" else []),
        "-S",
        "-emit-llvm",
        "-o",
        str(out),
        str(source),
    ]


def measure_unit(
    name: str,
    corpus: dict[str, Any],
    project: dict[str, Any],
    unit: dict[str, Any],
    where: dict[str, str],
    work: Path,
    known: dict[str, dict[str, str]],
) -> dict[str, Any]:
    stem = re.sub(r"[^\w.-]", "_", unit["source"])
    record: dict[str, Any] = {"source": unit["source"], "flags": unit.get("flags", []), "variants": {}}
    kernel_records: dict[str, dict[str, Any]] = {k: {} for k in unit.get("kernels", [])}
    for variant in VARIANTS:
        ll = work / f"{stem}.{variant}.ll"
        argv = command(corpus, project, unit, where, ll)
        if variant == "relaxed":
            # Before the output and the source, and after the project's flags, so these win.
            argv[-5:-5] = [*RELAX, *project.get("relax", [])]
        r = proc.run(argv, env=environment(), timeout=1800)
        if not r.ok:
            raise RuntimeError(f"{name}: {unit['source']} didn't compile\n{' '.join(argv)}\n{r.err[-3000:]}")
        bodies = functions(ll.read_text())
        verdicts = report(ll)
        if set(verdicts) != set(bodies):
            raise RuntimeError(
                f"{name}: {unit['source']}: ir-lean reported on other functions than the IR has"
            )
        refused = [reason(v, known) for v in verdicts.values() if v != "ok"]
        record["variants"][variant] = {
            "functions": len(bodies),
            "translated": len(bodies) - len(refused),
            "refused": dict(sorted(Counter(refused).items(), key=lambda kv: (-kv[1], kv[0]))),
        }
        if variant == "as-built":
            whole = describe([line for body in bodies.values() for line in body], known)
            record["instructions"] = whole["instructions"]
            record["intrinsics"] = whole["intrinsics"]
        for k, kr in kernel_records.items():
            if k not in bodies:
                raise RuntimeError(
                    f"{name}: {unit['source']} defines no function {k}, which the manifest names"
                )
            if variant == "as-built":
                kr.update(describe(bodies[k], known))
            kr[variant] = "ok" if verdicts[k] == "ok" else reason(verdicts[k], known)
    record["kernels"] = kernel_records
    return record


def measure(
    name: str, manifest: dict[str, Any], work: Path, jobs: int, offline: bool = False
) -> dict[str, Any]:
    """One project's demand, or `{"missing": True}` if `offline` and its source isn't in the store."""
    project = manifest["project"][name]
    src = kernels.source(name, project, offline)
    if src is None:
        return {"missing": True}
    work = work / name
    work.mkdir(parents=True, exist_ok=True)
    build = configure(name, project, src, work)
    where = places(name, project, src, build, offline)
    if where is None:
        return {"missing": True}
    known = features()
    with ThreadPoolExecutor(jobs) as pool:
        units = list(
            pool.map(
                lambda u: measure_unit(name, manifest["corpus"], project, u, where, work, known),
                project["unit"],
            )
        )
    return {"rev": project["rev"], "nix_hash": project["nix_hash"], "units": units}


def totals(units: list[dict[str, Any]], known: dict[str, dict[str, str]]) -> dict[str, Any]:
    """A project's units added up."""
    out: dict[str, Any] = {"units": len(units), "instructions": sum(u["instructions"] for u in units)}
    for variant in VARIANTS:
        refused: Counter[str] = Counter()
        for u in units:
            refused.update(u["variants"][variant]["refused"])
        out[variant] = {
            "functions": sum(u["variants"][variant]["functions"] for u in units),
            "translated": sum(u["variants"][variant]["translated"] for u in units),
            "refused": dict(sorted(refused.items(), key=lambda kv: (-kv[1], kv[0]))),
        }
    calls: Counter[str] = Counter()
    for u in units:
        calls.update(u["intrinsics"])
    out["intrinsics"] = {
        i: {
            "calls": n,
            "class": known.get(i, {}).get("class", "unknown"),
            **({"lane": known[i]["lane"]} if "lane" in known.get(i, {}) else {}),
        }
        for i, n in sorted(calls.items())
    }
    ks = [k for u in units for k in u["kernels"].values()]
    out["kernels"] = {
        "named": len(ks),
        **{variant: sum(1 for k in ks if k.get(variant) == "ok") for variant in VARIANTS},
    }
    return out


def run(args: argparse.Namespace) -> int:
    manifest = kernels.load()
    if found := kernels.problems(manifest):
        print("\n".join(f"FAIL {line}" for line in found))
        return 1
    with_units = [n for n, p in manifest["project"].items() if p.get("unit")]
    names = args.project or with_units
    if unknown := [n for n in names if n not in with_units]:
        print(f"no units for {', '.join(unknown)}", file=sys.stderr)
        return 2
    clang = pinned_clang()
    if clang is None:
        print(f"clang isn't the pinned {pins.llvm_version()}: run this in `nix develop`", file=sys.stderr)
        return 1
    known = features()
    previous = (
        schemas.read(args.out, schemas.KERNELS_DEMAND)["projects"]
        if args.project and args.out.exists()
        else {}
    )
    projects: dict[str, Any] = {n: previous[n] for n in with_units if n in previous and n not in names}
    for name in names:
        result = measure(name, manifest, args.work, args.jobs)
        result["totals"] = totals(result["units"], known)
        projects[name] = result
        t = result["totals"]
        print(
            f"ok   {name}: {t['units']} units, {t['as-built']['translated']}/{t['as-built']['functions']} "
            f"functions translate as built, {t['relaxed']['translated']}/"
            f"{t['relaxed']['functions']} relaxed",
            flush=True,
        )
    head = proc.run(["git", "-C", ROOT, "rev-parse", "HEAD"], timeout=60).out.strip()
    record = {
        "schema": schemas.KERNELS_DEMAND,
        "generated_by": "bench/kernels/demand.py run",
        "date": proc.now()[:10],
        "commit": head,
        "clang": clang.version.splitlines()[0] if clang.version else "",
        "opt": manifest["corpus"]["opt"],
        "variants": {"as-built": [], "relaxed": RELAX},
        "projects": {n: projects[n] for n in sorted(projects)},
    }
    schemas.write(args.out, record, schemas.KERNELS_DEMAND, indent=1)
    print(f"wrote {args.out}")
    return 0


def check(args: argparse.Namespace) -> int:
    """Every unit compiles at the pin and defines the kernels the manifest names."""
    manifest = kernels.load()
    if found := kernels.problems(manifest):
        print("\n".join(f"FAIL {line}" for line in found))
        return 1
    if not EMITTER.exists() or pinned_clang() is None:
        print("skip: this needs build/ir-lean and the pinned clang")
        return SKIP
    missing = []
    for name, project in sorted(manifest["project"].items()):
        if not project.get("unit"):
            continue
        result = measure(name, manifest, args.work, args.jobs, args.offline)
        if result.get("missing"):
            missing.append(name)
            continue
        named = sum(len(u["kernels"]) for u in result["units"])
        print(f"ok   {name}: {len(result['units'])} units compile, and define the {named} kernels named")
    if missing:
        print(
            f"skip: not in the Nix store: {', '.join(missing)}. `bench/kernels/demand.py check` fetches them"
        )
        return SKIP
    return 0


def table(args: argparse.Namespace) -> int:
    record = schemas.read(args.file, schemas.KERNELS_DEMAND)
    manifest = kernels.load()
    print("| Project | Units | Instructions | Functions | Translate as built | Relaxed |")
    print("| --- | ---: | ---: | ---: | ---: | ---: |")
    for name, p in record["projects"].items():
        t = p["totals"]
        print(
            f"| {name} | {t['units']} | {t['instructions']:,} | {t['as-built']['functions']} | "
            f"{t['as-built']['translated']} | {t['relaxed']['translated']} |"
        )
    print()
    print("| Project | Kernels named | Translate as built | Relaxed |")
    print("| --- | ---: | ---: | ---: |")
    for name, p in record["projects"].items():
        k = p["totals"]["kernels"]
        print(f"| {name} | {k['named']} | {k['as-built']} | {k['relaxed']} |")
    print()
    print("| Project | What stops the rest, relaxed: functions by first reason |")
    print("| --- | --- |")
    for name, p in record["projects"].items():
        refused = p["totals"]["relaxed"]["refused"]
        shown = "; ".join(f"{r}: {n}" for r, n in list(refused.items())[:8])
        rest = sum(list(refused.values())[8:])
        print(f"| {name} | {shown}{f'; others: {rest}' if rest else ''} |")
    print()
    print("| Project | `llvm.x86.*` the model has, with calls | `llvm.x86.*` it refuses, with calls |")
    print("| --- | --- | --- |")
    for name, p in record["projects"].items():
        x86 = {i: v for i, v in p["totals"]["intrinsics"].items() if i.startswith(X86)}
        have = ", ".join(
            f"`{i.removeprefix(X86)}` {v['calls']}" for i, v in x86.items() if v["class"] == "modeled"
        )
        lack = ", ".join(
            f"`{i.removeprefix(X86)}` {v['calls']}" for i, v in x86.items() if v["class"] != "modeled"
        )
        print(f"| {name} | {have or 'None'} | {lack or 'None'} |")
    live = {
        n: p
        for n, p in record["projects"].items()
        if manifest["project"].get(n, {}).get("status") != "rejected"
    }
    print()
    print("| What stops a function, relaxed, in the projects that aren't rejected | Functions | Projects |")
    print("| --- | ---: | --- |")
    reasons: Counter[str] = Counter()
    where: dict[str, list[str]] = {}
    for name, p in live.items():
        for r, n in p["totals"]["relaxed"]["refused"].items():
            reasons[r] += n
            where.setdefault(r, []).append(name)
    for r, n in sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"| {r} | {n} | {', '.join(where[r])} |")
    print()
    print("| Intrinsic the model refuses, in the projects that aren't rejected | Calls | Lane | Projects |")
    print("| --- | ---: | --- | --- |")
    calls: Counter[str] = Counter()
    lanes: dict[str, str] = {}
    users: dict[str, list[str]] = {}
    for name, p in live.items():
        for i, v in p["totals"]["intrinsics"].items():
            if v["class"] == "refused":
                calls[i] += v["calls"]
                lanes[i] = v.get("lane", "none")
                users.setdefault(i, []).append(name)
    for i, n in sorted(calls.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"| `{i}` | {n} | {lanes[i]} | {', '.join(users[i])} |")
    print()
    print("| Project | Kernel | Instructions | As built | Relaxed | Intrinsics it calls |")
    print("| --- | --- | ---: | --- | --- | --- |")
    for name, p in record["projects"].items():
        if manifest["project"].get(name, {}).get("status") == "rejected":
            continue
        for u in p["units"]:
            for k, kr in u["kernels"].items():
                called = ", ".join(f"`{i.removeprefix('llvm.')}` {n}" for i, n in kr["intrinsics"].items())
                print(
                    f"| {name} | `{k}` | {kr['instructions']:,} | {kr['as-built']} | "
                    f"{kr['relaxed']} | {called or 'None'} |"
                )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=(__doc__ or "").split("\n\n")[0])
    sub = parser.add_subparsers(dest="mode", required=True)
    r = sub.add_parser("run")
    r.add_argument("--project", action="append")
    r.add_argument("--out", type=Path, default=RESULTS)
    c = sub.add_parser("check")
    c.add_argument("--offline", action="store_true")
    for p in (r, c):
        p.add_argument("--jobs", type=int, default=8)
        p.add_argument("--work", type=Path, default=WORK)
    t = sub.add_parser("table")
    t.add_argument("file", type=Path, nargs="?", default=RESULTS)
    args = parser.parse_args()
    try:
        return {"run": run, "check": check, "table": table}[args.mode](args)
    except RuntimeError as e:
        print(f"FAIL {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
