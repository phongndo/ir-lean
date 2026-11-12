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
4. Runs build/ir-lean --reasons on each, and counts the functions it translates, and what stops the rest:
   by first reason, by every reason the emitter's checks find, and by what lifting one kind of refusal alone
   would translate, through the calls and cycles between functions. An instruction gives one reason at most,
   so lifting one can uncover another behind it there, and a function whose checks stopped early counts as
   stopped by what they didn't reach.
5. Counts the intrinsics each unit calls, and gives each its class in tests/llvm_scope/ir-features.json:
   modeled, assumed or refused, and for a refused one, the lane that holds it.

It measures what the code is and what the emitter does with it. It searches for nothing and rewrites nothing.

usage: bench/kernels/demand.py run [--project NAME]... [--jobs N] [--work DIR] [--out FILE]
       bench/kernels/demand.py table [FILE]        the results as the tables docs/kernels.md has
       bench/kernels/demand.py check [--offline]   every unit compiles, and defines the kernels named, and
                                                   every test a workload's check names is at the pin

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
# A reason that's another function in the module being refused, which `--reasons` gives by its name.
DEPENDS = re.compile(
    r"^(?:call to|indirect call that can reach|in a cycle with) @(.+), which isn't translated$"
)
# What stops a function whose checks a refusal stopped before they all ran: never lifted.
UNSURVEYED = "checks that didn't run, past a refusal"
# Each refused function in a module: its own kinds of refusal, and the functions in the module it waits on.
Blocked = dict[str, tuple[frozenset[str], frozenset[str]]]
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
    if raw.startswith("instruction ") and (m := re.search(r'@llvm\.assume\(.*\[ "(\w+)"', raw)):
        return f"operand bundle assume:{m[1]}"
    if raw.startswith("instruction ") and re.search(r"getelementptr .*, <\d+ x i\d+> ", raw):
        return "instruction getelementptr of vectors"
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


def report(ll: Path) -> dict[str, dict[str, Any]]:
    """What build/ir-lean --reasons says of each function in a module: `first`, `ok` or the reason --report
    gives, every reason its checks found, and whether they stopped early."""
    r = proc.run([EMITTER, ll, "--reasons"], timeout=600)
    if r.exit != 0:
        raise RuntimeError(f"ir-lean on {ll} exited {r.exit}\n{r.output[-2000:]}")
    return parse_reasons(r.out)


def parse_reasons(text: str) -> dict[str, dict[str, Any]]:
    """`ir-lean --reasons`' output, by function. Anything but what the emitter prints is an error, so nothing
    is read as less than it says: a line this doesn't know, a function twice, a reason or `partial` for one it
    didn't refuse, a refused function with no reason, a dependency on a name that isn't a refused function in
    the module, and a last line other than one `translated N/M` that agrees with the rest."""
    out: dict[str, dict[str, Any]] = {}
    lines = text.splitlines()
    total = re.fullmatch(r"translated (\d+)/(\d+)", lines[-1]) if lines else None
    if not total:
        raise RuntimeError("ir-lean --reasons didn't end with `translated N/M`")
    for line in lines[:-1]:
        fields = line.split("\t")
        if fields[0] in ("ok", "unsupported") and len(fields) == (7 if fields[0] == "ok" else 3):
            if fields[1] in out:
                raise RuntimeError(f"ir-lean --reasons reported {fields[1]} twice")
            first = "ok" if fields[0] == "ok" else fields[2]
            out[fields[1]] = {"first": first, "reasons": [], "partial": False}
        elif fields[0] in ("reason", "partial") and len(fields) == (3 if fields[0] == "reason" else 2):
            if out.get(fields[1], {}).get("first", "ok") == "ok":
                raise RuntimeError(
                    f"ir-lean --reasons gave a {fields[0]} for {fields[1]}, which it didn't refuse"
                )
            if fields[0] == "reason":
                out[fields[1]]["reasons"].append(fields[2])
            else:
                out[fields[1]]["partial"] = True
        else:
            raise RuntimeError(f"ir-lean --reasons printed a line this doesn't read: {line!r}")
    ok = sum(1 for v in out.values() if v["first"] == "ok")
    if (int(total[1]), int(total[2])) != (ok, len(out)):
        raise RuntimeError(f"ir-lean --reasons said `{lines[-1]}` of {ok} translated and {len(out)} reported")
    for name, v in out.items():
        if v["first"] != "ok" and not v["reasons"]:
            raise RuntimeError(f"ir-lean --reasons refused {name} and gave no reason")
    closed({n: (frozenset(), frozenset(waits(v["reasons"]))) for n, v in out.items() if v["first"] != "ok"})
    return out


def waits(reasons: list[str]) -> set[str]:
    """The functions in the module that reasons say a function waits on."""
    return {m[1] for r in reasons if (m := DEPENDS.match(r))}


def closed(blocked: Blocked) -> Blocked:
    """`blocked`, if every function one waits on is refused in it too. A name that isn't would drop out of
    `translated_with` and `needs`, counting what waits on it as free."""
    for name, (_, deps) in blocked.items():
        if missing := sorted(deps - set(blocked)):
            raise RuntimeError(f"{name} waits on {', '.join(missing)}, which isn't a refused function here")
    return blocked


def blockers(verdicts: dict[str, dict[str, Any]], known: dict[str, dict[str, str]]) -> Blocked:
    """Each refused function's own kinds of refusal, and the functions in its module it waits on."""
    out = {}
    for name, v in verdicts.items():
        if v["first"] == "ok":
            continue
        own, deps = set(), set()
        for raw in v["reasons"]:
            if m := DEPENDS.match(raw):
                deps.add(m[1])
            else:
                own.add(reason(raw, known))
        if v["partial"] or not v["reasons"]:
            own.add(UNSURVEYED)
        out[name] = (frozenset(own), frozenset(deps))
    return closed(out)


def translated_with(lifted: set[str], blocked: Blocked) -> set[str]:
    """The refused functions that would translate with every kind of refusal in `lifted` lifted: those whose
    own kinds are all lifted and that wait on no function still refused."""
    stuck = {f for f, (own, _) in blocked.items() if not own <= lifted}
    changed = True
    while changed:
        changed = False
        for f, (_, deps) in blocked.items():
            if f not in stuck and deps & stuck:
                stuck.add(f)
                changed = True
    return set(blocked) - stuck


def needs(name: str, blocked: Blocked) -> list[str]:
    """Every kind of refusal lifted before `name` translates: its own, and those of the refused functions it
    waits on, through calls and cycles."""
    seen, kinds, todo = set(), set(), [name]
    while todo:
        f = todo.pop()
        if f in seen or f not in blocked:
            continue
        seen.add(f)
        kinds |= blocked[f][0]
        todo.extend(blocked[f][1])
    return sorted(kinds)


def lifting(blocked: Blocked) -> tuple[dict[str, int], dict[str, int]]:
    """For a module: how many refused functions have each kind of refusal, among any of their reasons, and
    how many lifting each kind alone would translate."""
    having: Counter[str] = Counter(k for own, _ in blocked.values() for k in own)
    alone = {k: n for k in having if (n := len(translated_with({k}, blocked)))}
    return order(having), order(alone)


def stored(blocked: Blocked) -> dict[str, dict[str, list[str]]]:
    return {f: {"own": sorted(own), "waits": sorted(deps)} for f, (own, deps) in sorted(blocked.items())}


def loaded(record: dict[str, dict[str, list[str]]]) -> Blocked:
    return closed({f: (frozenset(b["own"]), frozenset(b["waits"])) for f, b in record.items()})


def lifting_order(modules: list[Blocked], steps: int) -> list[tuple[str, int, int]]:
    """Kinds of refusal to lift one after another, each the one that then translates the most functions
    across `modules`, or, where none translates any alone, the one most still-refused functions have: with
    how many functions it adds, and how many lifting all of them so far translates."""
    lifted: set[str] = set()
    done = 0
    out = []
    for _ in range(steps):
        left: Counter[str] = Counter(
            k for m in modules for f, (own, _) in m.items() for k in own - lifted if k != UNSURVEYED
        )
        if not left:
            break
        gains = {k: sum(len(translated_with(lifted | {k}, m)) for m in modules) for k in left}
        best = max(left, key=lambda k: (gains[k], left[k], k))
        lifted.add(best)
        out.append((best, gains[best] - done, gains[best]))
        done = gains[best]
    return out


def order(counts: dict[str, int]) -> dict[str, int]:
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


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
        surveyed = report(ll)
        if set(surveyed) != set(bodies):
            raise RuntimeError(
                f"{name}: {unit['source']}: ir-lean reported on other functions than the IR has"
            )
        verdicts = {f: v["first"] for f, v in surveyed.items()}
        refused = [reason(v, known) for v in verdicts.values() if v != "ok"]
        blocked = blockers(surveyed, known)
        having, alone = lifting(blocked)
        record["variants"][variant] = {
            "functions": len(bodies),
            "translated": len(bodies) - len(refused),
            "refused": order(Counter(refused)),
            "having": having,
            "alone": alone,
            "blocked": stored(blocked),
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
            kr.setdefault("needs", {})[variant] = needs(k, blocked)
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
        added: dict[str, Counter[str]] = {key: Counter() for key in ("refused", "having", "alone")}
        for u in units:
            for key, counts in added.items():
                counts.update(u["variants"][variant][key])
        out[variant] = {
            "functions": sum(u["variants"][variant]["functions"] for u in units),
            "translated": sum(u["variants"][variant]["translated"] for u in units),
            **{key: order(counts) for key, counts in added.items()},
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


def kept(old: dict[str, Any] | None, keep: list[str]) -> dict[str, Any]:
    """The projects of an earlier record that a run of other projects keeps, each with what it was measured
    with: its own `measured`, or else, in a record from before projects had one, the record's date, commit and
    clang."""
    if old is None:
        return {}
    top = {k: old.get(k, "") for k in ("date", "commit", "clang")}
    return {n: {"measured": top, **old["projects"][n]} for n in keep if n in old["projects"]}


def run(args: argparse.Namespace) -> int:
    manifest = kernels.load()
    if found := kernels.validate(manifest):
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
    head = proc.run(["git", "-C", ROOT, "rev-parse", "HEAD"], timeout=60).out.strip()
    # What each project's counts were measured with, kept with them: a run of some projects keeps the others'
    # counts, and they keep the date, commit and clang they were measured with, not this run's.
    measured = {
        "date": proc.now()[:10],
        "commit": head,
        "clang": clang.version.splitlines()[0] if clang.version else "",
    }
    old = schemas.read(args.out, schemas.KERNELS_DEMAND) if args.project and args.out.exists() else None
    projects = kept(old, [n for n in with_units if n not in names])
    for name in names:
        result = measure(name, manifest, args.work, args.jobs)
        result["totals"] = totals(result["units"], known)
        result["measured"] = measured
        projects[name] = result
        t = result["totals"]
        print(
            f"ok   {name}: {t['units']} units, {t['as-built']['translated']}/{t['as-built']['functions']} "
            f"functions translate as built, {t['relaxed']['translated']}/"
            f"{t['relaxed']['functions']} relaxed",
            flush=True,
        )
    record = {
        "schema": schemas.KERNELS_DEMAND,
        "generated_by": "bench/kernels/demand.py run",
        # The run that wrote this file. Each project's own `measured` says when its counts were measured.
        **measured,
        "opt": manifest["corpus"]["opt"],
        "variants": {"as-built": [], "relaxed": RELAX},
        "projects": {n: projects[n] for n in sorted(projects)},
    }
    schemas.write(args.out, record, schemas.KERNELS_DEMAND, indent=1)
    print(f"wrote {args.out}")
    return 0


def check(args: argparse.Namespace) -> int:
    """Every unit compiles at the pin and defines the kernels the manifest names, and every file of the
    project's own tests that a workload's known-answers check names is in its source."""
    manifest = kernels.load()
    if found := kernels.validate(manifest):
        print("\n".join(f"FAIL {line}" for line in found))
        return 1
    if not EMITTER.exists() or pinned_clang() is None:
        print("skip: this needs build/ir-lean and the pinned clang")
        return SKIP
    missing, failed = [], False
    for name, project in sorted(manifest["project"].items()):
        if not project.get("unit"):
            continue
        result = measure(name, manifest, args.work, args.jobs, args.offline)
        if result.get("missing"):
            missing.append(name)
            continue
        named = sum(len(u["kernels"]) for u in result["units"])
        print(f"ok   {name}: {len(result['units'])} units compile, and define the {named} kernels named")
        src = kernels.source(name, project, args.offline)
        tests = [
            t for w in project.get("workload", []) for c in w.get("check", []) for t in c.get("test", [])
        ]
        if absent := [t for t in tests if src is None or not (src / t).is_file()]:
            print(f"FAIL {name}: its checks name tests that aren't at the pin: {', '.join(absent)}")
            failed = True
        elif tests:
            print(f"ok   {name}: the {len(tests)} files of its own tests that its checks name are at the pin")
    if failed:
        return 1
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
    print(
        "| A kind of refusal, in the projects that aren't rejected | Functions with it, relaxed | "
        "Lifting it alone translates, relaxed | Functions with it, as built | Lifting it alone, as built |"
    )
    print("| --- | ---: | ---: | ---: | ---: |")
    having: dict[str, Counter[str]] = {v: Counter() for v in VARIANTS}
    alone: dict[str, Counter[str]] = {v: Counter() for v in VARIANTS}
    for p in live.values():
        for v in VARIANTS:
            having[v].update(p["totals"][v]["having"])
            alone[v].update(p["totals"][v]["alone"])
    kinds = set(having["relaxed"]) | set(having["as-built"])
    for r in sorted(
        kinds, key=lambda k: (-alone["relaxed"][k], -alone["as-built"][k], -having["relaxed"][k], k)
    ):
        print(
            f"| {r} | {having['relaxed'][r]} | {alone['relaxed'][r]} | {having['as-built'][r]} | "
            f"{alone['as-built'][r]} |"
        )
    for v in VARIANTS:
        modules = [loaded(u["variants"][v]["blocked"]) for p in live.values() for u in p["units"]]
        print()
        print(
            f"| Lifted next, {v}, the most it then translates first | Functions it adds | Translated in all |"
        )
        print("| --- | ---: | ---: |")
        for kind, added, total in lifting_order(modules, 15):
            print(f"| {kind} | {added} | {total} |")
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
    print(
        "| Project | Kernel | Instructions | As built | Relaxed | Relaxed, everything it needs | "
        "Intrinsics it calls |"
    )
    print("| --- | --- | ---: | --- | --- | --- | --- |")
    for name, p in record["projects"].items():
        if manifest["project"].get(name, {}).get("status") == "rejected":
            continue
        for u in p["units"]:
            for k, kr in u["kernels"].items():
                called = ", ".join(f"`{i.removeprefix('llvm.')}` {n}" for i, n in kr["intrinsics"].items())
                need = "; ".join(kr["needs"]["relaxed"]) or "Nothing"
                print(
                    f"| {name} | `{k}` | {kr['instructions']:,} | {kr['as-built']} | "
                    f"{kr['relaxed']} | {need} | {called or 'None'} |"
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
