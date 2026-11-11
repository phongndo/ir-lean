#!/usr/bin/env python3
"""Ranks x86's integer intrinsics by how often `clang -O3` leaves a call to one in real kernels, for
decision 7 of 2026-11-09: which intrinsics the model needs first. docs/x86-intrinsics.md has the result.

Clang's headers lower many `_mm*` functions to generic IR, so only those that reach IR as `llvm.x86.*` calls
need a model of their own. This counts them, and nothing else: it runs no rewrite on the IR, and keeps none of
it outside build/.

  count  Fetches each project in PROJECTS through nix, at the release the flake's nixpkgs pins, asks its own
         build system which command compiles each file, runs each again with the pinned clang at -O3, to IR,
         and counts the calls to each intrinsic. Writes tests/x86_rank/ranking.json.
  table  Prints docs/x86-intrinsics.md's tables, from ranking.json and the classification of the pin's
         intrinsics, tests/llvm_scope/ir-features.json. `--write` puts them in the document.
  check  Without the network or a compiler: ranking.json is of this pin, every intrinsic it counts is one the
         classification has, and docs/x86-intrinsics.md holds exactly what `table` prints, so a change to what
         the model has, or to the ranking, has to change the document.

usage: tools/x86_rank.py count [--jobs N] [--only PROJECT ...] [--probe build/ir-lean-probe]
       tools/x86_rank.py table [--write]
       tools/x86_rank.py check
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shlex
import shutil
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc, schemas  # noqa: E402

SCHEMA = schemas.X86_RANK
FILE = ROOT / "tests" / "x86_rank" / "ranking.json"
FEATURES = ROOT / "tests" / "llvm_scope" / "ir-features.json"
DOC = ROOT / "docs" / "x86-intrinsics.md"
WORK = ROOT / "build" / "x86-rank"
# How many of the other refused intrinsics the files call the table lists, most calls first.
OTHERS = 30
# The lines of the document `table` prints lie between these.
BEGIN, END = "<!-- x86_rank table: begin -->", "<!-- x86_rank table: end -->"


@dataclass
class Project:
    name: str
    domain: str
    # The attribute of the flake's nixpkgs whose `src` is the release, or "" for llama.cpp, which the flake
    # pins itself, in nix/llama.nix.
    attr: str
    # Where its CMakeLists.txt is, or None for one built with configure and make.
    cmake: str | None = ""
    options: list[str] = field(default_factory=list)
    # A file counts only if its path matches.
    only: str = ""
    # Programs its configure step needs that the dev shell lacks, from the same nixpkgs.
    needs: list[str] = field(default_factory=list)


PROJECTS = [
    Project(
        "llama.cpp",
        "inference",
        "",
        options=[
            "-DGGML_NATIVE=OFF",
            # What tests/llama.py compiles its kernels with.
            "-DCMAKE_C_FLAGS=-march=znver5",
            "-DCMAKE_CXX_FLAGS=-march=znver5",
            "-DLLAMA_CURL=OFF",
            "-DLLAMA_BUILD_TESTS=OFF",
            "-DLLAMA_BUILD_EXAMPLES=OFF",
            "-DLLAMA_BUILD_TOOLS=OFF",
            "-DLLAMA_BUILD_SERVER=OFF",
        ],
        only=r"/ggml/src/ggml-cpu/",
    ),
    Project(
        "ncnn",
        "inference",
        "ncnn",
        options=[
            "-DNCNN_VULKAN=OFF",
            "-DNCNN_OPENMP=OFF",
            "-DNCNN_BUILD_TOOLS=OFF",
            "-DNCNN_BUILD_EXAMPLES=OFF",
            "-DNCNN_BUILD_BENCHMARK=OFF",
            "-DNCNN_BUILD_TESTS=OFF",
        ],
        only=r"/src/",
    ),
    Project(
        "zlib-ng",
        "compression",
        "zlib-ng",
        options=["-DZLIB_ENABLE_TESTS=OFF", "-DZLIBNG_ENABLE_TESTS=OFF", "-DWITH_GTEST=OFF"],
    ),
    Project("libdeflate", "compression", "libdeflate", options=["-DLIBDEFLATE_BUILD_GZIP=OFF"]),
    Project(
        "zstd",
        "compression",
        "zstd",
        cmake="build/cmake",
        options=["-DZSTD_BUILD_PROGRAMS=OFF", "-DZSTD_BUILD_TESTS=OFF"],
    ),
    Project("libwebp", "codecs", "libwebp", only=r"/src/|/sharpyuv/"),
    Project(
        "libaom",
        "codecs",
        "libaom",
        options=["-DENABLE_TESTS=OFF", "-DENABLE_EXAMPLES=OFF", "-DENABLE_TOOLS=OFF", "-DENABLE_DOCS=OFF"],
        needs=["nasm", "perl"],
    ),
    Project(
        "xxHash",
        "hashing",
        "xxHash",
        cmake="cmake_unofficial",
        # Its dispatcher compiles XXH3's SSE2, AVX2 and AVX-512 loops into one file.
        options=["-DDISPATCH=ON", "-DXXHASH_BUILD_XXHSUM=OFF"],
    ),
    # Its build defaults to hand-written assembly, which never reaches IR. This is its C with intrinsics.
    Project("BLAKE3", "hashing", "libblake3", cmake="c", options=["-DBLAKE3_SIMD_TYPE=x86-intrinsics"]),
    Project("libsodium", "crypto", "libsodium", cmake=None),
]

# What comes before an instruction's name in `llvm.x86.ISA.NAME.WIDTH`.
ISAS = "sse sse2 sse3 ssse3 sse41 sse42 sse4a avx avx2 avx512 avx10 aesni bmi tbm xop".split()
# Intrinsics of one instruction that LLVM names differently at different widths.
ALIASES = {
    "PERMVARSI": "VPERMD",
    "PERMD": "VPERMD",
    "PERMVARDI": "VPERMQ",
    "PERMVARHI": "VPERMW",
    "PERMVARQI": "VPERMB",
    "CRC32328": "CRC32 of 8 bits",
    "CRC323216": "CRC32 of 16 bits",
    "CRC323232": "CRC32 of 32 bits",
    "CRC326464": "CRC32 of 64 bits",
}
FLOAT = re.compile(r"\b(float|double|half|bfloat|x86_fp80|fp128)\b")
CALL = re.compile(r"\b(?:call|invoke)\b([^@]*)@(llvm\.[\w.]+)\((.*)")
DEFINE = re.compile(r'^define\b.*?@("[^"]+"|[\w.$-]+)\(')


def family(name: str) -> str:
    """What an x86 intrinsic is a form of: its name without the instruction set and the width, so
    `llvm.x86.avx2.psrai.d` is PSRAID, PSRAD by an immediate count. A form on MMX's registers stays apart: the
    `mmx` ones, and SSSE3's with no width."""
    parts = name.removeprefix("llvm.x86.").split(".")
    mmx = parts[0] == "mmx" or (parts[0] == "ssse3" and parts[-1] != "128") or parts[:2] == ["sse", "pshuf"]
    if parts[0] in ISAS or mmx:
        parts = parts[1:]
    while parts and parts[-1] in ("128", "256", "512"):
        parts.pop()
    joined = "".join(parts).upper()
    return ("MMX " if mmx else "") + ALIASES.get(joined, joined)


def kind_of(result: str, operands: str) -> str:
    """What a call computes on, from its own types: floating point, memory, or integers only."""
    text = result + " " + operands
    if FLOAT.search(text):
        return "float"
    if re.search(r"\b(ptr|x86_amx|token|metadata)\b", text) or result.strip().startswith("void"):
        return "other"
    return "integer"


def count_calls(ir: str) -> dict[tuple[str, str], dict[str, int]]:
    """Each intrinsic a module calls, with the kind of its operands, as {(name, kind): {function: calls}}.
    Declarations don't count."""
    found: dict[tuple[str, str], dict[str, int]] = {}
    function = ""
    for line in ir.splitlines():
        if m := DEFINE.match(line):
            function = m[1]
        elif line.startswith("}"):
            function = ""
        elif function and (m := CALL.search(line)):
            # `tail call fastcc <8 x i32> @llvm...`: what's left of the types before the callee is the result.
            per = found.setdefault((m[2], kind_of(m[1].split("call")[-1], m[3])), {})
            per[function] = per.get(function, 0) + 1
    return found


def sh(argv: list[str], **kw: Any) -> proc.Ran:
    r = proc.run(argv, **kw)
    if not r.ok:
        sys.exit(f"{' '.join(map(str, argv))[:300]} failed:\n{r.output[-3000:]}")
    return r


def nix_shell(needs: list[str], argv: list[str]) -> list[str]:
    """`argv`, with programs the dev shell lacks from the flake's nixpkgs."""
    if not needs:
        return argv
    packages = [f"nixpkgs#{n}" for n in needs]
    return ["nix", "shell", "--inputs-from", str(ROOT), *packages, "-c", *argv]


def source(p: Project) -> tuple[Path, str]:
    """A project's source in the nix store, and its version."""
    if not p.attr:
        expr = f'(builtins.getFlake "{ROOT}").devShells.${{builtins.currentSystem}}.llama.LLAMA_CPP_SRC'
        out = sh(["nix", "build", "--impure", "--no-link", "--print-out-paths", "--expr", expr]).out
        rev = re.search(r'rev = "([^"]+)"', (ROOT / "nix" / "llama.nix").read_text())
        assert rev
        return Path(out.split()[-1]), rev[1]
    flake = ["--inputs-from", str(ROOT), f"nixpkgs#{p.attr}"]
    out = sh(["nix", "build", f"{flake[-1]}.src", *flake[:2], "--no-link", "--print-out-paths"]).out
    version = sh(["nix", "eval", "--raw", f"{flake[-1]}.version", *flake[:2]]).out
    return Path(out.split()[-1]), version.strip()


def commands(p: Project, src: Path, build: Path) -> list[tuple[str, list[str], str]]:
    """Each file the project's build compiles, as (directory, command, file)."""
    if p.cmake is not None:
        configure = [
            *["cmake", "-S", str(src / p.cmake), "-B", str(build), "-G", "Ninja"],
            *["-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON"],
            *["-DCMAKE_C_COMPILER=clang", "-DCMAKE_CXX_COMPILER=clang++", *p.options],
        ]
        sh(nix_shell(p.needs, configure), timeout=1800)
        entries = json.loads((build / "compile_commands.json").read_text())
        # Sources and headers the build writes itself, such as ncnn's copy of each layer for each instruction
        # set: every file of those kinds ninja has a rule for.
        targets = sh(nix_shell(p.needs, ["ninja", "-C", str(build), "-t", "targets", "all"])).out
        made = [
            line.split(": ")[0]
            for line in targets.splitlines()
            if line.split(": ")[0].endswith((".c", ".cc", ".cpp", ".h", ".hpp", ".inc"))
        ]
        if made:
            sh(nix_shell(p.needs, ["ninja", "-C", str(build), *made]), timeout=1800)
        return [(e["directory"], e.get("arguments") or shlex.split(e["command"]), e["file"]) for e in entries]
    # configure and make, with a compiler that writes down each command before it runs it.
    log, wrapper = build / "commands.log", build / "cc"
    wrapper.write_text(
        f'#!/bin/sh\n{{ printf \'%s\\t\' "$PWD" "$@"; echo; }} >> {shlex.quote(str(log))}\nexec clang "$@"\n'
    )
    wrapper.chmod(0o755)
    sh([str(src / "configure"), f"CC={wrapper}", "--disable-dependency-tracking"], cwd=build, timeout=1800)
    log.unlink(missing_ok=True)
    sh(["make", "-j8"], cwd=build, timeout=1800)
    out = []
    for line in log.read_text().splitlines():
        cwd, *argv = line.rstrip("\t").split("\t")
        files = [a for a in argv if a.endswith((".c", ".cc", ".cpp"))]
        if "-c" in argv and len(files) == 1:
            out.append((cwd, ["clang", *argv], str((Path(cwd) / files[0]).resolve())))
    return out


def to_ir(directory: str, argv: list[str], out: Path) -> bool:
    """Runs a compile command again, with the pinned clang at -O3, writing IR."""
    kept, skip = ["clang++" if "++" in Path(argv[0]).name else "clang"], False
    for a in argv[1:]:
        if skip:
            skip = False
        elif a in ("-o", "-MF", "-MT", "-MQ"):
            skip = True
        elif a not in ("-c", "-MD", "-MMD", "-MP") and not a.startswith(("-flto", "-Werror")):
            kept.append(a)
    r = proc.run([*kept, "-O3", "-w", "-S", "-emit-llvm", "-o", str(out)], cwd=directory, timeout=1800)
    return r.ok


def count_project(p: Project, jobs: int) -> dict[str, Any]:
    src, version = source(p)
    build = WORK / p.name
    shutil.rmtree(build, ignore_errors=True)
    (build / "ir").mkdir(parents=True)
    todo = [
        (d, argv, f)
        for d, argv, f in commands(p, src, build)
        if f.endswith((".c", ".cc", ".cpp")) and re.search(p.only, f)
    ]

    def one(job: tuple[int, tuple[str, list[str], str]]) -> dict[tuple[str, str], dict[str, int]] | None:
        n, (directory, argv, _) = job
        out = build / "ir" / f"{n}.ll"
        if not to_ir(directory, argv, out):
            return None
        counts = count_calls(out.read_text(errors="replace"))
        out.unlink()
        return {k: {f"{n}:{fn}": c for fn, c in v.items()} for k, v in counts.items()}

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        results = list(pool.map(one, enumerate(todo)))
    failed = sorted(os.path.relpath(f, src) for (_, _, f), r in zip(todo, results, strict=True) if r is None)
    calls: dict[str, dict[str, int]] = {}
    for r in results:
        for (name, kind), per in (r or {}).items():
            row = calls.setdefault(f"{name}|{kind}", {"calls": 0, "functions": 0})
            row["calls"] += sum(per.values())
            row["functions"] += len(per)
    print(f"{p.name} {version}: {len(todo)} files, {len(failed)} not compiled, {len(calls)} intrinsics")
    return {
        "name": p.name,
        "domain": p.domain,
        "version": version,
        "source": str(src),
        "files": len(todo),
        "not_compiled": failed,
        "calls": dict(sorted(calls.items())),
    }


def features() -> dict[str, Any]:
    return schemas.check(json.loads(FEATURES.read_text()), schemas.IR_FEATURES)


def classes(doc: dict[str, Any]) -> dict[str, str]:
    """The class of each intrinsic at the pin."""
    return {i["name"]: i["class"] for i in doc["items"] if i["kind"] == "intrinsic"}


def base(name: str, known: dict[str, str]) -> str | None:
    """An overloaded intrinsic's name without the types a call adds to it."""
    while name and name not in known:
        name = name.rpartition(".")[0]
    return name or None


def integer_intrinsics(probe: Path) -> list[str]:
    """The pin's x86 intrinsics that compute on integers only and touch nothing else: every type in a call the
    probe builds is an integer or a vector of them, and LLVM marks the intrinsic `memory(none)`."""
    text = sh([str(probe)]).out
    known = classes(features())
    groups = dict(re.findall(r"^attributes #(\d+) = \{(.*)\}$", text, flags=re.M))
    found = set()
    for m in re.finditer(r"^declare (.*?) @(llvm\.x86\.[\w.]+)\((.*?)\)(?: #(\d+))?$", text, flags=re.M):
        pure = "memory(none)" in groups.get(m[4], "")
        if pure and kind_of(m[1], m[3]) == "integer" and (name := base(m[2], known)):
            found.add(name)
    return sorted(found)


def cmd_count(args: argparse.Namespace) -> int:
    doc = features()
    old = json.loads(FILE.read_text()) if FILE.exists() else {"projects": []}
    done = {p["name"]: p for p in old["projects"]}
    for p in PROJECTS:
        if not args.only or p.name in args.only:
            done[p.name] = count_project(p, args.jobs)
    lock = json.loads((ROOT / "flake.lock").read_text())["nodes"]["nixpkgs"]["locked"]
    record = {
        "schema": SCHEMA,
        "generated_by": "tools/x86_rank.py count",
        "pin": doc["pin"],
        "clang": sh(["clang", "--version"]).out.splitlines()[0],
        "nixpkgs": lock["rev"],
        "integer": integer_intrinsics(Path(args.probe)),
        "projects": [done[p.name] for p in PROJECTS if p.name in done],
    }
    FILE.parent.mkdir(exist_ok=True)
    FILE.write_text(json.dumps(record, indent=1) + "\n")
    return 0


def integer_calls(p: dict[str, Any]) -> int:
    return sum(
        n["calls"] for k, n in p["calls"].items() if k.startswith("llvm.x86.") and k.endswith("|integer")
    )


def ranking(record: dict[str, Any], known: dict[str, str]) -> list[dict[str, Any]]:
    """Each family with an integer form, most needed first: its forms at the pin, how many are modeled, its
    integer calls in each project, and its share. A project's share of a family is the family's part of that
    project's integer x86 calls, and a family's share is the mean of that over the projects with any, so that
    a large project counts once."""
    rows: dict[str, dict[str, Any]] = {}
    for name in record["integer"]:
        row = rows.setdefault(family(name), {"forms": [], "calls": {}, "functions": 0, "share": 0.0})
        row["forms"].append(name)
    with_calls = [p for p in record["projects"] if integer_calls(p)]
    for p in with_calls:
        for key, n in p["calls"].items():
            name, kind = key.split("|")
            name = base(name, known) or name
            row = rows.get(family(name)) if name.startswith("llvm.x86.") else None
            if row and kind == "integer" and name in row["forms"]:
                row["calls"][p["name"]] = row["calls"].get(p["name"], 0) + n["calls"]
                row["functions"] += n["functions"]
                row["share"] += n["calls"] / integer_calls(p) / len(with_calls)
    out = []
    for fam, row in rows.items():
        modeled = sum(known[f] == "modeled" for f in row["forms"])
        out.append({"family": fam, "modeled": modeled, "total": sum(row["calls"].values()), **row})
    return sorted(out, key=lambda r: (-r["share"], -r["total"], r["family"]))


def table(record: dict[str, Any], doc: dict[str, Any]) -> str:
    known = classes(doc)
    rows = ranking(record, known)
    names = [p["name"] for p in record["projects"]]
    lines = [
        "| Project | Domain | Release | Files compiled | Not compiled | Integer `llvm.x86.*` calls |",
        "| --- | --- | --- | ---: | ---: | ---: |",
    ]
    for p in record["projects"]:
        lines.append(
            f"| {p['name']} | {p['domain']} | {p['version']} | {p['files']:,} | {len(p['not_compiled'])} | "
            f"{integer_calls(p):,} |"
        )
    used = [r for r in rows if r["total"]]
    total = sum(r["total"] for r in used)
    done = [r for r in used if r["modeled"] == len(r["forms"])]
    forms = [f for r in rows for f in r["forms"]]
    covered = sum(r["total"] for r in done)
    lines += [
        "",
        f"{len(forms)} integer intrinsics at the pin, forms of {len(rows)} families, "
        f"{sum(known[f] == 'modeled' for f in forms)} of them modeled. {len(used)} families have a call in "
        f"these projects, {total:,} calls in all. The {len(done)} of those families modeled at every form "
        f"have {covered:,} of the calls, {100 * covered / max(total, 1):.1f}%, "
        f"and {100 * sum(r['share'] for r in done):.1f}% by share.",
        "",
        "| Rank | Family | Share | Calls | Projects | Functions | Forms modeled | "
        + " | ".join(names)
        + " |",
        "| ---: | --- | ---: | ---: | ---: | ---: | --- | " + " | ".join("---:" for _ in names) + " |",
    ]
    for n, r in enumerate(used, 1):
        per = " | ".join(f"{r['calls'][name]:,}" if r["calls"].get(name) else "" for name in names)
        lines.append(
            f"| {n} | {r['family']} | {100 * r['share']:.2f}% | {r['total']:,} | {len(r['calls'])} | "
            f"{r['functions']:,} | {r['modeled']} of {len(r['forms'])} | {per} |"
        )
    unused = sorted((r for r in rows if not r["total"]), key=lambda r: r["family"])
    mmx = [r for r in unused if r["family"].startswith("MMX ")]
    lines += [
        "",
        f"No call in these projects: {len(unused)} families. {len(mmx)} are forms on MMX's registers, none "
        f"of them modeled. The other {len(unused) - len(mmx)}, with the forms modeled of each: "
        + ", ".join(f"{r['family']} ({r['modeled']} of {len(r['forms'])})" for r in unused if r not in mmx)
        + ".",
    ]
    # What else the same files call that the emitter refuses.
    other: dict[str, dict[str, int]] = {}
    for p in record["projects"]:
        for key, n in p["calls"].items():
            name, kind = key.split("|")
            name = base(name, known) or name
            if known.get(name) == "refused" and not (name.startswith("llvm.x86.") and kind == "integer"):
                per = other.setdefault(name, {})
                per[p["name"]] = per.get(p["name"], 0) + n["calls"]
    lines += [
        "",
        "| Other refused intrinsic these files call | Calls | Projects |",
        "| --- | ---: | ---: |",
    ]
    for name, per in sorted(other.items(), key=lambda kv: (-sum(kv[1].values()), kv[0]))[:OTHERS]:
        lines.append(f"| `{name}` | {sum(per.values()):,} | {len(per)} |")
    return "\n".join(lines) + "\n"


def load() -> tuple[dict[str, Any], dict[str, Any]]:
    return schemas.check(json.loads(FILE.read_text()), SCHEMA), features()


def cmd_table(args: argparse.Namespace) -> int:
    text = table(*load())
    if args.write:
        before, rest = DOC.read_text().split(BEGIN)
        DOC.write_text(before + BEGIN + "\n" + text + END + rest.split(END)[1])
    else:
        print(text, end="")
    return 0


def problems(record: dict[str, Any], doc: dict[str, Any], text: str) -> list[str]:
    """What's wrong with a ranking, or with the document that holds it."""
    known = classes(doc)
    wrong = []
    if record["pin"] != doc["pin"]:
        wrong.append(f"the ranking is of {record['pin']}, and the classification of {doc['pin']}")
    wrong += [f"{n} isn't an intrinsic at the pin" for n in record["integer"] if n not in known]
    for p in record["projects"]:
        for key in p["calls"]:
            if base(key.split("|")[0], known) is None:
                wrong.append(f"{p['name']} calls {key}, which isn't an intrinsic at the pin")
    if BEGIN not in text or END not in text:
        wrong.append(f"{DOC.name} has no table between its markers")
    elif wrong:
        # A table of a ranking that's wrong in itself says nothing.
        pass
    elif text.split(BEGIN)[1].split(END)[0].strip() != table(record, doc).strip():
        wrong.append(f"{DOC.name}'s table isn't what `tools/x86_rank.py table` prints")
    return wrong


def cmd_check(_: argparse.Namespace) -> int:
    record, doc = load()
    wrong = problems(record, doc, DOC.read_text())
    for w in wrong:
        print(f"FAIL  {w}")
    if not wrong:
        rows = ranking(record, classes(doc))
        print(f"ok  {len(record['projects'])} projects, {sum(1 for r in rows if r['total'])} instructions")
    return 1 if wrong else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=(__doc__ or "").split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    count = sub.add_parser("count")
    count.add_argument("--jobs", type=int, default=8)
    count.add_argument("--only", nargs="*", default=[])
    count.add_argument("--probe", default=str(ROOT / "build" / "ir-lean-probe"))
    count.set_defaults(run=cmd_count)
    tables = sub.add_parser("table")
    tables.add_argument(
        "--write", action="store_true", help="into docs/x86-intrinsics.md, between its markers"
    )
    tables.set_defaults(run=cmd_table)
    sub.add_parser("check").set_defaults(run=cmd_check)
    args = parser.parse_args()
    return args.run(args)


if __name__ == "__main__":
    sys.exit(main())
