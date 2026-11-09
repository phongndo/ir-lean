#!/usr/bin/env python3
"""BIND-02: every function and file a unit of LLVM's code can reach, from the pinned build's call graph.

`derive` compiles the pinned llvm-project's files with tests/llvm/targets.toml's flags for LLVM, the ones
tests/llvm.py and prototypes/binding/census.sh use: every .cpp in the directories `--index` names, so a
function called from one file can be found where it's defined. Then from the root symbol it follows each
direct call, to the copy in the same file for an inline function or template (`linkonce_odr`), or to the one
file that defines it otherwise, and each indirect call to every function whose address the reached files take,
which bounds it, until nothing new is reached. A call to a function no indexed file defines is `unresolved`,
and the closure is complete only if there is none and every indirect call is bounded.

The closure records every function, with its file, linkage, instruction count and the SHA-256 of its IR, and
every file of llvm-project the reached files read, headers included, with its SHA-256, which are its anchors.
`check` hashes the files again and fails if any changed, and with `--rebuild` compiles the reached files again
and fails if any function's IR, or what it calls, changed. `link` puts the closure in one module, as ir-lean
would have to take it, and reports what ir-lean translates of it.

usage: tests/llvm_scope/closure/closure.py derive --name NAME --root SYMBOL --file PATH [--index DIR ...]
           [--jobs N] [--cache DIR]
       tests/llvm_scope/closure/closure.py check NAME [--rebuild] [--jobs N] [--cache DIR]
       tests/llvm_scope/closure/closure.py link NAME OUT.ll [--cache DIR]

Needs `nix develop`. Compiling the index is a heavy run: see docs/llvm-closure.md.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tomllib
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, pins, proc  # noqa: E402

SCHEMA = "ir-lean.closure/1"
# Changes when what `parse` reads of a module does, so cached readings are redone.
PARSER = 3
TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
INDEX = [
    "llvm/lib/IR",
    "llvm/lib/Analysis",
    "llvm/lib/Support",
    "llvm/lib/TargetParser",
    "llvm/lib/BinaryFormat",
    "llvm/lib/Demangle",
]
DEFINE = re.compile(r"^define\s+(.*?)@(\"[^\"]+\"|[-\w.$]+)\(", re.M)
DECLARE = re.compile(r"^declare\s+.*?@(\"[^\"]+\"|[-\w.$]+)\(", re.M)
CALL = re.compile(r"\b(?:call|invoke)\b(.*)")
CALLEE = re.compile(r"([@%](?:\"[^\"]+\"|[-\w.$]+))\(")
ALIAS = re.compile(r"^@(\"[^\"]+\"|[-\w.$]+) = .*\balias\b.*, ptr @(\"[^\"]+\"|[-\w.$]+)\s*$", re.M)
TYPE = re.compile(r"^(void|i\d+|ptr|half|bfloat|float|double|x86_fp80|fp128|\{.*\}|<.*>|\[.*\])$")
REF = re.compile(r"@(\"[^\"]+\"|[-\w.$]+)")
LINKAGES = ("private", "internal", "linkonce_odr", "linkonce", "weak_odr", "weak", "available_externally",
            "extern_weak", "external")  # fmt: skip
# What the C and C++ runtimes give, which no file of llvm-project defines.
RUNTIME = re.compile(
    r"^(_Znw|_Zna|_Zdl|_Zda|__cxa_|_ZSt|_ZNSt|_ZNKSt|__gxx_|mem(cpy|move|set|cmp|chr)$|str\w+$|malloc$|calloc$|"
    r"realloc$|free$|abort$|__assert|_Unwind|pthread_|write$|read$|open$|close$|getenv$|"
    r"__errno_location$|fwrite$|fflush$|fputc$|__stack_chk_fail$|"
    r"qsort$|exit$|_exit$|raise$|sigaction$|sigemptyset$|__libc|__isoc|stderr$|stdout$)"
)


def flags() -> dict[str, Any]:
    f = tomllib.loads(TARGETS.read_text())["flags"]["llvm"]
    return {"args": f["args"], "include": f["include"], "local_include": f["local_include"]}


def src() -> Path:
    s = os.environ.get("LLVM_PROJECT_SRC")
    if not s:
        sys.exit("LLVM_PROJECT_SRC isn't set: run inside nix develop")
    return Path(s)


def includedir() -> str:
    r = proc.run(["llvm-config", "--includedir"], timeout=60)
    return r.stdout.decode().strip()


# Include directories upstream's CMake adds for one directory: llvm/lib/Support/CMakeLists.txt adds libc's,
# for APFloat's shared math.
DIRECTORY_INCLUDES = {"llvm/lib/Support": ["libc"]}


def compile_argv(path: str, out: Path, deps: Path, inc: str) -> list[str]:
    f = flags()
    cflags = ["-idirafter" if x == "-isystem" else x for x in os.environ.get("PROOF_CFLAGS", "").split()]
    extra = DIRECTORY_INCLUDES.get(str(Path(path).parent), [])
    argv = ["clang", *cflags, *f["args"], *[f"-I{i}" for i in f["include"] + extra], f"-I{Path(path).parent}"]
    argv += [f"-I{ROOT / i}" for i in f["local_include"]] + [f"-I{inc}"]
    return [
        *argv,
        "-S",
        "-emit-llvm",
        "-fno-discard-value-names",
        "-MD",
        "-MF",
        str(deps),
        "-o",
        str(out),
        path,
    ]


def cached(cache: Path, path: str) -> tuple[Path, Path]:
    base = cache / "ir" / path
    return base.with_suffix(".ll"), base.with_suffix(".d")


def compile_one(path: str, cache: Path, inc: str, force: bool = False) -> str | None:
    """Compiles one file of llvm-project to IR in the cache, from llvm-project's root, so the IR names no
    machine's path. Returns why it failed, or None."""
    ll, d = cached(cache, path)
    stamp = ll.with_suffix(".argv")
    argv = compile_argv(path, ll, d, inc)
    key = hashing.sha256_text(json.dumps(argv))
    if not force and ll.is_file() and stamp.is_file() and stamp.read_text() == key:
        return None
    ll.parent.mkdir(parents=True, exist_ok=True)
    r = proc.run(argv, cwd=src(), timeout=900)
    if r.exit != 0 or r.limit:
        return f"{path}: {r.limit or r.exit}: {r.stderr.decode(errors='replace')[-500:]}"
    stamp.write_text(key)
    return None


def dependencies(d: Path) -> list[Path]:
    text = d.read_text().replace("\\\n", " ")
    body = text.split(":", 1)[1] if ":" in text else ""
    out, word, chars = [], "", iter(body)
    for ch in chars:
        if ch == "\\":
            word += next(chars, "")
        elif ch.isspace():
            if word:
                out.append(word)
            word = ""
        else:
            word += ch
    if word:
        out.append(word)
    return [(src() / w).resolve() for w in out]


def unquote(s: str) -> str:
    return s[1:-1] if s.startswith('"') else s


def split_top(text: str) -> list[str]:
    """`text` split at its commas outside brackets and quotes."""
    parts, depth, cur, quoted = [], 0, "", False
    for ch in text:
        if ch == '"':
            quoted = not quoted
        if not quoted and ch in "([{<":
            depth += 1
        elif not quoted and ch in ")]}>":
            depth -= 1
        if ch == "," and depth == 0 and not quoted:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def first_type(arg: str) -> str:
    """The type an argument or parameter starts with."""
    if arg[:1] in "{<[":
        close = {"{": "}", "<": ">", "[": "]"}[arg[0]]
        depth = 0
        for i, ch in enumerate(arg):
            depth += ch == arg[0]
            depth -= ch == close
            if depth == 0:
                return arg[: i + 1]
    return arg.split()[0] if arg.split() else ""


def signature(before: str, args: str) -> str:
    """A function type, from the text before a callee or a definition's name, and its arguments: the last type
    before the name, and each argument's type. Attributes and calling conventions aren't types."""
    words = split_top(before.replace(" ", ","))
    ret = next((w for w in reversed(words) if TYPE.match(w)), "?")
    return ret + "(" + ",".join(first_type(a) for a in split_top(args)) + ")"


def call_args(line: str, at: int) -> str:
    """The arguments of the call whose `(` is at `at`."""
    depth = 0
    for i in range(at, len(line)):
        depth += line[i] == "("
        depth -= line[i] == ")"
        if depth == 0:
            return line[at + 1 : i]
    return line[at + 1 :]


ATTRIBUTES = re.compile(r"^attributes #(\d+) = (.*)$", re.M)
METADATA = re.compile(r"^!(\d+) = (.*)$", re.M)
ATTR_REF = re.compile(r"#(\d+)\b")
MD_REF = re.compile(r"!(\d+)\b")


def expand_metadata(md: dict[str, str], ref: str, seen: frozenset[str] = frozenset()) -> str:
    """A metadata node's text with every node it refers to written out in place, so the text doesn't depend on
    how the module numbered them. A node met again inside itself, as a loop's ID is, is `!self`."""
    if ref in seen:
        return "!self"
    text = md.get(ref, "!missing")
    return MD_REF.sub(lambda m: "!{" + expand_metadata(md, m.group(1), seen | {ref}) + "}", text)


def canonical_ir(body: str, attrs: dict[str, str], md: dict[str, str]) -> str:
    """A function's IR as its hash covers it: with the attribute groups and metadata it refers to written out
    in place, so a change to either changes the hash and their numbering doesn't, and without comments, which
    carry numbers that move with unrelated code."""
    lines = []
    for raw in body.split("\n"):
        line = re.sub(r"\s*;.*$", "", raw)
        line = ATTR_REF.sub(lambda m: "#{" + attrs.get(m.group(1), "missing") + "}", line)
        lines.append(MD_REF.sub(lambda m: "!{" + expand_metadata(md, m.group(1)) + "}", line))
    return "\n".join(lines)


def parse(ll: Path) -> dict[str, Any]:
    """Each definition in a module: its linkage, IR, instruction count, the functions it calls directly, how
    many indirect calls it makes, and every function the module refers to other than by calling it."""
    text = ll.read_text(errors="replace")
    attrs = {m.group(1): m.group(2) for m in ATTRIBUTES.finditer(text)}
    md = {m.group(1): m.group(2) for m in METADATA.finditer(text)}
    defs: dict[str, Any] = {}
    referenced: set[str] = set()
    starts = list(DEFINE.finditer(text))
    for m in starts:
        end = text.index("\n}", m.end()) + 2
        body = text[m.start() : end]
        head = m.group(1).split()
        linkage = next((w for w in head if w in LINKAGES), "external")
        calls: set[str] = set()
        indirect = 0
        types: set[str] = set()
        instructions = 0
        for line in body.split("\n")[1:-1]:
            if not line.startswith("  ") or line.lstrip().startswith(";"):
                continue
            instructions += 1
            callee = None
            c = CALL.search(line)
            if c:
                k = CALLEE.search(c.group(1))
                if k:
                    callee = k.group(1)
                    if callee.startswith("%"):
                        indirect += 1
                        rest = c.group(1)
                        types.add(signature(rest[: k.start()], call_args(rest, k.end() - 1)))
                    else:
                        calls.add(unquote(callee[1:]))
            for r in REF.findall(line):
                if callee is None or "@" + r != callee:
                    referenced.add(unquote(r))
        canonical = canonical_ir(body, attrs, md)
        first = body.split("\n", 1)[0]
        defs[unquote(m.group(2))] = {
            "linkage": linkage,
            "ir_sha256": hashing.sha256_text(canonical),
            "instructions": instructions,
            "calls": sorted(calls),
            "indirect": indirect,
            "indirect_types": sorted(types),
            "type": signature(m.group(1), call_args(first, m.end() - 1 - m.start())),
        }
    # Globals that hold functions' addresses, such as vtables.
    for line in text.split("\n"):
        if line.startswith("@") and "=" in line:
            referenced.update(unquote(r) for r in REF.findall(line.split("=", 1)[1]))
    aliases = {unquote(a.group(1)): unquote(a.group(2)) for a in ALIAS.finditer(text)}
    return {"defs": defs, "declares": sorted(unquote(m.group(1)) for m in DECLARE.finditer(text)),
            "referenced": sorted(referenced), "aliases": aliases}  # fmt: skip


def load(cache: Path, path: str) -> dict[str, Any]:
    ll, _ = cached(cache, path)
    parsed = ll.with_suffix(".json")
    key = hashing.sha256_file(ll)
    if parsed.is_file():
        p = json.loads(parsed.read_text())
        if p.get("key") == key and p.get("parser") == PARSER:
            return p
    p = parse(ll) | {"key": key, "parser": PARSER}
    parsed.write_text(json.dumps(p))
    return p


def demangle(symbols: list[str]) -> dict[str, str]:
    if not symbols:
        return {}
    r = proc.run(["llvm-cxxfilt"], stdin="\n".join(symbols) + "\n", timeout=120)
    return dict(zip(symbols, r.stdout.decode().splitlines(), strict=False))


def derive(name: str, root: str, file: str, index: list[str], jobs: int, cache: Path) -> dict[str, Any]:
    s = src()
    files = sorted({file} | {str(p.relative_to(s)) for d in index for p in (s / d).glob("*.cpp")})
    inc = includedir()
    with ThreadPoolExecutor(jobs) as pool:
        failed = [f for f in pool.map(lambda p: compile_one(p, cache, inc), files) if f]
    for f in failed:
        print(f"note: not indexed, {f}", file=sys.stderr)
    failed_files = {f.split(":", 1)[0] for f in failed}
    tus = [f for f in files if f not in failed_files]
    with ThreadPoolExecutor(jobs) as pool:
        modules = dict(zip(tus, pool.map(lambda p: load(cache, p), tus), strict=True))
    if file not in modules:
        sys.exit(f"{file} didn't compile")

    # Where each function with external linkage is defined. One defined weakly in several files is the
    # one-definition rule's, and taken from the file that reaches it.
    strong: dict[str, list[str]] = defaultdict(list)
    weak: dict[str, list[str]] = defaultdict(list)
    for tu, m in modules.items():
        for sym, d in m["defs"].items():
            if d["linkage"] in ("external", "available_externally"):
                if d["linkage"] == "external":
                    strong[sym].append(tu)
            elif d["linkage"] in ("linkonce_odr", "weak_odr", "linkonce", "weak"):
                weak[sym].append(tu)

    # Aliases, such as a complete-object constructor, `C1`, for its base-object one, `C2`.
    alias_of: dict[str, str] = {}
    for m in modules.values():
        alias_of.update(m["aliases"])

    def resolve(sym: str, caller_tu: str) -> tuple[str, str] | None:
        """The node a call from `caller_tu` reaches: a file and a symbol."""
        if sym in modules[caller_tu]["aliases"] or (sym in alias_of and sym not in strong):
            sym = modules[caller_tu]["aliases"].get(sym, alias_of[sym])
        here = modules[caller_tu]["defs"].get(sym)
        if here is not None and here["linkage"] != "available_externally":
            if here["linkage"] in ("private", "internal"):
                return (caller_tu, sym)
            if here["linkage"] != "external":
                return ("", sym)
        if strong.get(sym):
            return ("", sym)
        if weak.get(sym):
            return ("", sym)
        return None

    # What an indirect call can reach: every function whose address an indexed file takes, by its type.
    taken: dict[str, set[tuple[tuple[str, str], str]]] = defaultdict(set)
    for tu, m in modules.items():
        for ref in m["referenced"]:
            node = resolve(ref, tu)
            if node is None:
                continue
            owner = node[0] or (strong[node[1]][0] if strong.get(node[1]) else tu)
            d = modules[owner]["defs"].get(node[1]) if owner in modules else None
            if d is not None:
                taken[d["type"]].add((node, owner))

    def home(node: tuple[str, str], caller_tu: str) -> str:
        tu, sym = node
        if tu:
            return tu
        if strong.get(sym):
            return strong[sym][0]
        d = modules[caller_tu]["defs"].get(sym)
        if d is not None and d["linkage"] not in ("available_externally", "external"):
            return caller_tu
        return weak[sym][0]

    if root not in modules[file]["defs"]:
        sys.exit(f"{file} defines no {root}")
    start = (file if modules[file]["defs"][root]["linkage"] in ("private", "internal") else "", root)

    def walk(expand: bool) -> tuple[dict, dict, set, dict, dict]:
        """Every function the root reaches by direct calls, and with `expand`, by indirect ones too, each
        bounded by every function of its type whose address an indexed file takes."""
        where: dict[tuple[str, str], str] = {start: file}
        todo = [start]
        unresolved: dict[str, set[str]] = defaultdict(set)
        intrinsics: set[str] = set()
        runtime: dict[str, set[str]] = defaultdict(set)
        indirect: dict[str, list[str]] = {}
        while todo:
            node = todo.pop()
            tu = where[node]
            d = modules[tu]["defs"].get(node[1])
            if d is None:
                d = modules[home(node, tu)]["defs"][node[1]]
            # The linker keeps one copy of an inline function, from any file that has one, and copies can
            # differ in what they call after inlining: so what each copy calls is reached.
            copies = [(tu, d)]
            if not node[0] and not strong.get(node[1]):
                copies += [(c, modules[c]["defs"][node[1]]) for c in weak.get(node[1], []) if c != tu]
            for copy_tu, copy in copies:
                if copy["indirect"]:
                    indirect[node[1]] = sorted(set(indirect.get(node[1], [])) | set(copy["indirect_types"]))
                for callee in copy["calls"]:
                    if callee.startswith("llvm."):
                        intrinsics.add(callee)
                        continue
                    target = resolve(callee, copy_tu)
                    if target is None:
                        (runtime if RUNTIME.match(callee) else unresolved)[callee].add(node[1])
                        continue
                    if target not in where:
                        where[target] = home(target, copy_tu)
                        todo.append(target)
            # An indirect call can reach any function of its type whose address an indexed file takes: they're
            # its bound.
            for t in indirect.get(node[1], []) if expand else ():
                for target, owner in taken.get(t, ()):
                    if target not in where:
                        where[target] = owner
                        todo.append(target)
        return where, unresolved, intrinsics, runtime, indirect

    where, unresolved, intrinsics, runtime, indirect = walk(expand=False)
    bounded, bounded_unresolved, _, _, _ = walk(expand=True)
    bounded_instructions = sum(modules[tu]["defs"][sym]["instructions"] for (_, sym), tu in bounded.items())

    # Every copy whose calls the walk followed is part of the closure: its file is compiled, its anchors
    # hashed, and its IR recorded, so a change to any copy shows.
    def copy_files(node: tuple[str, str], tu: str) -> list[str]:
        if not node[0] and not strong.get(node[1]):
            return sorted({tu, *weak.get(node[1], [])})
        return [tu]

    reached_tus = sorted({c for node, tu in where.items() for c in copy_files(node, tu)})
    anchors: dict[str, str] = {}
    for tu in reached_tus:
        for p in dependencies(cached(cache, tu)[1]):
            if p.is_relative_to(s):
                anchors[str(p.relative_to(s))] = ""
    hashes = hashing.sha256_files([s / a for a in anchors])
    anchors = {a: hashes[s / a] for a in sorted(anchors)}

    functions: list[dict[str, Any]] = []
    for (key, sym), tu in sorted(where.items(), key=lambda kv: (kv[1], kv[0][1])):
        d = modules[tu]["defs"][sym]
        others = [c for c in copy_files((key, sym), tu) if c != tu]
        functions.append(
            {"symbol": sym, "file": tu, "linkage": d["linkage"], "instructions": d["instructions"],
             "ir_sha256": d["ir_sha256"], "indirect": d["indirect_types"],
             "copies": {c: modules[c]["defs"][sym]["ir_sha256"] for c in others}}
        )  # fmt: skip

    # The one-definition rule: whether each inline function's copies in the indexed files are the same IR.
    odr_differ = []
    odr_n = 0
    for f in functions:
        if f["linkage"] in ("linkonce_odr", "weak_odr"):
            odr_n += 1
            copies = {modules[t]["defs"][f["symbol"]]["ir_sha256"] for t in weak.get(f["symbol"], [])}
            if len(copies) > 1:
                odr_differ.append({"symbol": f["symbol"], "copies": len(weak[f["symbol"]]),
                                   "distinct": len(copies)})  # fmt: skip
    names = demangle(sorted(unresolved) + sorted(indirect))
    # Complete only with every call resolved, and every indirect call bounded by something tighter than its
    # type, which this doesn't have yet: a bound by type takes in every virtual function of that type.
    complete = not unresolved and not indirect
    linkage = Counter(f["linkage"] for f in functions)
    return {
        "schema": SCHEMA,
        "name": name,
        "root": {"symbol": root, "file": file},
        "llvm": pins.llvm(),
        "clang": proc.run(["clang", "--version"], timeout=60).stdout.decode().splitlines()[0],
        "build": flags()
        | {
            "proof_cflags": "PROOF_CFLAGS from the dev shell",
            "llvm_config_includedir": True,
            "directory_includes": DIRECTORY_INCLUDES,
        },
        "index": index,
        "not_indexed": sorted(failed_files),
        "complete": complete,
        "summary": {
            "functions": len(functions),
            "instructions": sum(f["instructions"] for f in functions),
            "files_compiled": len(reached_tus),
            "anchors": len(anchors),
            "by_linkage": dict(sorted(linkage.items())),
            "functions_with_indirect_calls": len(indirect),
            "indirect_call_types": len({t for ts in indirect.values() for t in ts}),
            "bounded_by_type": {
                "functions": len(bounded),
                "instructions": bounded_instructions,
                "files_compiled": len(set(bounded.values())),
                "unresolved": len(bounded_unresolved),
            },
            "intrinsics": len(intrinsics),
            "runtime": len(runtime),
            "unresolved": len(unresolved),
            "odr_copies": odr_n,
            "odr_copies_differing": len(odr_differ),
        },
        "files": anchors,
        "compiled": reached_tus,
        "functions": functions,
        "intrinsics": sorted(intrinsics),
        "runtime": {k: sorted(v) for k, v in sorted(runtime.items())},
        "unresolved": {
            k: {"demangled": names.get(k, k), "from": sorted(v)[:5]} for k, v in sorted(unresolved.items())
        },
        "odr_differing": odr_differ,
        "indirect": {k: {"demangled": names.get(k, k), "types": v} for k, v in sorted(indirect.items())},
    }


def dump(closure: dict[str, Any]) -> str:
    """JSON with one function per line, so a change to the closure reads as a diff of the functions it
    touched."""
    head = {k: v for k, v in closure.items() if k != "functions"}
    text = json.dumps(head, indent=1)
    lines = [json.dumps(f) for f in closure["functions"]]
    return text[:-2] + ',\n "functions": [\n  ' + ",\n  ".join(lines) + "\n ]\n}\n"


def check(
    name: str, rebuild: bool, jobs: int, cache: Path, path: Path | None = None, reuse: bool = False
) -> int:
    c = json.loads((path or HERE / f"{name}.json").read_text())
    s = src()
    if c.get("schema") != SCHEMA or c["llvm"] != pins.llvm():
        print(f"FAIL {name}: the closure is for {c.get('llvm')}, and the pin is {pins.llvm()}")
        return 1
    hashes = hashing.sha256_files([s / a for a in c["files"]])
    changed = sorted(a for a, h in c["files"].items() if hashes[s / a] != h)
    if changed:
        print(f"FAIL {name}: {len(changed)} files changed, such as {changed[:5]}")
        return 1
    print(f"ok   {name}: its {len(c['files'])} files have the recorded SHA-256s")
    clang = proc.run(["clang", "--version"], timeout=60).stdout.decode().splitlines()[0]
    if clang != c["clang"]:
        print(f"FAIL {name}: clang is {clang!r}, and the closure was derived with {c['clang']!r}")
        return 1
    print(f"ok   {name}: clang is the one it was derived with")
    if not rebuild:
        return 0
    inc = includedir()
    with ThreadPoolExecutor(jobs) as pool:
        failed = [
            f for f in pool.map(lambda p: compile_one(p, cache, inc, force=not reuse), c["compiled"]) if f
        ]
    if failed:
        print(f"FAIL {name}: {failed[0]}")
        return 1
    modules = {tu: load(cache, tu) for tu in c["compiled"]}
    wrong = []
    for f in c["functions"]:
        for file, h in {f["file"]: f["ir_sha256"], **f["copies"]}.items():
            d = modules[file]["defs"].get(f["symbol"])
            if d is None or d["ir_sha256"] != h:
                wrong.append(f"{f['symbol']} in {file}")
    if wrong:
        print(f"FAIL {name}: {len(wrong)} functions' IR or calls changed, such as {wrong[:3]}")
        return 1
    copies = sum(len(f["copies"]) for f in c["functions"])
    n, files = len(c["functions"]), len(c["compiled"])
    print(f"ok   {name}: its {files} files compile to the same {n} functions, and {copies} more copies")
    return 0


def link(name: str, out: Path, cache: Path) -> int:
    """The closure as one module: its files linked, and its functions taken out of them with llvm-extract,
    which keeps each one's callees as declarations if they aren't in it. Then what ir-lean makes of it."""
    c = json.loads((HERE / f"{name}.json").read_text())
    lls = [str(cached(cache, tu)[0]) for tu in c["compiled"]]
    linked = out.with_suffix(".linked.ll")
    r = proc.run(["llvm-link", "-S", "-o", str(linked), *lls], timeout=1800)
    if r.exit != 0:
        print(r.stderr.decode(errors="replace")[-2000:])
        return 1
    # Internal functions from different files can share a name, and llvm-link renames them, so they're
    # reached through LLVM's own call graph, from the root, and the rest by name too, since llvm-extract
    # doesn't follow an alias, such as a complete-object constructor's, to what it names.
    named = [f"--func={f['symbol']}" for f in c["functions"] if f["linkage"] not in ("internal", "private")]
    argv = [
        "llvm-extract",
        "--recursive",
        f"--func={c['root']['symbol']}",
        *named,
        "-S",
        "-o",
        str(out),
        str(linked),
    ]
    r = proc.run(argv, timeout=1800)
    if r.exit != 0:
        print(r.stderr.decode(errors="replace")[-2000:])
        return 1
    report = proc.run([str(ROOT / "build" / "ir-lean"), str(out), "--report"], timeout=1800)
    lines = [ln.split("\t") for ln in report.stdout.decode().splitlines()]
    ok = [x for x in lines if x[0] == "ok"]
    refused = [x for x in lines if x[0] == "unsupported"]
    defined = len(re.findall(r"^define ", out.read_text(), re.M))
    print(f"{name}: {defined} functions in one module, {len(ok)} translated, {len(refused)} refused")
    reasons = Counter(re.sub(r"@[-\w.$\"]+", "@F", x[2]).split(":")[0][:80] for x in refused if len(x) > 2)
    for reason, n in reasons.most_common(15):
        print(f"  {n:5} {reason}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("derive")
    d.add_argument("--name", required=True)
    d.add_argument("--root", required=True)
    d.add_argument("--file", required=True)
    d.add_argument("--index", nargs="*", default=INDEX)
    c = sub.add_parser("check")
    c.add_argument("name")
    c.add_argument("--rebuild", action="store_true")
    c.add_argument("--path", type=Path, help="check this file rather than NAME.json here")
    c.add_argument(
        "--reuse", action="store_true", help="with --rebuild, use what an earlier --rebuild compiled"
    )
    k = sub.add_parser("link")
    k.add_argument("name")
    k.add_argument("out", type=Path)
    for p in (d, c, k):
        p.add_argument("--jobs", type=int, default=4)
        p.add_argument("--cache", type=Path, default=ROOT / "build" / "closure")
    args = ap.parse_args()
    if args.cmd == "derive":
        closure = derive(args.name, args.root, args.file, args.index, args.jobs, args.cache)
        (HERE / f"{args.name}.json").write_text(dump(closure))
        print(json.dumps(closure["summary"], indent=1))
        return 0
    if args.cmd == "check":
        return check(args.name, args.rebuild, args.jobs, args.cache, args.path, args.reuse)
    return link(args.name, args.out, args.cache)


if __name__ == "__main__":
    sys.exit(main())
