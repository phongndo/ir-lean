#!/usr/bin/env python3
"""The kernel corpus's benchmark harness: builds a project's baseline and a candidate, checks they differ only
in the rewritten functions, and times them by docs/kernels.md's protocol. docs/kernels.md, "The harness".

1. `build`: the baseline, the project's own build with the pinned clang and its own flags, at -O3, or at the
   level the project builds at itself (`--opt project`), as decision 3 asks for zlib-ng's -O2.
2. `candidate`: a second tree of the same build, with the rewritten unit's object replaced and the binaries
   linked again by the build's own commands. Before anything is timed it checks that `llc` on the unit's
   unchanged IR gives the baseline's machine code, that the two builds' binaries differ in the rewritten
   functions and nothing else, and that each workload's check passes and its output is the baseline's.
3. `plan`: what a comparison will be, written before it's run: the two builds by their records' hashes, the
   workload, the threads and cores, the sessions and pairs, and a new seed for each session.
4. `measure`: runs a plan's sessions. Each pins itself to cores of one CCD, warms both builds once, and runs
   pairs back to back in an order drawn from its seed. No pair is removed. A run under `--min-seconds`, 2 s,
   is repeated inside one timed command until it isn't. Each run records its time, its output's hash, the
   load average and the cores.
5. `compare`: the median of the paired ratios with its bootstrap interval, per session and pooled, and the
   verdict by bench/kernels/protocol.py's rule: faster, slower or inconclusive.

A candidate is a unit's rewritten IR (`--ir`, the unit's whole module with the functions named by
`--functions` changed), or an object (`--object`). Controls, which check the harness and are never wins, can
also be the unit's unchanged IR (`--unchanged`) or the unit compiled at another level (`--recompile -O0`).

usage: bench/kernels/harness.py build PROJECT [--opt -O3|project]
       bench/kernels/harness.py candidate PROJECT NAME --unit SOURCE (--ir F.ll --functions F,G |
                              --object F.o --functions F,G | --unchanged | --recompile LEVEL) [--control KIND]
       bench/kernels/harness.py plan PROJECT --candidate NAME --workload W --out PLAN.json
                              [--baseline NAME] [--sessions 2] [--pairs 15] [--kind confirmation] [--cpus 8]
       bench/kernels/harness.py measure PLAN.json [--session N]
       bench/kernels/harness.py compare SESSION.json... [--other SESSION.json]... [--out FILE]
Every command takes [--opt -O3|project] [--work DIR] [--inputs DIR] [--spec PROJECT.toml]. `--spec` reads a
project from a file instead of the manifest, as tests/kernels_bench_test.py's synthetic one is.
"""

from __future__ import annotations

import argparse
import contextlib
import math
import os
import platform
import random
import re
import secrets
import shlex
import shutil
import statistics
import sys
import tomllib
from collections.abc import Generator
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(HERE))
import kernels  # noqa: E402
import protocol  # noqa: E402
from irlean import hashing, pins, proc, schemas  # noqa: E402

HARNESS = HERE / "harness.toml"
WORK = ROOT / "build" / "kernels" / "bench"
INPUTS = ROOT / "build" / "kernels" / "inputs"
# The levels a baseline is built at: the corpus's, or the project's own.
CORPUS_OPT = "-O3"
OWN_OPT = "project"
# What a control checks. A record with one is never a win.
CONTROLS = ("a/a", "slower", "faster")
# The longest a timed run, a build or a check may take.
RUN_LIMIT_S = 1800
BUILD_LIMIT_S = 3600
LEVEL = re.compile(r"-O([0-3sgz]?)")
# What `llc` takes for each level clang compiles at.
LLC_LEVEL = {"-O0": "-O0", "-O1": "-O1", "-O2": "-O2", "-O3": "-O3", "-Os": "-O2", "-Oz": "-O2", "-Og": "-O1"}
# Flags that write files a compile to IR mustn't, each with how many arguments it takes.
DEPENDENCY_FLAGS = {"-MD": 0, "-MMD": 0, "-MP": 0, "-MF": 1, "-MT": 1, "-MQ": 1}
# Padding objdump shows at the end of a function, which depends on where the next one starts.
PADDING = re.compile(r"^\s*(int3|nop\w*\b.*|xchg\s+%ax,%ax|data16\b.*|cs nop\w*.*)\s*$")


class Refused(Exception):
    """A build, a candidate or a session the protocol doesn't allow, or a check that failed."""


# ------------------------------------------------------------------------------------------------------------
# Projects and workloads


@dataclass
class Workload:
    name: str
    command: list[str]
    measure: str = protocol.TIME
    output: str = "result"
    rate: str | None = None
    check: list[str] | None = None
    setup: list[str] | None = None
    threads: int = 1
    # Where each field came from: the manifest or harness.toml, as a record says which.
    sources: dict[str, str] = field(default_factory=dict)

    def as_record(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "command": self.command,
            "measure": self.measure,
            "output": self.output,
            "rate": self.rate,
            "check": self.check,
            "setup": self.setup,
            "threads": self.threads,
            "from": self.sources,
        }


@dataclass
class Project:
    name: str
    src: Path
    system: str
    targets: list[str]
    binaries: list[str]
    configure: list[str]
    flags: list[str]
    project_opt: str
    workloads: dict[str, Workload]
    # The source's identity: its commit and Nix hash, or what a spec file says.
    pin: dict[str, str]
    # Where the workloads' inputs are, as bench/kernels/kernels.py fetches them.
    inputs: Path = INPUTS

    def tree(self, work: Path, opt: str, variant: str) -> Path:
        """Where a variant's build lives."""
        return work / self.name / opt_tag(opt) / variant


def opt_tag(opt: str) -> str:
    return "O3" if opt == CORPUS_OPT else "own"


def workloads(raw: dict[str, Any], manifest_workload: dict[str, Any] | None) -> dict[str, Workload]:
    """A project's workloads, from harness.toml's table, with the manifest's fields over the one that runs the
    manifest's command."""
    out: dict[str, Workload] = {}
    for name, w in raw.items():
        fields = dict(w)
        sources = dict.fromkeys(fields, "harness")
        if fields.pop("manifest", False):
            if manifest_workload is None:
                raise Refused(f"workload {name} runs the manifest's command, and the manifest has none")
            for key in ("command", "check", "threads", "measure", "output", "rate", "setup"):
                if key in manifest_workload:
                    fields[key] = manifest_workload[key]
                    sources[key] = "manifest"
            sources.pop("manifest", None)
        check = fields.get("check")
        if isinstance(check, dict):
            # A check the manifest gives as a table, with its command in it.
            check = check.get("command")
        workload = Workload(
            name=name,
            command=list(fields["command"]),
            measure=fields.get("measure", protocol.TIME),
            output=fields.get("output", "result"),
            rate=fields.get("rate"),
            check=list(check) if check else None,
            setup=list(fields["setup"]) if fields.get("setup") else None,
            threads=int(fields.get("threads", 1)),
            sources=sources,
        )
        if workload.measure not in protocol.MEASURES:
            raise Refused(f"{name}: measure {workload.measure!r} isn't one of {', '.join(protocol.MEASURES)}")
        if workload.output not in ("result", "timings"):
            raise Refused(f"{name}: output {workload.output!r} isn't result or timings")
        if workload.measure == protocol.RATE and not workload.rate:
            raise Refused(f"{name}: a rate needs `rate`, a pattern that matches the figure")
        if workload.output == "timings" and not workload.check:
            raise Refused(f"{name}: its output is only timings, so it needs a check of the functions it runs")
        out[name] = workload
    return out


def project_from_manifest(name: str, offline: bool = False) -> Project:
    manifest = kernels.load()
    entry = manifest.get("project", {}).get(name)
    if entry is None:
        raise Refused(f"the manifest has no project {name}")
    harness = tomllib.loads(HARNESS.read_text()).get(name)
    if harness is None or "build" not in harness:
        raise Refused(f"{HARNESS.relative_to(ROOT)} doesn't say how to build {name}")
    src = kernels.source(name, entry, offline)
    if src is None:
        raise Refused(f"{name}'s source isn't in the Nix store")
    build = harness["build"]
    return Project(
        name=name,
        src=src,
        system=build["system"],
        targets=list(build["targets"]),
        binaries=list(build["binaries"]),
        configure=list(build.get("configure", [])),
        flags=list(manifest["corpus"].get("flags", [])),
        project_opt=entry["project_opt"],
        workloads=workloads(harness.get("workload", {}), entry.get("workload")),
        pin={"rev": entry["rev"], "nix_hash": entry["nix_hash"], "tag": entry.get("tag", "")},
    )


def project_from_spec(path: Path) -> Project:
    """A project a file describes, with its source beside it, as the test's synthetic one is."""
    spec = tomllib.loads(path.read_text())
    src = (path.parent / spec["src"]).resolve()
    return Project(
        name=spec["name"],
        src=src,
        system=spec["system"],
        targets=list(spec["targets"]),
        binaries=list(spec["binaries"]),
        configure=list(spec.get("configure", [])),
        flags=list(spec.get("flags", [])),
        project_opt=spec.get("project_opt", CORPUS_OPT),
        workloads=workloads(spec.get("workload", {}), None),
        pin={"spec": str(path.resolve().relative_to(ROOT)), "sha256": hashing.files_hash(src, files(src))},
    )


def files(root: Path) -> list[Path]:
    return [p for p in hashing.walk(root) if p.is_file() and not p.is_symlink()]


# ------------------------------------------------------------------------------------------------------------
# Building


def environment() -> dict[str, str]:
    """The dev shell's, with what its compiler wrapper adds that stock clang doesn't turned off, as
    bench/kernels/profile.sh and tests/llama_bench.py have it."""
    env = {
        **os.environ,
        "NIX_ENFORCE_NO_NATIVE": "0",
        "NIX_HARDENING_ENABLE": "",
        "CC": "clang",
        "CXX": "clang++",
    }
    env.pop("SOURCE_DATE_EPOCH", None)
    return env


def sh(argv: list[str], cwd: Path | None = None, timeout: float = BUILD_LIMIT_S, **kw: Any) -> proc.Ran:
    r = proc.run(argv, cwd=cwd, env=kw.pop("env", environment()), timeout=timeout, **kw)
    if not r.ok:
        raise Refused(f"{shlex.join(argv)} failed: exit {r.exit} {r.limit or ''}\n{r.output[-3000:]}")
    return r


def make_flags(project: Project, opt: str) -> list[str]:
    """A make build's variables. Its own level can only be the corpus's, since CFLAGS replaces the one it
    would set."""
    if opt != CORPUS_OPT and project.project_opt != CORPUS_OPT:
        raise Refused(
            f"{project.name} builds with make at {project.project_opt}, which the harness can't ask for"
        )
    flags = shlex.join([CORPUS_OPT, *project.flags])
    return [f"CFLAGS={flags}", f"CXXFLAGS={flags}"]


def configure_and_build(project: Project, opt: str, tree: Path) -> Path:
    """Builds `project` its own way into `tree`, and returns the directory its binaries are in."""
    if tree.exists():
        shutil.rmtree(tree)
    tree.mkdir(parents=True)
    jobs = str(min(8, os.cpu_count() or 1))
    if project.system == "cmake":
        build = tree / "build"
        flags = project.flags if opt != CORPUS_OPT else [CORPUS_OPT, *project.flags]
        args = [f"-DCMAKE_C_FLAGS={' '.join(flags)}", f"-DCMAKE_CXX_FLAGS={' '.join(flags)}"]
        if opt == CORPUS_OPT:
            # Release adds its own level after CMAKE_C_FLAGS, and the last -O wins, so it's set too.
            args += [f"-DCMAKE_{lang}_FLAGS_RELEASE={CORPUS_OPT} -DNDEBUG" for lang in ("C", "CXX")]
        sh(
            [
                "cmake",
                "-S",
                str(project.src),
                "-B",
                str(build),
                "-G",
                "Ninja",
                "-DCMAKE_BUILD_TYPE=Release",
                *args,
                *project.configure,
            ]
        )
        sh(["ninja", "-C", str(build), "-j", jobs, *project.targets])
        return build
    if project.system == "make":
        # It builds in its source tree, so on a copy, as profile.sh does.
        build = tree / "src"
        shutil.copytree(project.src, build, symlinks=True)
        for p in [build, *hashing.walk(build)]:
            if not p.is_symlink():
                p.chmod(p.stat().st_mode | 0o200)
        sh(
            [
                "make",
                "-C",
                str(build),
                "-j",
                jobs,
                *make_flags(project, opt),
                *project.configure,
                *project.targets,
            ]
        )
        return build
    raise Refused(f"{project.name}: build system {project.system!r} isn't cmake or make")


def build_commands(project: Project, opt: str, build: Path) -> list[list[str]]:
    """Every command the build runs for its targets, as argument lists, run in `build`."""
    if project.system == "cmake":
        text = sh(["ninja", "-C", str(build), "-t", "commands", *project.targets]).out
    else:
        text = sh(
            [
                "make",
                "-C",
                str(build),
                "-n",
                "-B",
                *make_flags(project, opt),
                *project.configure,
                *project.targets,
            ]
        ).out
    out = []
    for line in text.splitlines():
        with contextlib.suppress(ValueError):
            argv = shlex.split(line)
            if argv and not argv[0].startswith("make"):
                out.append(argv)
    return out


def level(argv: list[str]) -> str | None:
    """The optimization level a compile command asks for: its last -O flag."""
    found = [a for a in argv if LEVEL.fullmatch(a)]
    if not found:
        return None
    return "-O1" if found[-1] == "-O" else found[-1]


@dataclass
class Compile:
    """One compile command of the unit: its arguments, run in `cwd`, and the object it writes."""

    argv: list[str]
    cwd: Path
    obj: Path

    def as_record(self, tree: Path) -> dict[str, Any]:
        return {"argv": self.argv, "object": str(self.obj.relative_to(tree)), "level": level(self.argv)}


def compiles(project: Project, opt: str, build: Path) -> list[Compile]:
    """The compile commands among the build's, each with the object it writes."""
    out = []
    for argv in build_commands(project, opt, build):
        if "-c" not in argv or "-o" not in argv:
            continue
        out.append(Compile(argv, build, (build / argv[argv.index("-o") + 1]).resolve()))
    return out


def sources_of(c: Compile) -> list[Path]:
    return [
        (c.cwd / a).resolve()
        for a in c.argv[1:]
        if not a.startswith("-") and Path(a).suffix in (".c", ".cc", ".cpp", ".cxx")
    ]


def unit_compiles(project: Project, opt: str, build: Path, unit: str) -> list[Compile]:
    """The compile commands of `unit` that the targets need."""
    root = build if project.system == "make" else project.src
    want = (root / unit).resolve()
    found = [c for c in compiles(project, opt, build) if want in sources_of(c)]
    if not found:
        raise Refused(f"{project.name}: the build compiles no {unit} for {', '.join(project.targets)}")
    return found


def check_levels(project: Project, opt: str, build: Path) -> str:
    """Checks every compile is at the level asked for, and returns it."""
    found = {level(c.argv) for c in compiles(project, opt, build)}
    if opt == CORPUS_OPT and found != {CORPUS_OPT}:
        raise Refused(
            f"{project.name}: asked for {CORPUS_OPT}, and the build compiles at {sorted(map(str, found))}"
        )
    if len(found) != 1 or None in found:
        raise Refused(f"{project.name}: its compiles aren't at one level: {sorted(map(str, found))}")
    got = found.pop()
    assert got is not None
    if opt == OWN_OPT and got != project.project_opt:
        raise Refused(
            f"{project.name}: its own build compiles at {got}, and the manifest says {project.project_opt}"
        )
    return got


def tools() -> dict[str, Any]:
    """The compiler and the tools a build record names, by path, hash and version."""
    out: dict[str, Any] = {}
    for name in ("clang", "llc", "objdump"):
        t = pins.tool(name)
        out[name] = None if t is None else {"path": str(t.path), "sha256": t.sha256, "version": t.version}
    return out


def binaries(project: Project, build: Path) -> dict[str, str]:
    return {b: hashing.sha256_file(build / b) for b in project.binaries}


def repo() -> dict[str, Any]:
    head = proc.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], timeout=60)
    dirty = proc.run(["git", "-C", str(ROOT), "status", "--porcelain", "--untracked-files=no"], timeout=60)
    return {
        "commit": head.out.strip() if head.ok else None,
        "dirty": bool(dirty.out.strip()) if dirty.ok else None,
    }


def host() -> dict[str, Any]:
    return {
        "name": platform.node().split(".")[0],
        "platform": sys.platform,
        "machine": platform.machine(),
        "release": platform.release(),
        "cpus": os.cpu_count(),
    }


def build_baseline(project: Project, opt: str, work: Path) -> dict[str, Any]:
    tree = project.tree(work, opt, "baseline")
    build = configure_and_build(project, opt, tree)
    got = check_levels(project, opt, build)
    record = {
        "schema": schemas.KERNELS_BUILD,
        "project": project.name,
        "pin": project.pin,
        "variant": "baseline",
        "opt": opt,
        "level": got,
        "system": project.system,
        "configure": project.configure,
        "flags": project.flags,
        "targets": project.targets,
        "build": str(build.relative_to(tree)),
        "binaries": binaries(project, build),
        "control": None,
        "tools": tools(),
        "repo": repo(),
        "host": host(),
        "built": proc.now(),
    }
    schemas.write(tree / "build.json", record, schemas.KERNELS_BUILD, indent=2)
    return record


# ------------------------------------------------------------------------------------------------------------
# Machine code


def code(path: Path) -> dict[str, str]:
    """Each function's machine code in an object or a binary, without addresses or anything that only says
    where things are, as tests/llama.py's `disassembly` has it, and without the padding after it. A name
    defined twice, as static functions of two units can be, is kept apart by a `#2`."""
    text = sh(["objdump", "-d", "--no-show-raw-insn", "--no-addresses", str(path)], env=None).out
    out: dict[str, str] = {}
    name: str | None = None
    lines: list[str] = []

    def keep() -> None:
        if name is None:
            return
        while lines and PADDING.match(lines[-1]):
            lines.pop()
        key, n = name, 1
        while key in out:
            n += 1
            key = f"{name}#{n}"
        out[key] = "\n".join(lines)

    for line in text.splitlines():
        if m := re.fullmatch(r"<(.+)>:", line):
            keep()
            name, lines = m[1], []
        elif line.startswith("Disassembly of section"):
            keep()
            name, lines = None, []
        elif name is not None and line.strip():
            text = re.sub(r"\b[0-9a-f]+ <([^>+]+)(\+0x[0-9a-f]+)?>", r"<\1\2>", line)
            text = re.sub(r"-?0x[0-9a-f]+\(%rip\)", "D(%rip)", text)
            lines.append(re.sub(r"\s*#.*$", "", text))
    keep()
    return out


def changed(a: dict[str, str], b: dict[str, str]) -> list[str]:
    """The functions whose code differs, or that only one of the two has."""
    return sorted(f for f in a.keys() | b.keys() if a.get(f) != b.get(f))


def ir_argv(c: Compile, out: Path) -> list[str]:
    """`c`, giving the unit's IR instead of its object, with its use lists, as tests/llama_bench.py does."""
    argv, skip = [], 0
    for i, a in enumerate(c.argv):
        if skip:
            skip -= 1
        elif a == "-c":
            pass
        elif a == "-o":
            skip = 1
        elif a in DEPENDENCY_FLAGS:
            skip = DEPENDENCY_FLAGS[a]
        elif i > 0 and a.startswith(("-MF", "-MT", "-MQ")) and len(a) > 3:
            pass
        else:
            argv.append(a)
    return [*argv, "-S", "-emit-llvm", "-Xclang", "-emit-llvm-uselists", "-o", str(out)]


def drop_asm_uselists(ll: Path) -> int:
    """Drops the `uselistorder` directives for inline assembly from `ll`, and says how many. The pinned clang
    writes them and its own parser refuses them, as "invalid type for inline asm constraint string", so
    `llc` can't read the IR otherwise. They only order the uses of an `asm` value, and the check that `llc`
    gives the build's machine code says whether dropping them changed anything."""
    lines = ll.read_text().splitlines(keepends=True)
    kept = [line for line in lines if not line.startswith("uselistorder ptr asm ")]
    if len(kept) != len(lines):
        ll.write_text("".join(kept))
    return len(lines) - len(kept)


def recompile_argv(c: Compile, at: str, out: Path) -> list[str]:
    """`c` at another level, writing `out`."""
    argv = [at if LEVEL.fullmatch(a) else a for a in c.argv]
    argv[argv.index("-o") + 1] = str(out)
    return argv


def relocation(argv: list[str]) -> str:
    """The relocation model clang compiles `argv` with: pic, as for PIE, clang's default on Linux, unless the
    last of the flags that set it turns it off."""
    model = "pic"
    for a in argv:
        if a in ("-fPIC", "-fpic", "-fPIE", "-fpie"):
            model = "pic"
        elif a in ("-fno-pic", "-fno-PIC", "-fno-pie", "-fno-PIE"):
            model = "static"
    return model


def llc(c: Compile, ll: Path, out: Path) -> None:
    at = level(c.argv) or "-O0"
    sh(
        [
            "llc",
            LLC_LEVEL[at],
            f"-relocation-model={relocation(c.argv)}",
            "-filetype=obj",
            str(ll),
            "-o",
            str(out),
        ]
    )


# ------------------------------------------------------------------------------------------------------------
# Candidates


@dataclass
class Replacement:
    """What a candidate puts in place of its unit's object."""

    form: str
    functions: list[str]
    ir: Path | None = None
    obj: Path | None = None
    level: str | None = None


def downstream(build: Path, node: str) -> list[str]:
    """What ninja builds from `node`, directly or not: the libraries and binaries an object is linked into."""
    seen: list[str] = []
    todo = [node]
    while todo:
        text = sh(["ninja", "-C", str(build), "-t", "query", todo.pop()]).out
        outputs = False
        for line in text.splitlines():
            if line.startswith("  "):
                outputs = line.strip() == "outputs:" or (outputs and line.startswith("    "))
                if outputs and line.startswith("    ") and line.strip() not in seen:
                    seen.append(line.strip())
                    todo.append(line.strip())
    return seen


def replace(project: Project, build: Path, obj: Path, new: Path) -> None:
    """Puts `new` where the build has `obj`, so that building the targets links it in with the build's own
    commands and doesn't compile `obj` again. Make goes by times alone, so the object is made newer than the
    binaries. Ninja also keeps each object's time in its deps log, and compiles again an object newer than
    that, so the object keeps its time, and what's linked from it is removed for ninja to link again."""
    if project.system == "cmake":
        st = obj.stat()
        shutil.copy(new, obj)
        os.utime(obj, ns=(st.st_atime_ns, st.st_mtime_ns))
        for out in downstream(build, os.path.relpath(obj, build)):
            path = build / out
            if path.is_file() and not path.is_symlink():
                path.unlink()
    else:
        shutil.copy(new, obj)
        os.utime(obj)


def rebuild(project: Project, opt: str, build: Path) -> None:
    """Links the targets again with the build's own commands, after an object was replaced."""
    if project.system == "cmake":
        sh(["ninja", "-C", str(build), *project.targets])
    else:
        sh(["make", "-C", str(build), *make_flags(project, opt), *project.configure, *project.targets])


def make_candidate(
    project: Project, opt: str, work: Path, name: str, unit: str, rep: Replacement, control: str | None
) -> dict[str, Any]:
    """Builds a candidate and checks it, and writes its record. Raises Refused if a check fails."""
    if name == "baseline" or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", name):
        raise Refused(f"a candidate's name is letters, digits, `_`, `.` and `-`, and not baseline: {name!r}")
    if control is not None and control not in CONTROLS:
        raise Refused(f"a control is one of {', '.join(CONTROLS)}")
    if rep.form in ("unchanged", "recompile") and control is None:
        raise Refused(f"a candidate made by {rep.form} is a control, so it says which with --control")
    base_tree = project.tree(work, opt, "baseline")
    base = schemas.read(base_tree / "build.json", schemas.KERNELS_BUILD)
    base_build = base_tree / base["build"]
    if binaries(project, base_build) != base["binaries"]:
        raise Refused("the baseline's binaries aren't the ones its record has: build it again")
    tree = project.tree(work, opt, name)
    build = configure_and_build(project, opt, tree)
    # A second build of the baseline, before anything is replaced: the same bytes, or at least the same code.
    same_bytes = binaries(project, build) == base["binaries"]
    if not same_bytes:
        for b in project.binaries:
            if differ := changed(code(base_build / b), code(build / b)):
                raise Refused(f"a second build of the baseline differs from it in {', '.join(differ[:10])}")
    scratch = tree / "unit"
    scratch.mkdir()
    replaced = []
    unit_ir = []
    for n, c in enumerate(unit_compiles(project, opt, build, unit), 1):
        ll, again = scratch / f"{n}.ll", scratch / f"{n}.llc.o"
        sh(ir_argv(c, ll), cwd=c.cwd)
        dropped = drop_asm_uselists(ll)
        unit_ir.append(hashing.sha256_file(ll))
        if rep.form in ("ir", "object") and len(set(unit_ir)) != 1:
            raise Refused(
                f"{unit} is compiled to different IR for different targets, and one {rep.form} can't "
                "stand for each"
            )
        llc(c, ll, again)
        built = code(c.obj)
        if differ := changed(built, code(again)):
            raise Refused(
                f"llc on {unit}'s unchanged IR doesn't give the build's machine code, in "
                f"{', '.join(differ[:10])}"
            )
        new = scratch / f"{n}.candidate.o"
        if rep.form == "unchanged":
            shutil.copy(again, new)
        elif rep.form == "recompile":
            assert rep.level is not None
            sh(recompile_argv(c, rep.level, new), cwd=c.cwd)
        elif rep.form == "ir":
            assert rep.ir is not None
            sh(["opt", "-passes=verify", "-disable-output", str(rep.ir)])
            llc(c, rep.ir, new)
        else:
            assert rep.obj is not None
            shutil.copy(rep.obj, new)
        record: dict[str, Any] = {
            "compile": c.as_record(build),
            "ir_sha256": hashing.sha256_file(ll),
            "asm_uselistorder_dropped": dropped,
            "llc_reproduces": True,
            "baseline_object_sha256": hashing.sha256_file(c.obj),
            "candidate_object_sha256": hashing.sha256_file(new),
            "functions_changed": changed(built, code(new)),
        }
        replace(project, build, c.obj, new)
        replaced.append((c, record))
    given = rep.ir or rep.obj
    rebuild(project, opt, build)
    for c, record in replaced:
        if hashing.sha256_file(c.obj) != record["candidate_object_sha256"]:
            raise Refused(f"the build compiled {c.obj.name} again, over the candidate's object")
    # The two builds' binaries differ in the rewritten functions and nothing else.
    unit_functions: set[str] = {f for _, r in replaced for f in r["functions_changed"]}
    differences: dict[str, list[str]] = {}
    for b in project.binaries:
        differences[b] = changed(code(base_build / b), code(build / b))
    found = sorted({f for fs in differences.values() for f in fs})
    if control is None:
        if found != sorted(rep.functions):
            raise Refused(f"the builds differ in {found}, and the candidate declares {sorted(rep.functions)}")
    elif not set(found) <= unit_functions:
        raise Refused(f"the builds differ outside {unit}: {sorted(set(found) - unit_functions)}")
    if control == "a/a" and found:
        raise Refused(f"an A/A control changes nothing, and the builds differ in {found}")
    checks = run_checks(project, opt, work, base_build, build)
    record = {
        "schema": schemas.KERNELS_BUILD,
        "project": project.name,
        "pin": project.pin,
        "variant": name,
        "opt": opt,
        "level": base["level"],
        "system": project.system,
        "configure": project.configure,
        "flags": project.flags,
        "targets": project.targets,
        "build": str(build.relative_to(tree)),
        "binaries": binaries(project, build),
        "control": control,
        "candidate": {
            "second_build_same_bytes": same_bytes,
            "unit": unit,
            "form": rep.form,
            "declared": sorted(rep.functions),
            "input_sha256": hashing.sha256_file(given) if given else None,
            "recompiled_at": rep.level,
            "objects": [r for _, r in replaced],
            "baseline_record_sha256": hashing.sha256_file(base_tree / "build.json"),
            "differ_from_baseline_in": differences,
            "checks": checks,
        },
        "tools": tools(),
        "repo": repo(),
        "host": host(),
        "built": proc.now(),
    }
    schemas.write(tree / "build.json", record, schemas.KERNELS_BUILD, indent=2)
    return record


def run_checks(project: Project, opt: str, work: Path, base: Path, cand: Path) -> dict[str, Any]:
    """Each workload's check on the candidate, and for one whose output is its result, its output against the
    baseline's, once, before anything is timed."""
    out: dict[str, Any] = {}
    for w in project.workloads.values():
        entry: dict[str, Any] = {"check": None, "output": None}
        with session_dir(project, opt, work, f"check-{w.name}") as scratch:
            if w.setup:
                sh(fill(w.setup, places(project, base, scratch, scratch, w)), timeout=RUN_LIMIT_S)
            if w.check:
                where = places(project, cand, scratch, scratch, w)
                sh(fill(w.check, where), timeout=RUN_LIMIT_S)
                entry["check"] = {
                    "command": w.check,
                    "from": w.sources.get("check", "harness"),
                    "passed": True,
                }
            if w.output == "result":
                hashes = {}
                for variant, build in (("baseline", base), ("candidate", cand)):
                    run = scratch / variant
                    run.mkdir()
                    hashes[variant] = run_once(
                        fill(w.command, places(project, build, scratch, run, w)), 1, run
                    )
                    if hashes[variant]["exit"] != 0:
                        raise Refused(f"{w.name} failed with the {variant}: exit {hashes[variant]['exit']}")
                same = hashes["baseline"]["output_sha256"] == hashes["candidate"]["output_sha256"]
                if not same:
                    raise Refused(f"{w.name}'s output with the candidate isn't the baseline's")
                entry["output"] = {"sha256": hashes["baseline"]["output_sha256"], "same": True}
        out[w.name] = entry
    return out


# ------------------------------------------------------------------------------------------------------------
# Running


@contextlib.contextmanager
def session_dir(project: Project, opt: str, work: Path, label: str) -> Generator[Path]:
    d = work / project.name / opt_tag(opt) / "runs" / f"{label}-{secrets.token_hex(4)}"
    d.mkdir(parents=True)
    try:
        yield d
    finally:
        shutil.rmtree(d, ignore_errors=True)


def places(project: Project, build: Path, scratch: Path, out: Path, w: Workload) -> dict[str, str]:
    return {
        "build": str(build),
        "src": str(project.src),
        "inputs": str(project.inputs),
        "work": str(scratch),
        "out": str(out),
        "threads": str(w.threads),
    }


def fill(argv: list[str], where: dict[str, str]) -> list[str]:
    """`argv` with its places filled in. `{input:NAME}` is the inputs directory for a zip, which
    bench/kernels/kernels.py unpacks there, and the file NAME there otherwise."""
    out = []
    for arg in argv:
        a = re.sub(
            r"\{input:([^}]+)\}",
            lambda m: where["inputs"] if m[1].endswith(".zip") else str(Path(where["inputs"]) / m[1]),
            arg,
        )
        for key, value in where.items():
            a = a.replace("{" + key + "}", value)
        if re.search(r"\{[a-z:]+[^}]*\}", a):
            raise Refused(f"{a!r} has a place the harness doesn't fill")
        out.append(a)
    return out


def repeated(argv: list[str], times: int) -> list[str]:
    """`argv` run `times` times, one after another, as one command, stopping at the first that fails."""
    if times == 1:
        return argv
    loop = 'n=0; while [ "$n" -lt "$0" ]; do "$@" || exit; n=$((n + 1)); done'
    return ["/bin/sh", "-c", loop, str(times), *argv]


def output_hash(run: Path) -> str:
    """What a run wrote: its stdout and every file it left in its directory, but its stderr."""
    names = sorted(p for p in files(run) if p.name != "stderr")
    return hashing.sha256_parts(*(f"{p.relative_to(run)}\0{hashing.sha256_file(p)}" for p in names))


def run_once(argv: list[str], times: int, run: Path, w: Workload | None = None) -> dict[str, Any]:
    """Runs a workload's command `times` times as one timed command, in `run`, which it leaves empty."""
    load = os.getloadavg()
    r = proc.run(
        repeated(argv, times),
        stdout=run / "stdout",
        stderr=run / "stderr",
        env=environment(),
        cwd=run,
        timeout=RUN_LIMIT_S,
    )
    record: dict[str, Any] = {
        "wall_s": r.seconds,
        "user_s": r.user_s,
        "sys_s": r.sys_s,
        "exit": r.exit,
        "limit": r.limit,
        "load": [round(x, 2) for x in load],
        "cpus": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
        "output_sha256": output_hash(run),
    }
    if w is not None and w.measure == protocol.RATE:
        assert w.rate is not None
        text = (run / "stdout").read_text(errors="replace") + (run / "stderr").read_text(errors="replace")
        figures = [float(m) for m in re.findall(w.rate, text)]
        record["rate"] = statistics.fmean(figures) if figures else None
        record["figures"] = figures
    for p in sorted(run.iterdir()):
        if p.is_dir():
            shutil.rmtree(p)
        else:
            p.unlink()
    return record


def value(run: dict[str, Any], w: Workload) -> float:
    return float(run["rate"] if w.measure == protocol.RATE else run["wall_s"])


def ccds() -> list[list[int]]:
    """The CPUs this process may run on, grouped by the L3 cache they share: on a Ryzen 9 9950X, its two
    CCDs. One group of every CPU allowed if the kernel doesn't say."""
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    groups: dict[str, list[int]] = {}
    for cpu in allowed:
        groups.setdefault(str(l3(cpu)), []).append(cpu)
    return [sorted(g) for _, g in sorted(groups.items(), key=lambda kv: min(kv[1]))]


def l3(cpu: int) -> list[int] | None:
    """Every CPU that shares `cpu`'s L3 cache, as the kernel says, whatever this process may run on, or None
    if it doesn't say."""
    shared = Path(f"/sys/devices/system/cpu/cpu{cpu}/cache/index3/shared_cpu_list")
    if not shared.exists():
        return None
    return sorted(c for part in shared.read_text().strip().split(",") for c in _span(part))


def cores(threads: int, asked: str | None) -> list[int]:
    """`threads` CPUs in one CCD, one a core: those asked for, or the first cores of the last CCD."""
    groups = ccds()
    if not groups:
        raise Refused("this platform can't pin a process to cores")
    if asked:
        chosen = sorted({int(c) for part in asked.split(",") for c in _span(part)})
    else:
        last = groups[-1]
        firsts = []
        for cpu in last:
            siblings = Path(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list")
            first = min(_span(siblings.read_text().strip().split(",")[0])) if siblings.exists() else cpu
            if first in last and first not in firsts:
                firsts.append(first)
        chosen = firsts[:threads]
    if len(chosen) != threads:
        raise Refused(f"{threads} threads take {threads} cores, and {chosen} is {len(chosen)}")
    if not any(set(chosen) <= set(g) for g in groups):
        raise Refused(f"{chosen} isn't in one CCD: {groups}")
    return chosen


def _span(text: str) -> range:
    lo, _, hi = text.partition("-")
    return range(int(lo), int(hi or lo) + 1)


def make_plan(
    project: Project,
    opt: str,
    work: Path,
    baseline: str,
    candidate: str,
    workload: str,
    sessions: int,
    pairs: int,
    kind: str,
    cpus: str | None,
    min_seconds: float,
) -> dict[str, Any]:
    if workload not in project.workloads:
        raise Refused(f"{project.name} has no workload {workload}: {', '.join(project.workloads)}")
    if kind not in protocol.KINDS:
        raise Refused(f"a session is one of {', '.join(protocol.KINDS)}")
    w = project.workloads[workload]
    records: dict[str, dict[str, Any]] = {}
    digests: dict[str, str] = {}
    for role, variant in (("baseline", baseline), ("candidate", candidate)):
        path = project.tree(work, opt, variant) / "build.json"
        records[role] = schemas.read(path, schemas.KERNELS_BUILD)
        digests[role] = hashing.sha256_file(path)
    built_on = records["candidate"].get("candidate", {}).get("baseline_record_sha256")
    if baseline == "baseline" and built_on not in (None, digests["baseline"]):
        raise Refused(f"{candidate} was built against another baseline than the one there now: make it again")
    controls = {r["control"] for r in records.values()} - {None}
    control = "faster" if baseline != "baseline" else (controls.pop() if controls else None)
    return {
        "schema": schemas.KERNELS_PLAN,
        "project": project.name,
        "opt": opt,
        "workload": w.as_record(),
        "baseline": {"variant": baseline, "record_sha256": digests["baseline"]},
        "candidate": {"variant": candidate, "record_sha256": digests["candidate"]},
        "control": control,
        "kind": kind,
        "sessions": [{"session": n, "seed": secrets.randbits(32)} for n in range(1, sessions + 1)],
        "pairs": pairs,
        "threads": w.threads,
        "cpus": cores(w.threads, cpus),
        "min_seconds": min_seconds,
        "written": proc.now(),
        "repo": repo(),
        "host": host(),
    }


def session(project: Project, plan: dict[str, Any], plan_sha256: str, n: int, work: Path) -> dict[str, Any]:
    """Runs session `n` of `plan`, and returns its record."""
    picked = [s for s in plan["sessions"] if s["session"] == n]
    if not picked:
        raise Refused(f"the plan has no session {n}")
    seed = picked[0]["seed"]
    opt = plan["opt"]
    w = project.workloads[plan["workload"]["name"]]
    if w.as_record() != plan["workload"]:
        raise Refused(f"{w.name} isn't what the plan wrote down")
    builds = {}
    for role in ("baseline", "candidate"):
        tree = project.tree(work, opt, plan[role]["variant"])
        if hashing.sha256_file(tree / "build.json") != plan[role]["record_sha256"]:
            raise Refused(f"the {role}'s build record isn't the one the plan names")
        record = schemas.read(tree / "build.json", schemas.KERNELS_BUILD)
        builds[role] = tree / record["build"]
        if binaries(project, builds[role]) != record["binaries"]:
            raise Refused(f"the {role}'s binaries aren't the ones its record has")
    pinned = list(plan["cpus"])
    if hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, pinned)
    rng = random.Random(seed)
    record: dict[str, Any] = {
        "schema": schemas.KERNELS_SESSION,
        "project": project.name,
        "plan_sha256": plan_sha256,
        "session": n,
        "kind": plan["kind"],
        "control": plan["control"],
        "workload": w.name,
        "measure": w.measure,
        "seed": seed,
        "cpus": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
        # The CPUs sharing the pinned ones' L3 cache, if they all share one, from the kernel's topology.
        "ccd": shared if (shared := l3(pinned[0])) is not None and set(pinned) <= set(shared) else None,
        "threads": w.threads,
        "min_seconds": plan["min_seconds"],
        "started": proc.now(),
        "host": host(),
        "repo": repo(),
    }
    with session_dir(project, opt, work, f"session-{w.name}-{n}") as scratch:
        if w.setup:
            sh(fill(w.setup, places(project, builds["baseline"], scratch, scratch, w)), timeout=RUN_LIMIT_S)

        def one(role: str, times: int) -> dict[str, Any]:
            run = scratch / role
            run.mkdir(exist_ok=True)
            got = run_once(fill(w.command, places(project, builds[role], scratch, run, w)), times, run, w)
            if got["exit"] != 0 or got["limit"]:
                raise Refused(f"{w.name} failed with the {role}: exit {got['exit']} {got['limit'] or ''}")
            if w.measure == protocol.RATE and not got.get("rate"):
                raise Refused(f"{w.name} printed no figure {w.rate!r} matches, with the {role}")
            return got

        warm = {role: one(role, 1) for role in ("baseline", "candidate")}
        if w.output == "result" and warm["baseline"]["output_sha256"] != warm["candidate"]["output_sha256"]:
            raise Refused("warming up, the candidate's output isn't the baseline's")
        once = min(warm["baseline"]["wall_s"], warm["candidate"]["wall_s"])
        times = max(1, math.ceil(plan["min_seconds"] / max(once, 1e-6)))
        record["repeats"] = times
        record["warmup"] = warm
        reference = None
        pairs = []
        for i in range(1, plan["pairs"] + 1):
            order = ["baseline", "candidate"] if rng.random() < 0.5 else ["candidate", "baseline"]
            runs = {role: one(role, times) for role in order}
            if w.output == "result":
                reference = reference or runs["baseline"]["output_sha256"]
                for role, got in runs.items():
                    if got["output_sha256"] != reference:
                        raise Refused(f"pair {i}: the {role}'s output isn't the baseline's")
            pairs.append(
                {
                    "pair": i,
                    "order": order,
                    **runs,
                    "ratio": protocol.ratio(
                        value(runs["baseline"], w), value(runs["candidate"], w), w.measure
                    ),
                }
            )
            print(
                f"     pair {i}/{plan['pairs']}: ratio {pairs[-1]['ratio']:.4f}, "
                f"load {runs[order[0]]['load'][0]}",
                flush=True,
            )
        record["pairs"] = pairs
        record["output_sha256"] = reference
    record["finished"] = proc.now()
    return record


# ------------------------------------------------------------------------------------------------------------
# Comparing


def compare(
    main: list[dict[str, Any]],
    others: dict[str, list[dict[str, Any]]],
    names: list[str],
    rule: protocol.Rule = protocol.PROTOCOL,
    plans: dict[str, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """The verdict on `main`'s sessions, all of one plan, with the project's other workloads' sessions."""
    problems = protocol_problems(main, rule, plans)
    if len({s["workload"] for s in main}) != 1:
        raise Refused("a comparison is of one workload")
    workload = main[0]["workload"]
    pooled_others: dict[str, list[float] | None] = {}
    other_records = {}
    for name, sessions in others.items():
        if name == workload:
            raise Refused(f"{name} is the workload compared, not another")
        problems += [f"{name}: {p}" for p in protocol_problems(sessions, rule, plans)]
        s = protocol.summary([p["ratio"] for x in sessions for p in x["pairs"]], seed_of(sessions), rule)
        pooled_others[name] = s["interval"]
        other_records[name] = {**s, "sessions": [x.get("_sha256") for x in sessions]}
    for name in names:
        if name != workload and name not in pooled_others:
            pooled_others[name] = None
    got = protocol.verdict(
        [[p["ratio"] for p in s["pairs"]] for s in main],
        [s["kind"] for s in main],
        seed_of(main),
        pooled_others,
        rule,
    )
    plan = (plans or {}).get(main[0]["plan_sha256"], {})
    return {
        "schema": schemas.KERNELS_COMPARISON,
        "project": main[0]["project"],
        "workload": workload,
        "plan_sha256": main[0]["plan_sha256"],
        "opt": plan.get("opt"),
        "baseline": plan.get("baseline"),
        "candidate": plan.get("candidate"),
        "control": main[0]["control"],
        "sessions": [
            {
                "session": s["session"],
                "seed": s["seed"],
                "kind": s["kind"],
                "started": s["started"],
                "repeats": s["repeats"],
                "cpus": s["cpus"],
                "sha256": s.get("_sha256"),
                "load": _loads(s),
                **statistic,
            }
            for s, statistic in zip(main, got["sessions"], strict=True)
        ],
        "pooled": got["pooled"],
        "others": other_records,
        "unmeasured": sorted(w for w, i in pooled_others.items() if i is None),
        "by_the_protocol": not problems,
        "protocol_problems": problems,
        "verdict": got["verdict"],
        "conditions": got["conditions"],
        "rule": got["rule"],
    }


def _loads(s: dict[str, Any]) -> dict[str, float]:
    loads = [run["load"][0] for p in s["pairs"] for run in (p["baseline"], p["candidate"])]
    return {"min": min(loads), "median": statistics.median(loads), "max": max(loads)}


def seed_of(sessions: list[dict[str, Any]]) -> int:
    """The pooled bootstrap's seed: from the sessions' own, so the interval is the same every time."""
    return int(hashing.sha256_text(",".join(str(s["seed"]) for s in sessions))[:8], 16)


def protocol_problems(
    sessions: list[dict[str, Any]], rule: protocol.Rule, plans: dict[str, dict[str, Any]] | None
) -> list[str]:
    """How these sessions fall short of the protocol, or nothing."""
    out = []
    if len({s["plan_sha256"] for s in sessions}) != 1:
        out.append("the sessions aren't all of one plan")
    seeds = [s["seed"] for s in sessions]
    if len(set(seeds)) != len(seeds):
        out.append("two sessions share a seed")
    for s in sessions:
        label = f"session {s['session']}"
        if s["min_seconds"] < rule.min_seconds:
            out.append(f"{label}: runs were repeated to {s['min_seconds']} s, not {rule.min_seconds}")
        if s["cpus"] is None or s.get("ccd") is None or not set(s["cpus"]) <= set(s["ccd"]):
            out.append(f"{label}: it wasn't pinned to cores of one CCD")
        if s["cpus"] is not None and len(s["cpus"]) != s["threads"]:
            out.append(f"{label}: {s['threads']} threads on {len(s['cpus'])} cores")
        plan = (plans or {}).get(s["plan_sha256"])
        if plan is not None:
            if s["started"] < plan["written"]:
                out.append(f"{label}: it started before its plan was written")
            if len(s["pairs"]) != plan["pairs"]:
                out.append(f"{label}: {len(s['pairs'])} pairs, and the plan has {plan['pairs']}")
            if s["cpus"] != plan["cpus"]:
                out.append(f"{label}: run on {s['cpus']}, and the plan wrote down {plan['cpus']}")
        elif plans is not None:
            out.append(f"{label}: its plan isn't given")
    return out


# ------------------------------------------------------------------------------------------------------------
# The command line


def load_project(args: argparse.Namespace) -> Project:
    project = project_from_spec(args.spec) if args.spec else project_from_manifest(args.project)
    project.inputs = args.inputs.resolve()
    return project


def workload_names(spec: Path | None, name: str) -> list[str]:
    """A project's workloads, without fetching its source."""
    table = tomllib.loads(spec.read_text()) if spec else tomllib.loads(HARNESS.read_text()).get(name, {})
    return sorted(table.get("workload", {}))


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--opt", default=CORPUS_OPT, choices=[CORPUS_OPT, OWN_OPT])
    common.add_argument("--work", type=Path, default=WORK)
    common.add_argument("--inputs", type=Path, default=INPUTS)
    common.add_argument("--spec", type=Path, help="a project described by a file, not the manifest")
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build", parents=[common])
    b.add_argument("project", nargs="?")
    c = sub.add_parser("candidate", parents=[common])
    c.add_argument("project", nargs="?")
    c.add_argument("name")
    c.add_argument("--unit", required=True)
    form = c.add_mutually_exclusive_group(required=True)
    form.add_argument("--ir", type=Path)
    form.add_argument("--object", type=Path)
    form.add_argument("--unchanged", action="store_true")
    form.add_argument("--recompile", metavar="LEVEL", choices=sorted(LLC_LEVEL))
    c.add_argument("--functions", default="")
    c.add_argument("--control", choices=CONTROLS)
    p = sub.add_parser("plan", parents=[common])
    p.add_argument("project", nargs="?")
    p.add_argument("--baseline", default="baseline")
    p.add_argument("--candidate", required=True)
    p.add_argument("--workload", required=True)
    p.add_argument("--sessions", type=int, default=2)
    p.add_argument("--pairs", type=int, default=15)
    p.add_argument("--kind", default=protocol.CONFIRMATION, choices=protocol.KINDS)
    p.add_argument("--cpus")
    p.add_argument("--min-seconds", type=float, default=protocol.PROTOCOL.min_seconds)
    p.add_argument("--out", type=Path, required=True)
    m = sub.add_parser("measure", parents=[common])
    m.add_argument("plan", type=Path)
    m.add_argument("--session", type=int)
    m.add_argument("--project", dest="project")
    k = sub.add_parser("compare", parents=[common])
    k.add_argument("sessions", type=Path, nargs="+")
    k.add_argument("--other", type=Path, action="append", default=[])
    k.add_argument("--out", type=Path)
    k.add_argument(
        "--min-seconds",
        type=float,
        default=protocol.PROTOCOL.min_seconds,
        help="read the sessions by a rule with this in place of the protocol's 2 s, as the test does",
    )
    args = ap.parse_args(argv)
    try:
        if args.cmd == "build":
            record = build_baseline(load_project(args), args.opt, args.work)
            print(f"ok   {record['project']} at {record['level']}: {', '.join(record['binaries'])}")
        elif args.cmd == "candidate":
            project = load_project(args)
            functions = [f for f in args.functions.split(",") if f]
            if (args.ir or args.object) and not functions:
                raise Refused("a rewrite names the functions it changes, with --functions")
            if args.ir:
                rep = Replacement("ir", functions, ir=args.ir.resolve())
            elif args.object:
                rep = Replacement("object", functions, obj=args.object.resolve())
            elif args.unchanged:
                rep = Replacement("unchanged", [])
            else:
                rep = Replacement("recompile", [], level=args.recompile)
            record = make_candidate(project, args.opt, args.work, args.name, args.unit, rep, args.control)
            differ = sorted({f for fs in record["candidate"]["differ_from_baseline_in"].values() for f in fs})
            print(
                f"ok   {record['project']} {args.name}: llc reproduces {args.unit}, and the builds differ in "
                f"{', '.join(differ) or 'nothing'}"
            )
        elif args.cmd == "plan":
            project = load_project(args)
            plan = make_plan(
                project,
                args.opt,
                args.work,
                args.baseline,
                args.candidate,
                args.workload,
                args.sessions,
                args.pairs,
                args.kind,
                args.cpus,
                args.min_seconds,
            )
            schemas.write(args.out, plan, schemas.KERNELS_PLAN, indent=2)
            # The two builds' records beside the plan, so what it compares is known from the plan alone.
            for role in ("baseline", "candidate"):
                tree = project.tree(args.work, args.opt, plan[role]["variant"])
                shutil.copy(tree / "build.json", args.out.with_name(f"{args.out.stem}.{role}.build.json"))
            print(f"ok   {args.out}: {args.sessions} sessions of {args.pairs} pairs on CPUs {plan['cpus']}")
        elif args.cmd == "measure":
            plan = schemas.read(args.plan, schemas.KERNELS_PLAN)
            if args.spec is None:
                args.project = plan["project"]
            project = load_project(args)
            digest = hashing.sha256_file(args.plan)
            for s in plan["sessions"]:
                if args.session not in (None, s["session"]):
                    continue
                print(f"     session {s['session']} of {args.plan}", flush=True)
                record = session(project, plan, digest, s["session"], args.work)
                out = args.plan.with_name(f"{args.plan.stem}.session-{s['session']}.json")
                schemas.write(out, record, schemas.KERNELS_SESSION, indent=2)
                ratios = [p["ratio"] for p in record["pairs"]]
                print(f"ok   {out}: median {statistics.median(ratios):.4f} over {len(ratios)} pairs")
        elif args.cmd == "compare":

            def read(path: Path) -> dict[str, Any]:
                s = schemas.read(path, schemas.KERNELS_SESSION)
                s["_sha256"] = hashing.sha256_file(path)
                return s

            main_sessions = [read(p) for p in args.sessions]
            others: dict[str, list[dict[str, Any]]] = {}
            for p in args.other:
                s = read(p)
                others.setdefault(s["workload"], []).append(s)
            plans = {}
            for path in {*args.sessions, *args.other}:
                for plan_path in path.parent.glob("*.json"):
                    with contextlib.suppress(schemas.SchemaError, OSError):
                        plans[hashing.sha256_file(plan_path)] = schemas.read(plan_path, schemas.KERNELS_PLAN)
            names = workload_names(args.spec, main_sessions[0]["project"])
            rule = protocol.Rule(min_seconds=args.min_seconds)
            result = compare(main_sessions, others, names, rule, plans)
            if args.out:
                schemas.write(args.out, result, schemas.KERNELS_COMPARISON, indent=2)
            print(describe(result))
    except Refused as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1
    return 0


def describe(c: dict[str, Any]) -> str:
    p = c["pooled"]
    lines = [
        f"{c['project']}, {c['workload']}{' (control: ' + c['control'] + ')' if c['control'] else ''}: "
        f"{c['verdict']}, median {p['median']:.4f} [{p['interval'][0]:.4f}, {p['interval'][1]:.4f}] over "
        f"{p['pairs']} pairs in {len(c['sessions'])} sessions"
    ]
    for name, cond in c["conditions"].items():
        lines.append(f"     {'held' if cond['held'] else 'not '} {name}: {cond['says']}")
    lines += [f"     not by the protocol: {problem}" for problem in c["protocol_problems"]]
    return "\n".join(lines)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
