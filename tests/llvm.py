#!/usr/bin/env python3
"""Proves real functions from llvm/llvm-project, from unmodified source, and writes down what it did.

For each target in tests/llvm/targets.toml, this compiles the pinned source with upstream's flags, translates
the IR to Lean, checks the proof against it, allows only known axioms, checks that each theorem is about the
function ir-lean generated, replays the proof through the kernel, and makes sure each of the target's injected
bugs stops the proof from checking with an error of its own. Running out of time or memory says nothing about
the bug. The manifest records the hashes, versions, theorem statements, assumptions and what stopped each
bug's proof. A function only counts toward the score when all of that passes.

usage: tests/llvm.py path/to/ir-lean [--only NAME ...] [--no-mutants] [--manifest FILE]
"""

import argparse
import json
import os
import re
import shutil
import sys
import tempfile
import threading
import time
import tomllib
from concurrent.futures import Future, ThreadPoolExecutor
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, proc  # noqa: E402
from irlean import lean as leanlib  # noqa: E402
from irlean import verdict as core  # noqa: E402

PROOFS = ROOT / "tests" / "llvm"
LEAN_ERROR = leanlib.ERROR
# A line that starts a command, or the doc comment of one.
COMMAND = re.compile(r"(/--|theorem |def |end |namespace |section )")
IMPORT = re.compile(r"^import (\S+)", re.MULTILINE)
# Lean's errors for running out of time, memory or stack, in a tactic or the kernel. A proof that stops at one
# of these might check with more, so it says nothing about whether the code changed. tests/proofs.sh has the
# same list.
LIMIT = leanlib.LIMIT
# A proof that runs away fails. It shouldn't take this long.
TIMEOUT_SECONDS = 600


sha256 = hashing.sha256_file


def checked(r: proc.Ran) -> str:
    """What a command printed, or raises with it if the command failed or ran out of time."""
    if r.limit is not None:
        raise RuntimeError(f"{' '.join(r.argv)}\ntimed out")
    if r.exit != 0:
        raise RuntimeError(f"{' '.join(r.argv)}\n{r.out[:4000]}{r.err[:4000]}")
    return r.out


def run(command: list[str], env: dict[str, str] | None = None, stdin: str | None = None) -> str:
    """Runs a command, and raises with its output if it fails."""
    return checked(proc.run(command, env=env, stdin=stdin, timeout=TIMEOUT_SECONDS))


def theorem_lines(proof: str, theorem: str) -> tuple[int, int]:
    """The lines that can stop a theorem: its own, or all of the `section` it's in, for its helpers."""
    lines = proof.splitlines()
    short = theorem.rsplit(".", 1)[-1]
    starts = [i for i, line in enumerate(lines) if re.match(rf"theorem {re.escape(short)}\b", line)]
    if not starts:
        return 1, len(lines)
    first = starts[0]
    sections = [i for i, line in enumerate(lines[:first]) if re.match(r"section \w+", line)]
    if sections and not any(re.match(r"end \w+", line) for line in lines[sections[-1] : first]):
        name = lines[sections[-1]].split()[1]
        return sections[-1] + 1, next(i for i, line in enumerate(lines) if line.strip() == f"end {name}") + 1
    last = first + 1
    while last < len(lines) and not COMMAND.match(lines[last]):
        last += 1
    return first + 1, last


def ends_command(lines: list[str], last: int) -> bool:
    """Whether a command ends after the first `last` lines, so cutting there leaves none of them half done.

    That's so when the last line kept that isn't blank ends a section, or is inside a proof while the next
    line starts a command. Anything else, such as an attribute for what comes next, isn't cut.
    """
    if last == len(lines):
        return True
    kept = [line for line in lines[:last] if line.strip()]
    if not kept:
        return False
    if kept[-1].startswith("end "):
        return True
    return kept[-1][0].isspace() and COMMAND.match(lines[last]) is not None


def strip_paths(ir: str) -> str:
    """Drops what only names the file, so moving a file doesn't count as changing its code."""
    return "\n".join(
        line for line in ir.splitlines() if not line.startswith(("; ModuleID", "source_filename"))
    )


class Pipeline:
    def __init__(self, tool: Path, work: Path, config: dict[str, Any]) -> None:
        self.tool = tool
        self.work = work
        self.config = config
        self.src = Path(os.environ["LLVM_PROJECT_SRC"])
        self.proof_cflags = os.environ["PROOF_CFLAGS"].split()
        self.memory = os.environ.get("LEAN_MAX_MB", "4000")
        # Lean gives each thread a stack of about 1 GiB, all of it committed. bv_decide forks the Lean
        # process to start its solver, and on a machine with less RAM and swap than that commit, such as
        # CI's runner, the fork can fail with ENOMEM. 64 MB is plenty for these proofs.
        self.limits = ["-M", self.memory, "-s", "65536"]
        # Targets and their mutants each run in a pool. This keeps it to LEAN_JOBS Lean processes in all.
        self.slots = threading.BoundedSemaphore(int(os.environ.get("LEAN_JOBS", "4")))

    def lean_env(self, directory: Path) -> dict[str, str]:
        return {**os.environ, "LEAN_PATH": f"{directory}:{ROOT}/.lake/build/lib/lean"}

    def lean_ran(
        self, directory: Path, *args: str, stdin: str | None = None, env: dict[str, str] | None = None
    ) -> proc.Ran:
        with self.slots:
            return proc.run(
                ["lean", *self.limits, *args],
                env=self.lean_env(directory) | (env or {}),
                stdin=stdin,
                timeout=TIMEOUT_SECONDS,
            )

    def lean(
        self, directory: Path, *args: str, stdin: str | None = None, env: dict[str, str] | None = None
    ) -> str:
        return checked(self.lean_ran(directory, *args, stdin=stdin, env=env))

    def compile_ran(self, directory: Path, source: Path, root: Path) -> proc.Ran:
        olean = directory / (source.stem + ".olean")
        return self.lean_ran(
            directory, "-DwarningAsError=true", "-R", str(root), "-o", str(olean), str(source)
        )

    def compile_lean(self, directory: Path, source: Path, root: Path) -> None:
        checked(self.compile_ran(directory, source, root))

    def source_path(self, target: dict[str, Any], overlay: Path | None) -> Path:
        """Where a target's source is. A file in this repo only says which of LLVM's functions to use."""
        if target.get("wrapper"):
            return ROOT / target["source"]
        return (overlay if overlay is not None else self.src) / target["source"]

    def clang_command(self, target: dict[str, Any], overlay: Path | None, output: Path) -> list[str]:
        flags = self.config["flags"][target["flags"]]
        proof_cflags = self.proof_cflags
        if flags.get("cxx"):
            # The C++ library's headers use `#include_next` to find the C library's, so those come after.
            proof_cflags = ["-idirafter" if flag == "-isystem" else flag for flag in proof_cflags]
        command = ["clang", *proof_cflags, *flags.get("args", []), *target.get("args", [])]
        includes = flags.get("include", [])
        if overlay is not None:
            command += [f"-I{overlay / i}" for i in includes]
        command += [f"-I{self.src / i}" for i in includes]
        command += [f"-I{ROOT / i}" for i in flags.get("local_include", [])]
        if flags.get("llvm_config"):
            command.append("-I" + run(["llvm-config", "--includedir"]).strip())
        source = self.source_path(target, overlay)
        return [*command, "-S", "-emit-llvm", "-fno-discard-value-names", "-o", str(output), str(source)]

    def generate(
        self, target: dict[str, Any], directory: Path, overlay: Path | None = None
    ) -> dict[str, tuple[bool, str]]:
        """Compiles a target's source, and translates and checks its Lean module. Returns what ir-lean says of
        each function: whether it translated it, and its Lean name or why it didn't."""
        name = target["module"]
        ll = directory / f"{name}.ll"
        generated = directory / f"{name}.lean"
        run(self.clang_command(target, overlay, ll))
        # Exit code 3 means some function was left out. Which ones is checked against the theorems.
        result = proc.run([self.tool, ll, "--namespace", name, "-o", generated, "--no-code"])
        if result.exit not in (0, 3):
            raise RuntimeError(f"ir-lean {ll}: {result.err[:4000]}")
        report = proc.run([self.tool, ll, "--namespace", name, "--report"])
        if report.exit not in (0, 3):
            raise RuntimeError(f"ir-lean --report {ll}: {report.err[:4000]}")
        functions = {}
        for line in report.out.splitlines():
            fields = line.split("\t")
            if fields[0] in ("ok", "unsupported") and len(fields) >= 3:
                functions[fields[1]] = (fields[0] == "ok", fields[2])
        self.lean(directory, "-R", str(directory), "-o", str(directory / f"{name}.olean"), str(generated))
        return functions

    def audit_ran(self, directory: Path, module: str, generated: str = "", theorems: str = "") -> proc.Ran:
        return self.lean_ran(
            directory,
            str(ROOT / "tests" / "check_axioms.lean"),
            env={
                "IRLEAN_CHECK_MODULE": module,
                "IRLEAN_CHECK_GENERATED": generated,
                "IRLEAN_CHECK_THEOREMS": theorems,
            },
        )

    def axioms(self, directory: Path, module: str, generated: str = "", theorems: str = "") -> str:
        """The axioms a proof module rests on, reading it as data, and that each theorem in `theorems`, a line
        of a theorem and the Lean name of a function, is about that function as ir-lean generated it in
        `generated`. Raises if anything is wrong."""
        return checked(self.audit_ran(directory, module, generated, theorems)).strip()

    def replay_ran(self, directory: Path, module: str) -> proc.Ran:
        with self.slots:
            return proc.run(["leanchecker", module], env=self.lean_env(directory), timeout=TIMEOUT_SECONDS)

    def replay(self, directory: Path, module: str) -> None:
        """Replays a module's declarations through the kernel. Lean code can add one the kernel never checked,
        with `debug.skipKernelTC`, and nothing else here would notice."""
        checked(self.replay_ran(directory, module))

    def proved(
        self,
        directory: Path,
        compiled: proc.Ran,
        module: str,
        generated: str,
        theorems: str,
        also: tuple[str, ...] = (),
    ) -> tuple[str, core.Decision]:
        """For a proof module `compiled` compiled: audits its axioms, and that each of `theorems` is about its
        function in `generated`, and replays it and the modules in `also` through the kernel. Returns the
        axioms, and whether irlean.verdict calls it proved. Raises if a step fails."""
        checked(compiled)
        audit = self.audit_ran(directory, module, generated, theorems)
        axioms = checked(audit).strip()
        replays = {m: self.replay_ran(directory, m) for m in (module, *also)}
        for r in replays.values():
            checked(r)
        olean = directory / f"{module}.olean"
        evidence = core.Evidence(
            lean=core.Step.of("lean", compiled),
            replay=core.Step.of("leanchecker", replays[module]),
            axioms=core.Step.of("check_axioms", audit),
            files={str(olean): olean.is_file()},
            checks={f"leanchecker {m}": r.ok for m, r in replays.items()},
        )
        return axioms, core.decide(core.Verdict.PROVED, evidence)

    def statement(self, directory: Path, module: str, theorem: str) -> str:
        source = f"import {module}\nset_option pp.fullNames true\n#check @{theorem}\n"
        return self.lean(directory, "--stdin", stdin=source).strip()

    def check_mutant(
        self, target: dict[str, Any], mutant: dict[str, str], theorem: str
    ) -> tuple[str | None, str | None]:
        """Returns what went wrong, or None if the bug stopped the proof of `theorem`, and the error that
        stopped it."""
        scratch = Path(tempfile.mkdtemp(dir=self.work))
        overlay = scratch / "overlay"
        file = mutant.get("file", target["source"])
        for path in {file} if target.get("wrapper") else {file, target["source"]}:
            (overlay / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(self.src / path, overlay / path)
            (overlay / path).chmod(0o644)
        text = (overlay / file).read_text()
        if mutant["from"] not in text:
            return f"{mutant['name']}: changed nothing in {file}", None
        (overlay / file).write_text(text.replace(mutant["from"], mutant["to"], 1))
        for support in (self.work / "support").glob("*.olean"):
            shutil.copy(support, scratch)
        original = (self.work / f"{target['module']}.ll").read_text()
        try:
            self.generate(target, scratch, overlay)
        except RuntimeError as error:
            return f"{mutant['name']}: didn't compile: {str(error)[:2000]}", None
        if strip_paths(original) == strip_paths((scratch / f"{target['module']}.ll").read_text()):
            return f"{mutant['name']}: the bug didn't change the IR", None
        proof = PROOFS / f"{target['proof']}.lean"
        checked = proof
        if len(target["functions"]) > 1:
            # Only errors in the theorem's own lines count below, and Lean reads a file in order, so nothing
            # after them can change what it says about them. That part of the file isn't checked.
            text = proof.read_text()
            _, last = theorem_lines(text, theorem)
            if ends_command(text.splitlines(), last):
                checked = scratch / "proof" / proof.name
                checked.parent.mkdir()
                checked.write_text("".join(text.splitlines(keepends=True)[:last]))
        result = self.lean_ran(scratch, str(checked))
        if result.limit is not None:
            return f"{mutant['name']}: unknown, since the proof neither passed nor failed in time", None
        shutil.rmtree(scratch)
        errors = [
            (int(m.group(1)), line)
            for line in result.out.splitlines()
            if (m := LEAN_ERROR.match(line)) and not (m.group(1) == "1" and m.group(2) == "0")
        ]
        if result.exit == 0:
            return f"{mutant['name']}: the proof still checks", None
        if not errors:
            output = result.out[:2000]
            return f"{mutant['name']}: unknown, since Lean failed with no error in the proof: {output}", None
        # With one function in the file, its helpers count too. With several, each stops its own theorem.
        if len(target["functions"]) > 1:
            first, last = theorem_lines(proof.read_text(), theorem)
            errors = [(line, text) for line, text in errors if first <= line <= last]
            if not errors:
                return f"{mutant['name']}: stopped the proof, but not of {theorem}", None
        # Running out of time, memory or stack says the proof might check with more. Lean goes on to the next
        # declaration after one, with the one that failed still there for the rest to use, so another error is
        # the bug's.
        own = [text for _, text in errors if not LIMIT.search(text)]
        if not own:
            return (
                f"{mutant['name']}: unknown, since the proof only ran out of resources: {errors[0][1][:500]}",
                None,
            )
        finding = re.sub(r"^.*?:\d+:\d+: error(\([^)]*\))?: ", "", own[0]).strip()[:300]
        caught = core.decide(
            core.Verdict.CAUGHT, core.Evidence(step=core.Step.of("lean", result), finding=finding)
        )
        if not caught.granted:
            return f"{mutant['name']}: {caught.verdict}, since {caught.detail}", None
        return None, finding


def check_target(pipeline: Pipeline, target: dict[str, Any], mutants: bool) -> dict[str, Any]:
    """Runs one target, and returns its manifest entry. `failures` is empty if every function counts."""
    work = pipeline.work
    entry: dict[str, Any] = {
        "module": target["module"],
        "source": target["source"],
        "source_sha256": sha256(pipeline.source_path(target, None)),
        "flags": target["flags"],
        "extra_flags": target.get("args", []),
        "failures": [],
        "functions": {},
    }
    started = time.monotonic()
    try:
        translated = pipeline.generate(target, work)
        entry["ir_sha256"] = sha256(work / f"{target['module']}.ll")
        entry["lean_sha256"] = sha256(work / f"{target['module']}.lean")
        proof = PROOFS / f"{target['proof']}.lean"
        entry["proof_sha256"] = sha256(proof)
        compiled = pipeline.compile_ran(work, proof, PROOFS)
        checked(compiled)
        # Each theorem has to be about its function, as ir-lean generated it. One left out can't be proved
        # about, and a proof could define something of its own with the generated module's name.
        theorems = []
        for function, details in target["functions"].items():
            symbol = details.get("symbol", function)
            ok, name = translated.get(symbol, (False, f"there's no @{symbol} in the IR"))
            if not ok:
                entry["failures"].append(f"ir-lean left out {function}: {name}")
            else:
                theorems.append(f"{details['theorem']} {target['module']}.{name}")
        if not entry["failures"]:
            entry["axioms"], proved = pipeline.proved(
                work, compiled, target["proof"], target["module"], "\n".join(theorems)
            )
            if not proved.granted:
                entry["failures"].append(f"{target['proof']} isn't proved: {proved.detail}")
        for function, details in target["functions"].items():
            statement = pipeline.statement(work, target["proof"], details["theorem"])
            entry["functions"][function] = {k: v for k, v in details.items() if k != "mutants"} | {
                "statement": statement
            }
    except RuntimeError as error:
        entry["failures"].append(str(error)[:6000])
    entry["proof_seconds"] = round(time.monotonic() - started, 1)
    if mutants and not entry["failures"]:
        entry["mutants"] = []
        entry["mutants_stopped_by"] = {}
        checks: list[tuple[str, str, Future[tuple[str | None, str | None]]]] = []
        with ThreadPoolExecutor(int(os.environ.get("LEAN_JOBS", "4"))) as pool:
            for function, details in target["functions"].items():
                # A target with one function can list its bugs on the target.
                bugs = details.get("mutants", [])
                if len(target["functions"]) == 1:
                    bugs = bugs + target.get("mutants", [])
                if not bugs:
                    entry["failures"].append(f"{function} has no mutants")
                for mutant in bugs:
                    entry["mutants"].append(mutant["name"])
                    checks.append(
                        (
                            function,
                            mutant["name"],
                            pool.submit(pipeline.check_mutant, target, mutant, details["theorem"]),
                        )
                    )
        for function, name, check in checks:
            failure, stopped_by = check.result()
            if failure is not None:
                entry["failures"].append(f"{function}: {failure}")
            else:
                entry["mutants_stopped_by"][f"{function}: {name}"] = stopped_by
    return entry


def versions() -> dict[str, str]:
    def first_line(command: list[str]) -> str:
        return run(command).splitlines()[0]

    return {
        "clang": first_line(["clang", "--version"]),
        "llvm": first_line(["llvm-config", "--version"]),
        "lean": first_line(["lean", "--version"]),
    }


def emitter_commit() -> str:
    """The commit, and whether the tree has changes, since the emitter and the model are trusted."""
    try:
        commit = run(["git", "-C", str(ROOT), "rev-parse", "HEAD"]).strip()
        dirty = run(["git", "-C", str(ROOT), "status", "--porcelain", "src", "IRLean"]).strip()
    except (RuntimeError, FileNotFoundError):
        return "unknown"
    return commit + (" with local changes" if dirty else "")


def summarize(entries: list[dict[str, Any]], checked_mutants: bool) -> dict[str, Any]:
    """The score: what passed everything, and what kinds of functions those are."""
    proved = [(e, f, d) for e in entries if not e["failures"] for f, d in e["functions"].items()]
    projects: dict[str, int] = {}
    for entry, _, _ in proved:
        project = "llvm" if entry["source"].startswith("tests/") else entry["source"].split("/")[0]
        projects[project] = projects.get(project, 0) + 1
    return {
        "functions": len(proved),
        "hard": [f for _, f, d in proved if d.get("hard")],
        "loops": sum(1 for _, _, d in proved if d.get("loop")),
        "memory": sum(1 for _, _, d in proved if d.get("memory")),
        "projects": projects,
        "partial": {f: d["partial"] for _, f, d in proved if d.get("partial")},
        "mutants_checked": checked_mutants,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("tool", type=Path)
    parser.add_argument("--only", nargs="*", default=None, help="only these modules")
    parser.add_argument("--no-mutants", action="store_true")
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()

    config = tomllib.loads((PROOFS / "targets.toml").read_text())
    targets = config["target"]
    if args.only:
        targets = [t for t in targets if t["module"] in args.only]
    jobs = int(os.environ.get("LEAN_JOBS", "4"))

    found = versions()
    if config["project"]["tag"] != f"llvmorg-{found['llvm']}":
        print(f"FAIL  {config['project']['tag']} is pinned, but this shell has LLVM {found['llvm']}")
        return 1

    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        pipeline = Pipeline(args.tool.resolve(), work, config)
        # Proofs share these, and mutants copy them, so they come first. Each compiles once what it imports
        # from the others has, at the same time as any others that are ready.
        (work / "support").mkdir()
        support = config.get("support", [])
        compiled: set[str] = set()
        with ThreadPoolExecutor(jobs) as pool:
            while len(compiled) < len(support):
                ready = [
                    m
                    for m in support
                    if m not in compiled
                    and set(IMPORT.findall((PROOFS / f"{m}.lean").read_text())) & set(support) <= compiled
                ]
                if not ready:
                    print(f"FAIL  support modules {sorted(set(support) - compiled)} import each other")
                    return 1
                list(pool.map(lambda m: pipeline.compile_lean(work, PROOFS / f"{m}.lean", PROOFS), ready))
                compiled.update(ready)
        for module in support:
            shutil.copy(work / f"{module}.olean", work / "support")
        # Each proof's check reads the support modules' axioms, and this replays their declarations once.
        try:
            list(ThreadPoolExecutor(jobs).map(lambda m: pipeline.replay(work, m), support))
        except RuntimeError as error:
            print(f"FAIL  support modules: {str(error)[:4000]}")
            return 1
        with ThreadPoolExecutor(jobs) as pool:
            futures = [pool.submit(check_target, pipeline, target, not args.no_mutants) for target in targets]
            entries = [future.result() for future in futures]

    for entry in entries:
        if entry["failures"]:
            print(f"FAIL  {entry['module']}")
            for failure in entry["failures"]:
                print(f"      {failure}")
        else:
            count = len(entry.get("mutants", []))
            seconds = entry["proof_seconds"]
            print(f"ok    {entry['module']} ({seconds}s, {count} mutants, axioms: {entry['axioms']})")

    score = summarize(entries, not args.no_mutants)
    if args.manifest:
        manifest = {
            "llvm_project": {**config["project"], "store_path": os.environ["LLVM_PROJECT_SRC"]},
            "versions": found,
            "emitter": emitter_commit(),
            "flags": config["flags"],
            "proof_cflags": os.environ["PROOF_CFLAGS"],
            "score": score,
            "targets": entries,
        }
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    print(f"score: {json.dumps(score)}")
    return 1 if any(entry["failures"] for entry in entries) else 0


if __name__ == "__main__":
    sys.exit(main())
