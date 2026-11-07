#!/usr/bin/env python3
"""Proves real functions from llvm/llvm-project, from unmodified source, and writes down what it did.

For each target in tests/llvm/targets.toml, this compiles the pinned source with upstream's flags, translates
the IR to Lean, checks the proof against it, allows only known axioms, and makes sure each of the target's
injected bugs stops the proof from checking. The manifest records the hashes, versions, theorem statements and
assumptions. A function only counts toward the score when all of that passes.

usage: tests/llvm.py path/to/ir-lean [--only NAME ...] [--no-mutants] [--manifest FILE]
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from concurrent.futures import Future, ThreadPoolExecutor
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
PROOFS = ROOT / "tests" / "llvm"
LEAN_ERROR = re.compile(r"^.*?:(\d+):(\d+): error")
# A proof that runs away fails. It shouldn't take this long.
TIMEOUT_SECONDS = 600


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], env: dict[str, str] | None = None, stdin: str | None = None) -> str:
    """Runs a command, and raises with its output if it fails."""
    try:
        result = subprocess.run(
            command,
            env=env,
            input=stdin,
            capture_output=True,
            text=True,
            timeout=TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"{' '.join(command)}\ntimed out") from error
    if result.returncode != 0:
        raise RuntimeError(f"{' '.join(command)}\n{result.stdout[:4000]}{result.stderr[:4000]}")
    return result.stdout


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
    while last < len(lines) and not re.match(r"(/--|theorem |def |end |namespace |section )", lines[last]):
        last += 1
    return first + 1, last


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

    def lean_env(self, directory: Path) -> dict[str, str]:
        return {**os.environ, "LEAN_PATH": f"{directory}:{ROOT}/.lake/build/lib/lean"}

    def lean(self, directory: Path, *args: str, stdin: str | None = None) -> str:
        return run(["lean", "-M", self.memory, *args], self.lean_env(directory), stdin)

    def compile_lean(self, directory: Path, source: Path, root: Path) -> None:
        olean = directory / (source.stem + ".olean")
        self.lean(directory, "-DwarningAsError=true", "-R", str(root), "-o", str(olean), str(source))

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

    def generate(self, target: dict[str, Any], directory: Path, overlay: Path | None = None) -> None:
        """Compiles a target's source, and translates and checks its Lean module."""
        name = target["module"]
        ll = directory / f"{name}.ll"
        generated = directory / f"{name}.lean"
        run(self.clang_command(target, overlay, ll))
        # Exit code 3 means some function was left out. A proof about it would fail.
        result = subprocess.run(
            [str(self.tool), str(ll), "--namespace", name, "-o", str(generated), "--no-code"],
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode not in (0, 3):
            raise RuntimeError(f"ir-lean {ll}: {result.stderr[:4000]}")
        self.lean(directory, "-R", str(directory), "-o", str(directory / f"{name}.olean"), str(generated))

    def axioms(self, directory: Path, module: str) -> str:
        template = (ROOT / "tests" / "check_axioms.lean").read_text()
        return self.lean(directory, "--stdin", stdin=template.replace("MODULE", module)).strip()

    def statement(self, directory: Path, module: str, theorem: str) -> str:
        source = f"import {module}\nset_option pp.fullNames true\n#check @{theorem}\n"
        return self.lean(directory, "--stdin", stdin=source).strip()

    def check_mutant(self, target: dict[str, Any], mutant: dict[str, str], theorem: str) -> str | None:
        """Returns what went wrong, or None if the bug stopped the proof of `theorem`."""
        scratch = Path(tempfile.mkdtemp(dir=self.work))
        overlay = scratch / "overlay"
        file = mutant.get("file", target["source"])
        for path in {file} if target.get("wrapper") else {file, target["source"]}:
            (overlay / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(self.src / path, overlay / path)
            (overlay / path).chmod(0o644)
        text = (overlay / file).read_text()
        if mutant["from"] not in text:
            return f"{mutant['name']}: changed nothing in {file}"
        (overlay / file).write_text(text.replace(mutant["from"], mutant["to"], 1))
        for support in (self.work / "support").glob("*.olean"):
            shutil.copy(support, scratch)
        original = (self.work / f"{target['module']}.ll").read_text()
        try:
            self.generate(target, scratch, overlay)
        except RuntimeError as error:
            return f"{mutant['name']}: didn't compile: {str(error)[:2000]}"
        if strip_paths(original) == strip_paths((scratch / f"{target['module']}.ll").read_text()):
            return f"{mutant['name']}: the bug didn't change the IR"
        proof = PROOFS / f"{target['proof']}.lean"
        try:
            result = subprocess.run(
                ["lean", "-M", self.memory, str(proof)],
                env=self.lean_env(scratch),
                capture_output=True,
                text=True,
                timeout=TIMEOUT_SECONDS,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return f"{mutant['name']}: the proof neither passed nor failed in time"
        shutil.rmtree(scratch)
        errors = [
            int(m.group(1))
            for line in result.stdout.splitlines()
            if (m := LEAN_ERROR.match(line)) and not (m.group(1) == "1" and m.group(2) == "0")
        ]
        if result.returncode == 0:
            return f"{mutant['name']}: the proof still checks"
        if not errors:
            return f"{mutant['name']}: failed with no error in the proof: {result.stdout[:2000]}"
        # With one function in the file, its helpers count too. With several, each stops its own theorem.
        if len(target["functions"]) > 1:
            first, last = theorem_lines(proof.read_text(), theorem)
            if not any(first <= line <= last for line in errors):
                return f"{mutant['name']}: stopped the proof, but not of {theorem}, at lines {errors[:10]}"
        return None


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
        pipeline.generate(target, work)
        entry["ir_sha256"] = sha256(work / f"{target['module']}.ll")
        entry["lean_sha256"] = sha256(work / f"{target['module']}.lean")
        proof = PROOFS / f"{target['proof']}.lean"
        entry["proof_sha256"] = sha256(proof)
        pipeline.compile_lean(work, proof, PROOFS)
        entry["axioms"] = pipeline.axioms(work, target["proof"])
        for function, details in target["functions"].items():
            statement = pipeline.statement(work, target["proof"], details["theorem"])
            entry["functions"][function] = {k: v for k, v in details.items() if k != "mutants"} | {
                "statement": statement
            }
            if f"{target['module']}." not in statement:
                entry["failures"].append(
                    f"{details['theorem']} doesn't mention anything in {target['module']}"
                )
    except RuntimeError as error:
        entry["failures"].append(str(error)[:6000])
    entry["proof_seconds"] = round(time.monotonic() - started, 1)
    if mutants and not entry["failures"]:
        entry["mutants"] = []
        checks: list[tuple[str, Future[str | None]]] = []
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
                        (function, pool.submit(pipeline.check_mutant, target, mutant, details["theorem"]))
                    )
        for function, check in checks:
            failure = check.result()
            if failure is not None:
                entry["failures"].append(f"{function}: {failure}")
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
        # Proofs share these, and mutants copy them, so they come first.
        (work / "support").mkdir()
        for module in config.get("support", []):
            pipeline.compile_lean(work, PROOFS / f"{module}.lean", PROOFS)
            shutil.copy(work / f"{module}.olean", work / "support")
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
