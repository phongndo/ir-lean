#!/usr/bin/env python3
"""Times a candidate against the baseline on one workload of the kernel corpus, by docs/kernels.md's
protocol, and reads sessions of that by its rule. docs/kernels.md, "The harness".

A variant is a build of the project: a directory, which fills the manifest's `{build}`, and environment
variables added to everything it runs. A session:

1. Reads the workload from the manifest, and nowhere else: its `build`, `setup` and `run`, what's measured,
   its thread count and its checks.
2. Runs the workload's `build` for each variant, then finds what each variant's timed program loads, with
   `ldd` under that variant's environment, and hashes the program and every library. That's the variant's
   identity. Two variants with the same identity are a control, and have to be declared one.
3. Runs the workload's `setup` for each, and its checks: the project's test against known answers, on the
   candidate, or what a check's own run writes, hashed, the candidate's against the baseline's.
4. Warms each variant once, pinned as the timed runs are. For a time, the warm-up says how often a run
   repeats to last the rule's 2 seconds.
5. Times the pairs, baseline and candidate back to back in an order drawn from the seed, pinned to the cores
   given. Where a check hashes what the workload's own run writes, every timed run's is hashed and compared.
6. Hashes what each variant loads again, and writes one numbered record beside the others of the same
   workload and pair of identities.

A run that crashes, is killed, hits its time limit or exits non-zero, in any step, fails the session: its
record says `failed`, with why, and has no pair. `read` pools every confirmation session of one directory
and applies the rule, each figure of a rate on its own. Every run those sessions planned has to be there, so
one that failed leaves the reading inconclusive.

`faster` here is the rule's "measurably faster" on one workload. It isn't a win, which also needs a proof
and a review, as docs/kernels.md's "What a win is" says.

usage: bench/kernels/timing.py session PROJECT WORKLOAD --baseline BUILD --candidate BUILD --cpus LIST
                                       --seed N --sessions DIR [--kind exploratory|confirmation] [--control]
                                       [--pairs N] [--inputs DIR] [--work DIR]
                                       [--baseline-env NAME=VALUE]... [--candidate-env NAME=VALUE]...
       bench/kernels/timing.py read DIR [--other DIR]...

`session` exits 0 for a complete session, 1 for a failed one, whose record it still writes, and 5 for one it
won't run. `read` asks irlean.verdict what the sessions come to, and exits 0 for `faster`, 2 for `slower`,
3 for `inconclusive`, 4 for a control, which is none of those, 1 for an error, and 5 if it couldn't read
them.
"""

from __future__ import annotations

import argparse
import csv
import io
import itertools
import json
import math
import os
import random
import re
import shutil
import sys
import tempfile
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
import kernels  # noqa: E402
import protocol  # noqa: E402
from irlean import hashing, proc, schemas, verdict  # noqa: E402

# Stock clang: without the hardening and frame pointers the dev shell's wrapper adds, and with -march=native
# left alone, as bench/kernels/profile.sh and tests/llama_bench.py have it.
STOCK = {"NIX_ENFORCE_NO_NATIVE": "0", "NIX_HARDENING_ENABLE": "", "CC": "clang", "CXX": "clang++"}
# What of this process's environment a command gets: where programs are, and what Nix's compiler wrappers
# read. Nothing else is inherited, so a `MAKEFLAGS=n` in the caller's shell can't make a check a dry run, and
# an `LD_PRELOAD` or `LD_LIBRARY_PATH` there can't change what a variant loads.
INHERITED = ("PATH", "HOME", "USER", "LANG", "TMPDIR", "TERM")
INHERITED_PREFIXES = ("NIX_", "LC_")
VARIANTS = ("baseline", "candidate")
COMPLETE, FAILED = "complete", "failed"
# What ldd prints for a library it found, and for what has no file to find: the vDSO, or the loader by path.
RESOLVED = re.compile(r"\t(\S+) => (\S+) \(0x[0-9a-f]+\)")
UNSOUGHT = re.compile(r"\t(\S+) \(0x[0-9a-f]+\)")
ASSIGNMENT = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)=(.*)", re.S)
CPUS = re.compile(r"\d+(-\d+)?(,\d+(-\d+)?)*")
# A step that isn't timed gets this long. A timed run gets the longer of this and 20 warm-ups.
STEP_SECONDS = 3600.0
RUN_SECONDS = 600.0


class Refused(Exception):
    """What was asked can't be run as a session at all. Nothing is recorded."""


class Failed(Exception):
    """A session that ran and can't count. Its record says why."""


@dataclass(frozen=True)
class Variant:
    build: Path
    env: dict[str, str] = field(default_factory=dict)


def llama_bench(stdout: bytes) -> dict[str, float]:
    """`avg_ts`, tokens a second, in the last row of the CSV `llama-bench -o csv` prints."""
    rows = list(csv.DictReader(io.StringIO(stdout.decode())))
    if not rows or not rows[-1].get("avg_ts"):
        raise Failed("llama-bench printed no CSV row with avg_ts")
    return {"avg_ts": float(rows[-1]["avg_ts"])}


# How a workload's rate is read from what its run prints. The manifest says what the figure is, in prose, so
# a rate with no reader here is refused, not guessed at.
RATES: dict[tuple[str, str], Callable[[bytes], dict[str, float]]] = {
    ("llama.cpp", "pp512"): llama_bench,
    ("llama.cpp", "tg128"): llama_bench,
}


def cpu_list(text: str) -> list[int]:
    if not CPUS.fullmatch(text):
        raise Refused(f"--cpus {text!r} isn't a list such as 12 or 8-15")
    out: set[int] = set()
    for part in text.split(","):
        low, _, high = part.partition("-")
        out |= set(range(int(low), int(high or low) + 1))
    missing = sorted(out - os.sched_getaffinity(0))
    if missing:
        raise Refused(f"this process can't run on cpus {missing}")
    return sorted(out)


def topology(cpus: list[int]) -> dict[str, dict[str, str]]:
    """Each cpu's hyperthread siblings and the cpus it shares its last-level cache with, where /sys says."""
    out = {}
    for c in cpus:
        base = Path(f"/sys/devices/system/cpu/cpu{c}")
        found = {}
        for key, path in (
            ("siblings", "topology/thread_siblings_list"),
            ("l3", "cache/index3/shared_cpu_list"),
        ):
            if (base / path).is_file():
                found[key] = (base / path).read_text().strip()
        out[str(c)] = found
    return out


def split_env(command: list[str]) -> tuple[dict[str, str], list[str]]:
    """A command's own environment, and the program it runs with its arguments. A command is PROGRAM ARG...
    or `env NAME=VALUE... PROGRAM ARG...`, and nothing else `env` takes, an option among them, since what
    it would run then isn't what this reads."""
    if command[0] != "env":
        return {}, command
    env: dict[str, str] = {}
    rest = command[1:]
    while rest and (m := ASSIGNMENT.fullmatch(rest[0])):
        env[m[1]] = m[2]
        rest = rest[1:]
    if not rest or rest[0].startswith("-"):
        raise Refused(f"a command through env is `env NAME=VALUE... PROGRAM ARG...`, not {command}")
    return env, rest


def loaded(program: Path, env: dict[str, str], cwd: Path) -> list[dict[str, str]]:
    """The program and each library `ldd` says it loads under `env`, from `cwd`, where the timed command
    runs, so that a path that isn't absolute finds what the command finds. By name, path and SHA-256. A
    library the program opens while it runs isn't seen."""
    r = proc.run(["ldd", program], env=env, cwd=cwd, timeout=120)
    if not r.ok:
        raise Failed(f"ldd {program} ended with exit code {r.exit}: {r.output[-500:]}")
    found = [("program", program)]
    for line in r.out.splitlines():
        if line.strip() == "statically linked":
            continue
        if m := RESOLVED.fullmatch(line):
            # A path that isn't absolute is from where the command runs.
            found.append((m[1], cwd / m[2]))
        elif (m := UNSOUGHT.fullmatch(line)) and m[1].startswith("/"):
            found.append((Path(m[1]).name, Path(m[1])))
        elif not m:
            raise Failed(f"ldd {program} printed a line this doesn't read: {line!r}")
    return [{"name": n, "path": str(p), "sha256": hashing.sha256_file(p)} for n, p in found]


class Session:
    """One session's plan and what running it found. `run` returns the record, complete or failed."""

    def __init__(
        self,
        manifest: dict[str, Any],
        manifest_path: Path,
        project: str,
        workload: str,
        variants: dict[str, Variant],
        cpus: str,
        seed: int,
        pairs: int,
        kind: str,
        control: bool,
        work: Path,
        sessions: Path,
        inputs: Path | None = None,
        src: Path | None = None,
        rule: protocol.Rule = protocol.PROTOCOL,
    ) -> None:
        workloads = manifest.get("project", {}).get(project, {}).get("workload", [])
        found = next((w for w in workloads if w.get("name") == workload), None)
        if found is None:
            raise Refused(f"the manifest has no workload {workload} of {project}")
        self.w: dict[str, Any] = found
        if kind not in protocol.KINDS:
            raise Refused(f"a session is one of {', '.join(protocol.KINDS)}")
        if pairs < 1:
            raise Refused("a session has at least one pair")
        measure = self.w.get("measure")
        if measure not in protocol.MEASURES:
            raise Refused(f"{project} {workload} doesn't say what's measured")
        self.measure: str = measure
        self.reader = RATES.get((project, workload))
        if self.measure == protocol.RATE and self.reader is None:
            raise Refused(f"nothing here reads {project} {workload}'s rate: {self.w.get('rate')}")
        self.checks = self.w.get("check", [])
        if not self.checks:
            raise Refused(f"{project} {workload} has no check, so nothing says a candidate computes the same")
        self.project, self.workload, self.variants = project, workload, variants
        self.cpus, self.seed, self.pairs, self.kind, self.control = cpus, seed, pairs, kind, control
        self.cpu_ids = cpu_list(cpus)
        self.threads = self.w.get("threads", 1)
        if len(self.cpu_ids) < self.threads:
            raise Refused(
                f"{workload} runs {self.threads} threads, and --cpus {cpus} has {len(self.cpu_ids)}"
            )
        for name in VARIANTS:
            if not variants[name].build.is_dir():
                raise Refused(f"the {name}'s build, {variants[name].build}, isn't a directory")
        # Commands run in a variant's build, so every place they're given is absolute.
        self.rule, self.work, self.src = rule, work.absolute(), src
        self.inputs = None if inputs is None else inputs.absolute()
        self.sessions = sessions.absolute()
        self.manifest, self.manifest_path = manifest, manifest_path
        corpus = manifest_path.resolve() == kernels.MANIFEST.resolve()
        if corpus and (problems := kernels.validate(manifest)):
            raise Refused("the corpus's manifest doesn't meet its rules: " + "; ".join(problems[:3]))
        self.record: dict[str, Any] = {
            "schema": schemas.KERNELS_SESSION,
            "project": project,
            "workload": workload,
            "workloads": sorted(w["name"] for w in workloads),
            "kind": kind,
            "control": control,
            "seed": seed,
            "cpus": cpus,
            "topology": topology(self.cpu_ids),
            "threads": self.threads,
            "measure": self.measure,
            "rule": rule.as_record(),
            "manifest": {
                "sha256": hashing.sha256_file(manifest_path),
                "corpus": corpus and project in manifest.get("corpus", {}).get("approved", []),
            },
            "variants": {n: {"build": str(v.build.resolve()), "env": v.env} for n, v in variants.items()},
            "started": proc.now(),
            "status": FAILED,
            "planned_pairs": pairs,
            "pairs": [],
        }
        if len({t.get("l3") for t in self.record["topology"].values()}) > 1:
            raise Refused(f"--cpus {cpus} share no one last-level cache, and the protocol pins a run to one")
        self.out = {n: self.work / n for n in VARIANTS}
        self.repeat = 1

    # Places, environments and commands.

    def place(self, text: str, variant: str) -> str:
        """`text` with the manifest's places filled in for `variant`. {out} is one path for both variants,
        a link this points at the variant's own directory before each of its commands, so that nothing a run
        writes can differ only by where it was told to write."""

        def fill(m: re.Match[str]) -> str:
            kind, _, what = m[1].partition(":")
            if kind == "input":
                return str(self.input(what))
            if m[1] == "build":
                return str(self.variants[variant].build.resolve())
            if m[1] == "out":
                return str(self.work / "out")
            if m[1] == "repo":
                return str(ROOT)
            if m[1] == "src":
                if self.src is None:
                    self.src = kernels.source(self.project, self.manifest["project"][self.project])
                return str(self.src)
            raise Refused(f"{{{m[1]}}} in {text!r} names no place")

        return kernels.PLACEHOLDER.sub(fill, text)

    def input(self, name: str) -> Path:
        """One of the project's inputs, in --inputs: a file, of the SHA-256 the manifest pins, hashed when
        it's first named and again when the session ends. Anything else is refused: a directory, as an
        archive unpacked would be, has no hash here to hold it to."""
        if self.inputs is None or not (self.inputs / name).is_file():
            raise Refused(f"{{input:{name}}} needs --inputs, a directory holding the file {name}")
        path = self.inputs / name
        known = self.record.setdefault("inputs", {})
        if name not in known:
            declared = self.manifest["project"][self.project].get("input", [])
            want = next((i.get("sha256") for i in declared if i.get("name") == name), None)
            have = hashing.sha256_file(path)
            if want is None or have != want:
                raise Refused(f"{path} isn't the {name} the manifest pins: its SHA-256 is {have}, not {want}")
            known[name] = have
        return path

    def env(self, variant: str, own: dict[str, str] | None = None) -> dict[str, str]:
        both = set(self.variants[variant].env) & set(own or {})
        if both:
            raise Refused(f"the {variant}'s environment and the command's both set {sorted(both)}")
        inherited = {
            k: v for k, v in os.environ.items() if k in INHERITED or k.startswith(INHERITED_PREFIXES)
        }
        return {**inherited, **STOCK, **self.variants[variant].env, **(own or {})}

    def point(self, variant: str) -> None:
        link = self.work / "out"
        link.unlink(missing_ok=True)
        link.symlink_to(self.out[variant])

    def step(self, what: str, commands: list[list[str]], variant: str) -> list[proc.Ran]:
        """Runs commands that aren't timed, in the variant's build. Any that doesn't end well fails the
        session."""
        self.point(variant)
        ran = []
        for command in commands:
            argv = [self.place(a, variant) for a in command]
            r = proc.run(argv, env=self.env(variant), cwd=self.variants[variant].build, timeout=STEP_SECONDS)
            if not r.ok:
                raise Failed(
                    f"the {variant}'s {what} didn't end well: {' '.join(argv)[:300]} ended with exit code "
                    f"{r.exit}{', at its ' + r.limit if r.limit else ''}: {r.output[-800:]}"
                )
            ran.append(r)
        return ran

    def programs(self, variant: str) -> list[tuple[dict[str, str], list[str]]]:
        """Each command of the workload's `run` for `variant`: its own environment, and the program with its
        arguments. The program has to be in the variant's build, so that the variant decides what's timed."""
        out = []
        build = self.variants[variant].build.resolve()
        for command in self.w["run"]:
            own, argv = split_env([self.place(a, variant) for a in command])
            if not Path(argv[0]).resolve().is_relative_to(build):
                raise Refused(f"{self.workload} times {argv[0]}, which isn't in the {variant}'s build")
            out.append((own, argv))
        return out

    def identity(self, variant: str) -> dict[str, Any]:
        files = []
        for own, argv in self.programs(variant):
            files += loaded(Path(argv[0]).resolve(), self.env(variant, own), self.variants[variant].build)
        return {
            "loads": files,
            "id": hashing.sha256_text(json.dumps([[f["name"], f["sha256"]] for f in files])),
        }

    # Checks.

    def hashes(self, check: dict[str, Any], variant: str, stdout: bytes) -> dict[str, str]:
        out = {}
        for o in check["output"]:
            if o == "stdout":
                out[o] = hashing.sha256(stdout)
                continue
            path = Path(self.place(o, variant))
            if not path.is_file():
                raise Failed(f"the {variant} didn't write {o}")
            out[o] = hashing.sha256_file(path)
        if "sha256" in check and list(out.values()) != [check["sha256"]]:
            raise Failed(f"the {variant}'s output isn't the one the manifest knows: {out}")
        return out

    def clear(self, check: dict[str, Any], variant: str) -> None:
        """Removes the files a check hashes, before the commands that write them, so that one left by an
        earlier run can't stand in for one this run didn't write."""
        self.point(variant)
        for o in check["output"]:
            if o != "stdout":
                Path(self.place(o, variant)).unlink(missing_ok=True)

    def check(self) -> list[dict[str, Any]]:
        """Runs each check that has commands of its own, and returns what each found. A check with none is
        about what the workload's own run writes, which `timed` hashes on every run."""
        found = []
        for n, c in enumerate(self.checks, 1):
            entry: dict[str, Any] = {"check": n, "kind": c.get("kind")}
            if c.get("kind") == "known-answers":
                self.step(f"check {n}, the project's test", c["run"], "candidate")
                entry["candidate"] = "passed"
            elif c.get("kind") == "output" and "run" in c:
                for variant in VARIANTS:
                    self.clear(c, variant)
                    ran = self.step(f"check {n}", c["run"], variant)
                    entry[variant] = self.hashes(c, variant, b"".join(r.stdout for r in ran))
                if entry["baseline"] != entry["candidate"]:
                    raise Failed(f"check {n}: the candidate's output isn't the baseline's: {entry}")
            elif c.get("kind") == "output":
                entry["on"] = "every timed run"
            else:
                raise Refused(f"check {n} is of a kind this doesn't run: {c.get('kind')!r}")
            found.append(entry)
        return found

    # Timing.

    def timed(self, variant: str, limit: float) -> dict[str, Any]:
        """One run of `variant`: the workload's commands, `self.repeat` times over, pinned. What it measures
        is the wall time of all of it, or the rate its last repetition printed. Where a check is about what
        the workload's own run writes, each repetition's is hashed, and they have to be the same."""
        self.point(variant)
        own_output = [c for c in self.checks if c.get("kind") == "output" and "run" not in c]
        seconds = user = system = 0.0
        stdout = b""
        output = None
        for _ in range(self.repeat):
            stdout = b""
            for c in own_output:
                self.clear(c, variant)
            for own, argv in self.programs(variant):
                r = proc.run(
                    ["taskset", "-c", self.cpus, *argv],
                    env=self.env(variant, own),
                    cwd=self.variants[variant].build,
                    timeout=limit,
                )
                if not r.ok:
                    raise Failed(
                        f"a run of the {variant} didn't end well: exit code {r.exit}"
                        f"{', at its ' + r.limit if r.limit else ''}: {r.output[-800:]}"
                    )
                seconds, user, system = seconds + r.seconds, user + r.user_s, system + r.sys_s
                stdout += r.stdout
            wrote = [self.hashes(c, variant, stdout) for c in own_output]
            if output is not None and wrote != output:
                raise Failed(f"two repetitions of one run of the {variant} wrote different things")
            output = wrote
        figures = {"seconds": seconds} if self.reader is None else self.reader(stdout)
        for name, value in figures.items():
            if type(value) is not float or not math.isfinite(value) or value <= 0:
                raise Failed(f"a run of the {variant} measured {name} as {value!r}, which no time or rate is")
        run: dict[str, Any] = {
            "exit": r.exit,
            "limit": r.limit,
            "figures": figures,
            "seconds": seconds,
            "user_s": user,
            "sys_s": system,
            "load1": os.getloadavg()[0],
        }
        if own_output:
            run["output"] = output
        return run

    def body(self) -> None:
        record = self.record
        # Where its record goes is known before anything runs, so its seed is checked against the others
        # there first.
        where = directory(self.sessions, record)
        if where.is_dir() and any(r["seed"] == self.seed for _, r in records(where)):
            raise Refused(f"seed {self.seed} was used by another session in {where}")
        for variant in VARIANTS:
            self.out[variant].mkdir(parents=True)
            self.step("build", self.w.get("build", []), variant)
        before = {v: self.identity(v) for v in VARIANTS}
        for v in VARIANTS:
            record["variants"][v]["identity"] = before[v]
        builds = {v: self.variants[v].build.resolve() for v in VARIANTS}
        if builds["baseline"] != builds["candidate"]:
            # Two builds: neither may load a file of the other's, whatever else of it differs.
            for v, other in (("baseline", "candidate"), ("candidate", "baseline")):
                for f in before[v]["loads"]:
                    if Path(f["path"]).resolve().is_relative_to(builds[other]):
                        raise Failed(f"the {v} loads {f['path']}, which is in the {other}'s build")
        same = before["baseline"]["id"] == before["candidate"]["id"]
        if same and not self.control:
            raise Failed(
                "the candidate loads what the baseline loads, byte for byte, and this isn't a control"
            )
        if self.control and not same:
            raise Failed("a control's two variants load the same bytes, and these differ")
        for variant in VARIANTS:
            self.step("setup", self.w.get("setup", []), variant)
        record["checks"] = self.check()
        warm = {v: self.timed(v, RUN_SECONDS) for v in VARIANTS}
        record["warm_up"] = warm
        reference = warm["baseline"].get("output")
        if warm["candidate"].get("output") != reference:
            raise Failed("the candidate's warm-up didn't write what the baseline's did")
        shortest = min(w["seconds"] for w in warm.values())
        # A fifth more than the warm-up says the minimum needs, since a later run can be quicker.
        if self.measure == protocol.TIME and 0 < shortest < 1.2 * self.rule.min_seconds:
            self.repeat = math.ceil(1.2 * self.rule.min_seconds / shortest)
        record["repeat"] = self.repeat
        limit = max(RUN_SECONDS, 20 * self.repeat * max(w["seconds"] for w in warm.values()))
        rng = random.Random(self.seed)
        pairs = []
        for n in range(1, self.pairs + 1):
            order = rng.sample(VARIANTS, 2)
            runs = {v: self.timed(v, limit) for v in order}
            for v in VARIANTS:
                if runs[v].get("output") != reference:
                    raise Failed(f"pair {n}: the {v} didn't write what the baseline's warm-up did")
                if self.measure == protocol.TIME and runs[v]["seconds"] < self.rule.min_seconds:
                    raise Failed(
                        f"pair {n}: a run of the {v} took {runs[v]['seconds']:.3f} s, under the rule's "
                        f"{self.rule.min_seconds} s"
                    )
            ratios = {
                f: protocol.ratio(
                    runs["baseline"]["figures"][f], runs["candidate"]["figures"][f], self.measure
                )
                for f in runs["baseline"]["figures"]
            }
            pairs.append({"pair": n, "order": order, **runs, "ratios": ratios})
        for v in VARIANTS:
            if self.identity(v)["id"] != before[v]["id"]:
                raise Failed(f"what the {v} loads changed while the session ran")
        for name, sha256 in record.get("inputs", {}).items():
            if self.inputs is None or hashing.sha256_file(self.inputs / name) != sha256:
                raise Failed(f"the input {name} changed while the session ran")
        # Only now does the record get its pairs, so a session that failed anywhere above has none.
        record["pairs"] = pairs
        record["status"] = COMPLETE

    def run(self) -> dict[str, Any]:
        try:
            self.body()
        except Refused:
            raise
        except Failed as failure:
            self.record["failure"] = str(failure)
        except Exception as error:
            # Whatever else stops it, a program that can't start or a figure that isn't a number among
            # them: a session that began has a record, and it says failed.
            self.record["failure"] = f"the session stopped on {type(error).__name__}: {error}"
        self.record["ended"] = proc.now()
        return self.record


def comparison(record: dict[str, Any]) -> list[Any]:
    """What a session compares: a workload of a project, between two builds, each with its environment."""
    variants = [[record["variants"][v]["build"], record["variants"][v]["env"]] for v in VARIANTS]
    return [record["project"], record["workload"], *variants]


def directory(sessions: Path, record: dict[str, Any]) -> Path:
    """Where a session's record goes: one directory for each comparison. That's known before anything runs,
    so every session of it is beside the others, however early it failed."""
    name = hashing.sha256_text(json.dumps(comparison(record), sort_keys=True))[:16]
    return sessions / record["project"] / record["workload"] / name


def records(where: Path) -> list[tuple[Path, dict[str, Any]]]:
    return [(p, schemas.read(p, schemas.KERNELS_SESSION)) for p in sorted(where.glob("*.json"))]


def write(sessions: Path, record: dict[str, Any]) -> Path:
    """Writes the record under the next number its directory doesn't have, never over another."""
    where = directory(sessions, record)
    where.mkdir(parents=True, exist_ok=True)
    text = schemas.dumps(record, schemas.KERNELS_SESSION, indent=1) + "\n"
    for n in itertools.count(1):
        try:
            with open(where / f"{n:03d}.json", "x") as f:
                f.write(text)
            return where / f"{n:03d}.json"
        except FileExistsError:
            continue
    raise AssertionError


def session(plan: Session) -> tuple[Path, dict[str, Any]]:
    """Runs a session and writes its record, complete or failed."""
    record = plan.run()
    return write(plan.sessions, record), record


def pooled_seed(seeds: list[int]) -> int:
    """The bootstrap's seed, from the sessions' own, so it isn't something to choose."""
    return int(hashing.sha256_text(json.dumps(sorted(seeds)))[:12], 16)


# What `read` asks irlean.verdict for, and each reason it gives, with its status and the exit code that ends
# with: irlean.verdict.status's table. A grant's word and exit code are its grant's.
ASKED = ("timing.faster", "timing.slower")
TABLE = {
    **{name: (verdict.GRANTS[name].word, verdict.GRANTS[name].exit) for name in ASKED},
    "not_shown": ("inconclusive", 3),
    "control": ("control", 4),
    "denied": ("error", 1),
    verdict.INTERNAL: ("error", 1),
}
REFUSED_EXIT = 5
# What the complete sessions of one directory have to share, besides what they compare and what each variant
# loads.
SHARED = ("workloads", "cpus", "topology", "threads", "measure", "rule", "manifest", "control")


class Sessions:
    """The sessions of one directory, as `read` takes them. Raises Refused if they aren't of one comparison,
    if the complete ones measured it differently, or if two used one seed."""

    def __init__(self, where: Path) -> None:
        found = records(where)
        if not found:
            raise Refused(f"{where} has no session")
        first = found[0][1]
        for path, r in found:
            if comparison(r) != comparison(first):
                raise Refused(f"{path} and {found[0][0].name} measured different things: what they compare")
        complete = [(path, r) for path, r in found if r["status"] == COMPLETE]
        if not complete:
            why = "; ".join(str(r.get("failure", ""))[:200] for _, r in found)
            raise Refused(f"{where} has no complete session: {why}")
        self.where = where
        self.project, self.workload = first["project"], first["workload"]
        self.builds = {v: first["variants"][v]["build"] for v in VARIANTS}
        self.shared = {k: complete[0][1][k] for k in SHARED}
        loads = {v: complete[0][1]["variants"][v]["identity"]["id"] for v in VARIANTS}
        for path, r in complete:
            differs = [k for k in SHARED if r[k] != self.shared[k]]
            differs += [
                f"what the {v} loads" for v in VARIANTS if r["variants"][v]["identity"]["id"] != loads[v]
            ]
            if differs:
                raise Refused(f"{path} and {complete[0][0].name} measured different things: {differs}")
        seeds = [r["seed"] for _, r in found]
        if len(set(seeds)) != len(seeds):
            raise Refused(f"two sessions in {where} used one seed")
        # Every confirmation session counts, a failed one too: what it planned and didn't time is missing.
        self.counted: list[dict[str, Any]] = [
            {"session": path.name, **r} for path, r in found if r["kind"] == protocol.CONFIRMATION
        ]
        self.left: list[dict[str, str]] = [
            {"session": path.name, "why": "exploratory: only confirmation sessions count"}
            for path, r in found
            if r["kind"] != protocol.CONFIRMATION
        ]
        self.timed: list[dict[str, Any]] = [s for s in self.counted if s["status"] == COMPLETE]
        self.whole = len(self.timed) == len(self.counted)

    def ratios(self) -> dict[str, list[list[float]]]:
        """Each figure's paired ratios, session by session, of the complete confirmation sessions, worked
        out again from what each run measured: a record's own `ratios` aren't read. Raises Refused if two
        runs measured different figures, or one measured what no time or rate is."""
        out: dict[str, list[list[float]]] = {}
        names: list[str] | None = None
        for s in self.timed:
            each: dict[str, list[float]] = {}
            for pair in s["pairs"]:
                figures = [pair[v]["figures"] for v in VARIANTS]
                names = sorted(figures[0]) if names is None else names
                if any(sorted(f) != names for f in figures):
                    raise Refused(f"{self.where}/{s['session']}: its runs didn't all measure {names}")
                for name in names:
                    try:
                        ratio = protocol.ratio(figures[0][name], figures[1][name], self.shared["measure"])
                    except (TypeError, ValueError) as error:
                        raise Refused(f"{self.where}/{s['session']}, pair {pair['pair']}: {error}") from error
                    each.setdefault(name, []).append(ratio)
            for name, values in each.items():
                out.setdefault(name, []).append(values)
        return out

    def seed(self) -> int:
        return pooled_seed([s["seed"] for s in self.timed])

    def pooled(self, rule: protocol.Rule) -> dict[str, dict[str, Any]]:
        return {
            f: protocol.summary([r for s in each for r in s], self.seed(), rule)
            for f, each in self.ratios().items()
        }

    def runs(self) -> tuple[list[str], list[verdict.Step]]:
        """Every timed run the confirmation sessions planned, and each a complete one recorded, as
        irlean.verdict takes cases: a run is named by its workload, session, pair and variant, and its exit
        code is its last command's. A failed session's runs aren't evidence, only its plan is."""
        planned, observed = [], []
        for s in self.counted:
            at = f"{self.workload}/{s['session']}"
            planned += [f"{at}:{n}:{v}" for n in range(1, s["planned_pairs"] + 1) for v in VARIANTS]
            if s["status"] == COMPLETE:
                observed += [
                    verdict.Step(f"{at}:{pair['pair']}:{v}", pair[v]["exit"], pair[v]["limit"])
                    for pair in s["pairs"]
                    for v in VARIANTS
                ]
        return planned, observed


def read(where: Path, others: list[Path]) -> dict[str, Any]:
    """Reads one directory of sessions by the rule. `others` are the directories of the project's other
    workloads, for the rule's fourth condition, one each, of the same two builds. They're held to what the
    workload's own are: their runs are cases too, and their manifest and rule have to be the protocol's.
    What the reading comes to is irlean.verdict's to say."""
    mine = Sessions(where)
    shared = mine.shared
    rule = protocol.Rule(**shared["rule"])
    reading: dict[str, Any] = {
        "schema": schemas.KERNELS_READING,
        "project": mine.project,
        "workload": mine.workload,
        **{k: shared[k] for k in ("measure", "cpus", "threads", "control")},
        "sessions": [{"session": s["session"], "status": s["status"]} for s in mine.counted],
        "left_out": mine.left,
    }

    def say(decision: verdict.Decision | None, reason: str, why: str = "") -> dict[str, Any]:
        reading["status"], reading["reason"], reading["exit_code"] = verdict.status(decision, TABLE, reason)
        if why:
            reading["why"] = why
        return reading

    by_figure = mine.ratios()
    if not by_figure:
        return say(None, "not_shown", "no complete confirmation session")
    if shared["control"]:
        pooled = mine.pooled(rule)
        reading["pooled"] = pooled
        # A control with a confirmation session that failed isn't whole, and says nothing.
        reading["control_contains_one"] = mine.whole and all(
            p["interval"][0] <= 1 <= p["interval"][1] for p in pooled.values()
        )
        return say(None, "control", "" if mine.whole else "a confirmation session of it failed")
    live = hashing.sha256_file(kernels.MANIFEST)
    # A comparison that isn't by the protocol is never shown faster or slower: the corpus's manifest as it
    # is now, an approved project, and the protocol's own rule, for the workload and for each of the others.
    corpus = bool(shared["manifest"]["corpus"]) and shared["manifest"]["sha256"] == live
    protocols = rule == protocol.PROTOCOL
    # The project's workloads are the manifest's, where that's the corpus's as it is now. A record's own
    # list is read only for a manifest this can't see, and then nothing is by the protocol.
    names = shared["workloads"]
    if corpus:
        names = sorted(w["name"] for w in kernels.load()["project"][mine.project]["workload"])
    measured: dict[str, list[float] | None] = {w: None for w in names if w != mine.workload}
    planned, observed = mine.runs()
    for other in others:
        theirs = Sessions(other)
        if theirs.project != mine.project or theirs.builds != mine.builds or theirs.shared["control"]:
            raise Refused(f"{other} isn't sessions of the same two builds of {mine.project}")
        if theirs.workload not in measured:
            raise Refused(f"{other} has no confirmation session of another workload of {mine.project}")
        if measured[theirs.workload] is not None:
            raise Refused(f"{other} is a second directory of {theirs.workload}'s sessions")
        ends = [p["interval"] for p in theirs.pooled(protocol.Rule(**theirs.shared["rule"])).values()]
        if not ends:
            raise Refused(f"{other} has no confirmation session of another workload of {mine.project}")
        # A workload with several figures is slower if any of them is: its lowest upper end is what counts.
        measured[theirs.workload] = min(ends, key=lambda i: i[1])
        more = theirs.runs()
        planned, observed = planned + more[0], observed + more[1]
        corpus = corpus and theirs.shared["manifest"] == shared["manifest"]
        protocols = protocols and theirs.shared["rule"] == shared["rule"]
    kinds = [s["kind"] for s in mine.timed]
    found = protocol.conditions(by_figure, kinds, mine.seed(), measured, rule)
    reading["result"] = found
    checks = {name: c["held"] for name, c in found["conditions"].items()}
    checks["corpus"], checks["rule"] = corpus, protocols
    evidence = verdict.Evidence(
        plan=verdict.Plan(tuple(planned), whole=True), cases=tuple(observed), checks=checks
    )
    # Asked by name, each as a literal, which tests/verdict_test.py counts: nothing here picks a grant.
    decisions = {
        "timing.faster": verdict.decide("timing.faster", evidence),
        "timing.slower": verdict.decide("timing.slower", evidence),
    }
    reading["decisions"] = {n: {"reason": d.reason, "detail": d.detail} for n, d in decisions.items()}
    for name, decision in decisions.items():
        if decision.granted:
            return say(decision, name)
    if any(d.reason == "denied" for d in decisions.values()):
        return say(None, "denied")
    return say(None, "not_shown", "; ".join(f"{n}: {d.reason}" for n, d in decisions.items()))


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    s = sub.add_parser("session")
    s.add_argument("project")
    s.add_argument("workload")
    for name in VARIANTS:
        s.add_argument(f"--{name}", type=Path, required=True, metavar="BUILD")
        s.add_argument(f"--{name}-env", action="append", default=[], metavar="NAME=VALUE")
    s.add_argument("--cpus", required=True)
    s.add_argument("--seed", type=int, required=True)
    s.add_argument("--sessions", type=Path, required=True)
    s.add_argument("--kind", choices=protocol.KINDS, default=protocol.EXPLORATORY)
    s.add_argument("--control", action="store_true")
    s.add_argument("--pairs", type=int, default=15)
    s.add_argument("--inputs", type=Path)
    s.add_argument("--work", type=Path, default=ROOT / "build" / "kernels" / "timing")
    r = sub.add_parser("read")
    r.add_argument("directory", type=Path)
    r.add_argument("--other", type=Path, action="append", default=[])
    args = parser.parse_args(argv)
    try:
        if args.command == "read":
            reading = read(args.directory, args.other)
            print(schemas.dumps(reading, schemas.KERNELS_READING, indent=1))
            return int(reading["exit_code"])
        variants = {}
        for name in VARIANTS:
            env = {}
            for text in getattr(args, f"{name}_env"):
                if not (m := ASSIGNMENT.fullmatch(text)):
                    raise Refused(f"--{name}-env {text!r} isn't NAME=VALUE")
                env[m[1]] = m[2]
            variants[name] = Variant(getattr(args, name), env)
        args.work.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="session-", dir=args.work))
        try:
            plan = Session(
                kernels.load(),
                kernels.MANIFEST,
                args.project,
                args.workload,
                variants,
                args.cpus,
                args.seed,
                args.pairs,
                args.kind,
                args.control,
                work,
                args.sessions,
                args.inputs,
            )
            path, record = session(plan)
        finally:
            shutil.rmtree(work, ignore_errors=True)
    except Refused as refusal:
        print(f"refused: {refusal}", file=sys.stderr)
        return REFUSED_EXIT
    print(f"{record['status']}: {path}" + (f": {record['failure']}" if record["status"] == FAILED else ""))
    return 0 if record["status"] == COMPLETE else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
