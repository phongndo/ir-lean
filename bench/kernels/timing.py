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
VARIANTS = ("baseline", "candidate")
COMPLETE, FAILED = "complete", "failed"
# What ldd prints for a library it found, and for what has no file to find: the vDSO, or the loader by path.
RESOLVED = re.compile(r"\t(\S+) => (/\S+) \(0x[0-9a-f]+\)")
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


def loaded(program: Path, env: dict[str, str]) -> list[dict[str, str]]:
    """The program and each library `ldd` says it loads under `env`, by name, path and SHA-256. A library
    it opens while it runs isn't seen."""
    r = proc.run(["ldd", program], env=env, timeout=120)
    if not r.ok:
        raise Failed(f"ldd {program} ended with exit code {r.exit}: {r.output[-500:]}")
    found = [("program", program)]
    for line in r.out.splitlines():
        if line.strip() == "statically linked":
            continue
        if m := RESOLVED.fullmatch(line):
            found.append((m[1], Path(m[2])))
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
        """One of the project's inputs, in --inputs, checked once against the SHA-256 the manifest gives."""
        if self.inputs is None or not (self.inputs / name).exists():
            raise Refused(f"{{input:{name}}} needs --inputs, a directory holding {name}")
        path = self.inputs / name
        known = self.record.setdefault("inputs", {})
        if name not in known:
            declared = self.manifest["project"][self.project].get("input", [])
            want = next((i.get("sha256") for i in declared if i.get("name") == name), None)
            # A directory, as an unpacked archive is, has no hash of its own here.
            have = hashing.sha256_file(path) if path.is_file() else None
            if want is None or (have is not None and have != want):
                raise Refused(f"{path} isn't the {name} the manifest pins: its SHA-256 is {have}, not {want}")
            known[name] = have
        return path

    def env(self, variant: str, own: dict[str, str] | None = None) -> dict[str, str]:
        both = set(self.variants[variant].env) & set(own or {})
        if both:
            raise Refused(f"the {variant}'s environment and the command's both set {sorted(both)}")
        env = {**os.environ, **STOCK, **self.variants[variant].env, **(own or {})}
        env.pop("SOURCE_DATE_EPOCH", None)
        return env

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
            files += loaded(Path(argv[0]).resolve(), self.env(variant, own))
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
        for variant in VARIANTS:
            self.out[variant].mkdir(parents=True)
            self.step("build", self.w.get("build", []), variant)
        before = {v: self.identity(v) for v in VARIANTS}
        for v in VARIANTS:
            record["variants"][v]["identity"] = before[v]
        same = before["baseline"]["id"] == before["candidate"]["id"]
        if same and not self.control:
            raise Failed(
                "the candidate loads what the baseline loads, byte for byte, and this isn't a control"
            )
        if self.control and not same:
            raise Failed("a control's two variants load the same bytes, and these differ")
        # The identities say which directory this session's record goes in, so only now can its seed be
        # checked against the others there. Nothing has been timed yet.
        where = directory(self.sessions, record)
        if where.is_dir() and any(r["seed"] == self.seed for _, r in records(where)):
            raise Refused(f"seed {self.seed} was used by another session in {where}")
        for variant in VARIANTS:
            self.step("setup", self.w.get("setup", []), variant)
        record["checks"] = self.check()
        warm = {v: self.timed(v, RUN_SECONDS) for v in VARIANTS}
        record["warm_up"] = warm
        reference = warm["baseline"].get("output")
        if warm["candidate"].get("output") != reference:
            raise Failed("the candidate's warm-up didn't write what the baseline's did")
        shortest = min(w["seconds"] for w in warm.values())
        if self.measure == protocol.TIME and shortest > 0:
            self.repeat = max(1, math.ceil(self.rule.min_seconds / shortest))
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
        # Only now does the record get its pairs, so a session that failed anywhere above has none.
        record["pairs"] = pairs
        record["status"] = COMPLETE

    def run(self) -> dict[str, Any]:
        try:
            self.body()
        except Failed as failure:
            self.record["failure"] = str(failure)
        self.record["ended"] = proc.now()
        return self.record


def directory(sessions: Path, record: dict[str, Any]) -> Path:
    """Where a session's record goes: one directory for each workload and pair of identities, so that every
    session of one candidate on one workload is beside the others, the failed ones too."""
    ids = [record["variants"][v].get("identity", {}).get("id") for v in VARIANTS]
    pair = hashing.sha256_text(json.dumps(ids))[:16] if all(ids) else "unidentified"
    return sessions / record["project"] / record["workload"] / pair


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


def sessions_of(where: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    """The confirmation sessions of a directory, complete and failed, what was left out and why, and what
    the complete ones share. Raises Refused if they measured different things, or two used one seed."""
    found = records(where)
    if not found:
        raise Refused(f"{where} has no session")
    shared_keys = (
        "project",
        "workload",
        "workloads",
        "cpus",
        "threads",
        "measure",
        "rule",
        "manifest",
        "control",
    )
    complete = [(p, r) for p, r in found if r["status"] == COMPLETE]
    if not complete:
        why = "; ".join(str(r.get("failure", ""))[:200] for _, r in found)
        raise Refused(f"{where} has no complete session: {why}")
    first = complete[0][1]
    shared = {k: first[k] for k in shared_keys}
    shared["builds"] = {v: first["variants"][v]["build"] for v in VARIANTS}
    shared["identities"] = {v: first["variants"][v]["identity"]["id"] for v in VARIANTS}
    for p, r in complete:
        differs = [k for k in shared_keys if r[k] != shared[k]]
        differs += [v for v in VARIANTS if r["variants"][v]["identity"]["id"] != shared["identities"][v]]
        differs += [f"{v}'s build" for v in VARIANTS if r["variants"][v]["build"] != shared["builds"][v]]
        if differs:
            raise Refused(f"{p} and {complete[0][0].name} measured different things: {differs}")
    seeds = [r["seed"] for _, r in complete]
    if len(set(seeds)) != len(seeds):
        raise Refused(f"two sessions in {where} used one seed")
    counted, left = [], []
    for p, r in found:
        if r["kind"] == protocol.CONFIRMATION:
            # A failed confirmation session counts too: what it planned and didn't time is what's missing.
            counted.append({"session": p.name, **r})
        else:
            left.append({"session": p.name, "why": "exploratory: only confirmation sessions count"})
    return counted, left, shared


def ratios(counted: list[dict[str, Any]]) -> dict[str, list[list[float]]]:
    """Each figure's paired ratios, session by session, of the sessions that have pairs."""
    timed = [s for s in counted if s["pairs"]]
    figures = sorted(timed[0]["pairs"][0]["ratios"]) if timed else []
    return {f: [[p["ratios"][f] for p in s["pairs"]] for s in timed] for f in figures}


def runs(counted: list[dict[str, Any]]) -> tuple[verdict.Plan, tuple[verdict.Step, ...]]:
    """Every timed run the sessions planned, and each they recorded, as irlean.verdict takes cases: a run is
    named by its session, its pair and its variant, and its exit code is its last command's."""
    planned, observed = [], []
    for s in counted:
        planned += [f"{s['session']}:{n}:{v}" for n in range(1, s["planned_pairs"] + 1) for v in VARIANTS]
        for pair in s["pairs"]:
            for v in VARIANTS:
                run = pair[v]
                observed.append(verdict.Step(f"{s['session']}:{pair['pair']}:{v}", run["exit"], run["limit"]))
    return verdict.Plan(tuple(planned), whole=True), tuple(observed)


def read(where: Path, others: list[Path]) -> dict[str, Any]:
    """Reads one directory of sessions by the rule. `others` are the directories of the project's other
    workloads, for the rule's fourth condition: each has to be of the same two builds. What the reading
    comes to is irlean.verdict's to say: each timed run is a case, and the rule's conditions its checks."""
    counted, left, shared = sessions_of(where)
    rule = protocol.Rule(**shared["rule"])
    reading: dict[str, Any] = {
        "schema": schemas.KERNELS_READING,
        **{k: shared[k] for k in ("project", "workload", "measure", "cpus", "threads", "control")},
        "sessions": [{"session": s["session"], "status": s["status"]} for s in counted],
        "left_out": left,
    }

    def say(decision: verdict.Decision | None, reason: str, why: str = "") -> dict[str, Any]:
        reading["status"], reading["reason"], reading["exit_code"] = verdict.status(decision, TABLE, reason)
        if why:
            reading["why"] = why
        return reading

    by_figure = ratios(counted)
    if not by_figure:
        return say(None, "not_shown", "no confirmation session with pairs")
    seed = pooled_seed([s["seed"] for s in counted if s["pairs"]])
    if shared["control"]:
        pooled = {
            f: protocol.summary([r for s in each for r in s], seed, rule) for f, each in by_figure.items()
        }
        reading["pooled"] = pooled
        reading["control_contains_one"] = all(
            p["interval"][0] <= 1 <= p["interval"][1] for p in pooled.values()
        )
        return say(None, "control")
    measured: dict[str, list[float] | None] = {
        w: None for w in shared["workloads"] if w != shared["workload"]
    }
    for other in others:
        theirs, _, about = sessions_of(other)
        if about["project"] != shared["project"] or about["builds"] != shared["builds"] or about["control"]:
            raise Refused(f"{other} isn't sessions of the same two builds of {shared['project']}")
        each = ratios(theirs)
        if about["workload"] not in measured or not each:
            raise Refused(f"{other} has no confirmation session of another workload of {shared['project']}")
        ends = [protocol.summary([r for s in e for r in s], seed, rule)["interval"] for e in each.values()]
        # A workload with several figures is slower if any of them is: its lowest upper end is what counts.
        measured[about["workload"]] = min(ends, key=lambda i: i[1])
    kinds = [s["kind"] for s in counted if s["pairs"]]
    found = protocol.conditions(by_figure, kinds, seed, measured, rule)
    reading["result"] = found
    live = hashing.sha256_file(kernels.MANIFEST)
    checks = {name: c["held"] for name, c in found["conditions"].items()}
    # A comparison that isn't by the protocol is never shown faster or slower: the corpus's manifest as it
    # is now, an approved project, and the protocol's own rule.
    checks["corpus"] = bool(shared["manifest"]["corpus"]) and shared["manifest"]["sha256"] == live
    checks["rule"] = rule == protocol.PROTOCOL
    plan, cases = runs(counted)
    evidence = verdict.Evidence(plan=plan, cases=cases, checks=checks)
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
