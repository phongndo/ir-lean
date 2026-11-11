#!/usr/bin/env python3
"""The kernel corpus's manifest, bench/kernels/manifest.toml: reading it, the rules it has to meet, and the
digest that fixes it. docs/kernels.md.

The kernel corpus is the fixed list of real projects the superoptimizer is judged on. It isn't the corpus of
docs/corpus.md, the pairs of IR tools/corpus/capture.py takes from `opt`.

The manifest names each project's pinned source, by commit and Nix hash, the units its hot kernels are
compiled from, the flags the project builds them with, the kernels, its inputs, each with its hash, and the
workloads wall time is measured on. A workload says what it runs, what's measured, its wall time or a rate it
prints, and how a candidate is checked before it's timed: its output, compared bit for bit with the
baseline's, or the project's own test of the same functions against known answers. A driver of ours that a
workload runs is pinned by its hash too, and so is every other file of this repository a workload or a check
runs.

While `corpus.state` is `proposed` it's a proposal, and nothing is approved. Once the maintainer approves a
list, `state` is `approved`, `corpus.approved` names the projects, and `corpus.approved_on` and
`corpus.decided_in` say when and where, with nothing locked yet, since what the decision asks for before
fixing can still change an entry. Then `state` is `fixed`, every workload of an approved project says what's
measured and has a check, and `[lock]` records the digest of what was approved. From then on any change to an
approved project, or to what the corpus compiles with, changes the digest, and `problems` reports it unless an
`[[amendment]]` records the change, its date and its reason, each amendment starting from the digest the one
before it ended on. The lock itself is held to the decision it records: its digest has to be in the section of
the doc `lock.approved_in` points to, docs/roadmap.md's record, so replacing it is a change to a reviewed
decision, and tests/kernels_test.py holds it to the digest approved too. So the corpus can't change quietly.

usage: bench/kernels/kernels.py check          the manifest meets every rule
       bench/kernels/kernels.py digest         the digest of the projects named, or of `corpus.approved`
       bench/kernels/kernels.py digest NAME...
       bench/kernels/kernels.py source NAME    fetch a project's source through Nix at its pin, and say where
       bench/kernels/kernels.py inputs DIR [NAME...]   fetch workload inputs into DIR, by their hashes
"""

from __future__ import annotations

import base64
import binascii
import copy
import io
import re
import sys
import tarfile
import tomllib
import zipfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, pins, proc, schemas  # noqa: E402

MANIFEST = Path(__file__).resolve().parent / "manifest.toml"

# Decision 7 of 2026-11-09: inference, compression, codecs, hashing and crypto.
DOMAINS = ("inference", "compression", "codecs", "hashing", "crypto")
STATUSES = ("recommended", "alternate", "rejected")
STATES = ("proposed", "approved", "fixed")
# S3's bar is wins from at least 3 projects, so a fixed corpus can't have fewer.
MIN_PROJECTS = 3
# Licenses that let this repo commit IR generated from the source and publish a rewrite of it, as README.md's
# table does for zlib and llama.cpp. A project under anything else needs the maintainer to add it here.
LICENSES = {
    "Apache-2.0",
    "BSD-2-Clause",
    "BSD-3-Clause",
    "CC0-1.0",
    "ISC",
    "MIT",
    "Zlib",
}
# How a project's hot kernels reach the processor. Only the first two give the pinned clang IR to work on.
SIMD = ("intrinsics", "vectorizer", "assembly", "none")
# The criteria of docs/kernels.md, by number. A rejected project names the ones it fails.
CRITERIA = range(1, 9)

REV = re.compile(r"[0-9a-f]{40}")
SHA256 = re.compile(r"[0-9a-f]{64}")
REPOSITORY = re.compile(r"https://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)")
NAME = re.compile(r"[a-z0-9][a-z0-9.+-]*")
# What a unit's flags mustn't set: the corpus sets the optimization level, and `native` would make the IR
# depend on the host, where naming the processor makes it the same on any.
BANNED_FLAG = re.compile(r"-O.*|-march=native|-mtune=native|-mcpu=native")
# What's measured of a workload, by docs/kernels.md's protocol: the wall time of its run, or a speed the
# benchmark prints, where it runs for a fixed time, as xxhsum -b does, or times its own repetitions, as
# llama-bench does.
MEASURES = ("time", "rate")
# How a candidate is shown to compute what the baseline does before it's timed: what its run writes, hashed
# and compared bit for bit with the baseline's, or the project's own test of the same functions, in its
# checking mode.
CHECKS = ("output", "known-answers")
# The places a workload's commands name: the source at its pin, the project's build, a directory for what a
# run writes, and this repository. {input:NAME} names one of the project's inputs.
PLACES = ("src", "build", "out", "repo")
PLACEHOLDER = re.compile(r"\{([^{}]*)\}")
# A file of this repository a command names, which has to be pinned by its hash.
REPO_FILE = re.compile(r"\{repo\}/(\S+)")


def load(path: Path = MANIFEST) -> dict[str, Any]:
    """The manifest, as TOML gives it."""
    return tomllib.loads(path.read_text())


def nix_hash_ok(value: Any) -> bool:
    """Whether `value` is an SRI SHA-256, as Nix prints a source's hash."""
    if not isinstance(value, str) or not value.startswith("sha256-"):
        return False
    try:
        return len(base64.b64decode(value.removeprefix("sha256-"), validate=True)) == 32
    except (binascii.Error, ValueError):
        return False


def licenses(expression: Any) -> list[str]:
    """The licenses an SPDX expression of `OR`s names, or nothing if it isn't one."""
    if not isinstance(expression, str) or not expression:
        return []
    return [part.strip() for part in expression.split(" OR ")]


def digest(manifest: dict[str, Any], names: list[str] | None = None) -> str:
    """The SHA-256 that fixes the corpus: over what every project is compiled with and measured on, and over
    each named project's whole entry but the fields that only say how the proposal ranks it. With no names,
    over `corpus.approved`."""
    corpus = manifest.get("corpus", {})
    chosen = sorted(corpus.get("approved", []) if names is None else names)
    projects = manifest.get("project", {})
    fixed = {
        "schema": manifest.get("schema"),
        "corpus": {
            k: corpus.get(k)
            for k in ("llvm_tag", "llvm_commit", "llvm_nix_hash", "target", "opt", "flags", "machine")
        },
        "projects": {
            name: {k: v for k, v in projects.get(name, {}).items() if k not in ("status", "note")}
            for name in chosen
        },
    }
    return hashing.sha256(hashing.canonical(fixed))


def _strings(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(v, str) and v for v in value)


def _project_problems(name: str, p: Any) -> list[str]:
    """What's wrong with one project's entry."""
    if not isinstance(p, dict):
        return [f"{name}: not a table"]
    out: list[str] = []
    if not NAME.fullmatch(name):
        out.append(f"{name}: a project's name is lower case letters, digits, `.`, `+` and `-`")
    for key in (
        "what",
        "users",
        "repository",
        "tag",
        "rev",
        "nix_hash",
        "license",
        "domain",
        "status",
        "simd",
    ):
        if not isinstance(p.get(key), str) or not p[key]:
            out.append(f"{name}: no {key}")
    if isinstance(p.get("repository"), str) and not REPOSITORY.fullmatch(p["repository"]):
        out.append(
            f"{name}: repository isn't https://github.com/OWNER/REPO, which is what `source` can fetch"
        )
    if isinstance(p.get("rev"), str) and not REV.fullmatch(p["rev"]):
        out.append(f"{name}: rev isn't a full commit hash, so it doesn't pin the source")
    if "nix_hash" in p and not nix_hash_ok(p["nix_hash"]):
        out.append(f"{name}: nix_hash isn't an SRI SHA-256, so the source fetched isn't checked")
    if p.get("domain") not in DOMAINS:
        out.append(f"{name}: domain {p.get('domain')!r} isn't one of {', '.join(DOMAINS)}")
    if p.get("status") not in STATUSES:
        out.append(f"{name}: status {p.get('status')!r} isn't one of {', '.join(STATUSES)}")
    if p.get("simd") not in SIMD:
        out.append(f"{name}: simd {p.get('simd')!r} isn't one of {', '.join(SIMD)}")
    named = licenses(p.get("license"))
    if named and not any(one in LICENSES for one in named):
        out.append(f"{name}: license {p['license']!r} offers none of {', '.join(sorted(LICENSES))}")

    if p.get("status") == "rejected":
        fails = p.get("fails")
        if not isinstance(fails, list) or not fails or not all(f in CRITERIA for f in fails):
            out.append(f"{name}: a rejected project names the criteria it fails, by number, in `fails`")
        if not isinstance(p.get("why"), str) or not p["why"]:
            out.append(f"{name}: a rejected project says why, in `why`")
        return out

    # From here on, a project the maintainer could approve.
    if "fails" in p:
        out.append(f"{name}: only a rejected project has `fails`")
    if p.get("simd") in ("assembly", "none"):
        out.append(
            f"{name}: simd is {p['simd']!r}, so the pinned clang has no SIMD kernel to compile: reject it"
        )
    if "flags" in p and not _strings(p["flags"]) and p["flags"] != []:
        out.append(f"{name}: flags isn't a list of strings")
    if "relax" in p and not _strings(p["relax"]):
        out.append(f"{name}: relax isn't a list of flags")
    if "include" in p and not _strings(p["include"]):
        out.append(f"{name}: include isn't a list of strings")
    if "configure" in p and not _strings(p["configure"]):
        out.append(f"{name}: configure isn't a command, a list of strings")
    deps = p.get("dep", [])
    if not isinstance(deps, list):
        out.append(f"{name}: dep isn't a list of tables")
        deps = []
    for d in deps:
        # Another source a unit's headers come from, pinned as the project's own is.
        label = f"{name}: dep {d.get('name') if isinstance(d, dict) else d!r}"
        if not isinstance(d, dict) or not isinstance(d.get("name"), str) or not NAME.fullmatch(d["name"]):
            out.append(f"{label}: no name")
            continue
        if not isinstance(d.get("repository"), str) or not REPOSITORY.fullmatch(d["repository"]):
            out.append(f"{label}: repository isn't https://github.com/OWNER/REPO")
        if not isinstance(d.get("rev"), str) or not REV.fullmatch(d["rev"]):
            out.append(f"{label}: rev isn't a full commit hash")
        if not nix_hash_ok(d.get("nix_hash")):
            out.append(f"{label}: nix_hash isn't an SRI SHA-256")
    if not isinstance(p.get("project_opt"), str) or not re.fullmatch(r"-O[0-3s]", p["project_opt"]):
        out.append(f"{name}: no project_opt, the level the project's own release build compiles at")

    units = p.get("unit")
    if not isinstance(units, list) or not units:
        out.append(f"{name}: no unit, so nothing says which code its kernels are compiled from")
        units = []
    seen: dict[str, str] = {}
    kernels = 0
    for u in units:
        source = u.get("source") if isinstance(u, dict) else None
        if not isinstance(source, str) or not source or source.startswith("/") or ".." in Path(source).parts:
            out.append(f"{name}: a unit's source is a path inside the project, not {source!r}")
            continue
        label = f"{name}: {source}"
        flags = u.get("flags", [])
        if flags != [] and not _strings(flags):
            out.append(f"{label}: flags isn't a list of strings")
            flags = []
        shared = p.get("flags", []) if isinstance(p.get("flags", []), list) else []
        for flag in [*shared, *flags]:
            if isinstance(flag, str) and BANNED_FLAG.fullmatch(flag):
                out.append(
                    f"{label}: {flag} isn't a unit's to set: the corpus sets -O, and names the processor"
                )
        names = u.get("kernels", [])
        if names != [] and not _strings(names):
            out.append(f"{label}: kernels isn't a list of function names")
            names = []
        for k in names:
            kernels += 1
            if k in seen:
                out.append(f"{label}: kernel {k} is also in {seen[k]}")
            seen[k] = source
    if units and not kernels:
        out.append(f"{name}: no kernel named in any unit, so nothing says which functions are hot")

    inputs = p.get("input", [])
    if not isinstance(inputs, list):
        out.append(f"{name}: inputs aren't a list")
        inputs = []
    named: set[str] = set()
    for i in inputs:
        if not isinstance(i, dict) or not isinstance(i.get("name"), str) or not i["name"]:
            out.append(f"{name}: an input has no name")
            continue
        named.add(i["name"])
        if not isinstance(i.get("url"), str) or not i["url"].startswith("https://"):
            out.append(f"{name}: input {i['name']} has no https url")
        if not isinstance(i.get("sha256"), str) or not SHA256.fullmatch(i["sha256"]):
            out.append(f"{name}: input {i['name']} has no SHA-256, so the workload isn't pinned")

    workloads = p.get("workload")
    if not isinstance(workloads, list) or not workloads:
        out.append(f"{name}: no workload, so nothing says what wall time is measured on")
        return out
    seen_workloads: set[str] = set()
    for w in workloads:
        label = f"{name}: workload {w.get('name') if isinstance(w, dict) else w!r}"
        if not isinstance(w, dict) or not isinstance(w.get("name"), str) or not NAME.fullmatch(w["name"]):
            out.append(f"{label}: a workload has a name, lower case letters, digits, `.`, `+` and `-`")
            continue
        if w["name"] in seen_workloads:
            out.append(f"{label}: two workloads have that name")
        seen_workloads.add(w["name"])
        out += _workload_problems(label, w, named)
    return out


def _commands(value: Any) -> bool:
    """Whether `value` is a list of commands, each a list of strings with a program."""
    return isinstance(value, list) and bool(value) and all(_strings(c) and c for c in value)


def _words(value: Any) -> list[str]:
    """Every string of a list of commands, or none if it isn't one."""
    return [s for c in value for s in c] if _commands(value) else []


def _places(label: str, strings: list[str], inputs: set[str]) -> list[str]:
    """What's wrong with the placeholders in a workload's strings: each names a place PLACES has, or one of
    the project's inputs."""
    out = []
    for s in strings:
        for place in PLACEHOLDER.findall(s):
            kind, _, what = place.partition(":")
            known = what in inputs if kind == "input" else place in PLACES
            if not known:
                out.append(f"{label}: {{{place}}} in {s!r} names no input of the project or place")
    return out


def _pinned(label: str, value: Any) -> tuple[set[str], list[str]]:
    """The files of this repository a workload's or a check's `pinned` pins, a table of each path to its
    SHA-256, and what's wrong with it. The lock covers them by their hashes, as it covers a driver."""
    if value is None:
        return set(), []
    if not isinstance(value, dict) or not all(isinstance(v, str) for v in value.values()):
        return set(), [f"{label}: pinned isn't a table of paths in this repository to their SHA-256"]
    out = []
    for path, sha256 in value.items():
        if not path or path.startswith("/") or ".." in Path(path).parts:
            out.append(f"{label}: pinned {path!r} isn't a path in this repository")
        elif not (ROOT / path).is_file():
            out.append(f"{label}: pinned {path} doesn't exist")
        elif sha256 != (actual := hashing.sha256_file(ROOT / path)):
            out.append(
                f"{label}: pinned {path}'s SHA-256 isn't the file's, {actual}: "
                "a change to a file of ours that a workload runs is a change to the corpus"
            )
    return set(value), out


def _unpinned(label: str, strings: list[str], pinned: set[str]) -> list[str]:
    """Each file of this repository `strings` name, as {repo}/PATH, that isn't in `pinned`."""
    return [
        f"{label}: {{repo}}/{path} isn't pinned: a file of this repository that a workload runs is its "
        "driver or in `pinned`, with its SHA-256"
        for s in strings
        for path in REPO_FILE.findall(s)
        if path not in pinned
    ]


def _workload_problems(label: str, w: dict[str, Any], inputs: set[str]) -> list[str]:
    """What's wrong with one workload. A fixed corpus asks more of an approved project's: `problems`."""
    out: list[str] = []
    for key in ("what", "benchmark"):
        if not isinstance(w.get(key), str) or not w[key]:
            out.append(f"{label}: no {key}")
    if not _commands(w.get("run")):
        out.append(f"{label}: no run, a list of commands, each a list of strings")
    strings = _words(w.get("run"))
    for key in ("setup", "build"):
        if key in w and not _commands(w[key]):
            out.append(f"{label}: {key} isn't a list of commands, each a list of strings")
        strings += _words(w.get(key))
    threads = w.get("threads", 1)
    if not isinstance(threads, int) or isinstance(threads, bool) or threads < 1:
        out.append(f"{label}: threads isn't a count")

    measure = w.get("measure")
    if measure is not None and measure not in MEASURES:
        out.append(f"{label}: measure {measure!r} isn't one of {', '.join(MEASURES)}")
    if measure == "rate" and (not isinstance(w.get("rate"), str) or not w["rate"]):
        out.append(f"{label}: a rate says what figure it is, and in what unit, in `rate`")
    if measure != "rate" and "rate" in w:
        out.append(f"{label}: only a workload measured as a rate has `rate`")

    if "driver" in w:
        # A program of ours: the lock covers it by its hash, so it can't change quietly either.
        driver = w["driver"]
        path = ROOT / driver if isinstance(driver, str) else None
        if path is None or not driver.startswith("bench/kernels/") or ".." in Path(driver).parts:
            out.append(f"{label}: driver isn't a path in bench/kernels/")
        elif not path.is_file():
            out.append(f"{label}: driver {driver} doesn't exist")
        elif w.get("driver_sha256") != hashing.sha256_file(path):
            out.append(
                f"{label}: driver_sha256 isn't the SHA-256 of {driver}, {hashing.sha256_file(path)}: "
                "a change to a driver is a change to the corpus"
            )
        if isinstance(driver, str) and f"{{repo}}/{driver}" not in strings:
            out.append(f"{label}: build doesn't compile the driver, {{repo}}/{driver}")
    elif "driver_sha256" in w:
        out.append(f"{label}: driver_sha256 without a driver")
    pinned, wrong = _pinned(label, w.get("pinned"))
    out += wrong
    if isinstance(w.get("driver"), str):
        pinned.add(w["driver"])
    out += _unpinned(label, strings, pinned)

    checks = w.get("check", [])
    if not isinstance(checks, list) or not all(isinstance(c, dict) for c in checks):
        out.append(f"{label}: check isn't a list of tables")
        checks = []
    for n, c in enumerate(checks, 1):
        at = f"{label}: check {n}"
        kind = c.get("kind")
        if kind not in CHECKS:
            out.append(f"{at}: kind {kind!r} isn't one of {', '.join(CHECKS)}")
        if not isinstance(c.get("what"), str) or not c["what"]:
            out.append(f"{at}: no what, saying what it compares and with what")
        if "run" in c and not _commands(c["run"]):
            out.append(f"{at}: run isn't a list of commands, each a list of strings")
        strings += _words(c.get("run"))
        its, wrong = _pinned(at, c.get("pinned"))
        out += wrong + _unpinned(at, _words(c.get("run")), pinned | its)
        if kind == "output":
            output = c.get("output")
            if not _strings(output) or not output:
                out.append(f"{at}: an output check names what's hashed, in `output`")
                output = []
            for o in output:
                if o != "stdout" and not o.startswith("{out}/"):
                    out.append(f"{at}: {o!r} isn't stdout or a file in {{out}}, what a run writes")
            strings += output
            if "sha256" in c and (not isinstance(c["sha256"], str) or not SHA256.fullmatch(c["sha256"])):
                out.append(f"{at}: sha256 isn't a SHA-256")
            if measure == "rate" and "run" not in c:
                out.append(f"{at}: a rate's run prints timings, so its output check runs its own, in `run`")
            if "test" in c:
                out.append(f"{at}: only a known-answers check names a test")
        elif kind == "known-answers":
            if "run" not in c:
                out.append(f"{at}: a known-answers check runs the project's test, in `run`")
            test = c.get("test")
            if not _strings(test) or not test:
                out.append(f"{at}: a known-answers check names the project's test and its answers, in `test`")
                test = []
            for t in test:
                if t.startswith("/") or ".." in Path(t).parts:
                    out.append(f"{at}: {t!r} isn't a path in the project")
            for key in ("output", "sha256"):
                if key in c:
                    out.append(f"{at}: only an output check has {key}")
    return out + _places(label, strings, inputs)


def unchecked(manifest: dict[str, Any]) -> list[str]:
    """What a fixed corpus asks of every workload of an approved project that it lacks: what's measured, and
    how a candidate's correctness is checked before it's timed, docs/kernels.md's protocol."""
    out = []
    projects = manifest.get("project", {})
    for name in manifest.get("corpus", {}).get("approved", []):
        workloads = projects.get(name, {}).get("workload", [])
        for w in workloads if isinstance(workloads, list) else []:
            label = f"{name}: workload {w.get('name') if isinstance(w, dict) else w!r}"
            if not isinstance(w, dict):
                continue
            if "measure" not in w:
                out.append(f"{label}: a fixed corpus says what's measured, time or a rate, in `measure`")
            if not w.get("check"):
                out.append(
                    f"{label}: a fixed corpus checks every workload of an approved project: it has no check"
                )
    return out


def problems(manifest: dict[str, Any]) -> list[str]:
    """Everything wrong with a manifest, or nothing."""
    out: list[str] = []
    if manifest.get("schema") != schemas.KERNELS_MANIFEST:
        return [f"schema {manifest.get('schema')!r}, not {schemas.KERNELS_MANIFEST}"]
    corpus = manifest.get("corpus")
    if not isinstance(corpus, dict):
        return ["no [corpus]"]
    state = corpus.get("state")
    if state not in STATES:
        out.append(f"corpus.state {state!r} isn't one of {', '.join(STATES)}")
    # The baseline is the pinned clang's, so the pin moving is a change to the corpus: its tag, and the commit
    # and source hash under it, which can move while the tag doesn't.
    llvm = pins.llvm()
    for key, pin in (("llvm_tag", "tag"), ("llvm_commit", "commit"), ("llvm_nix_hash", "nix_hash")):
        if corpus.get(key) != llvm[pin]:
            out.append(f"corpus.{key} {corpus.get(key)!r} isn't tests/llvm/targets.toml's {pin}, {llvm[pin]}")
    if corpus.get("opt") != "-O3":
        out.append("corpus.opt isn't -O3, the level decision 6's baseline names")
    if corpus.get("target") != "x86_64-unknown-linux-gnu":
        out.append("corpus.target isn't x86_64-unknown-linux-gnu: decision 7 puts x86-64 first")
    if not isinstance(corpus.get("machine"), str) or not corpus["machine"]:
        out.append("corpus.machine doesn't name the machine wall time is measured on")
    if corpus.get("flags", []) != [] and not _strings(corpus.get("flags")):
        out.append("corpus.flags isn't a list of strings")

    projects = manifest.get("project")
    if not isinstance(projects, dict) or not projects:
        return [*out, "no [project.NAME]"]
    for name in sorted(projects):
        out += _project_problems(name, projects[name])

    approved = corpus.get("approved")
    if not isinstance(approved, list) or not all(isinstance(a, str) for a in approved):
        return [*out, "corpus.approved isn't a list of project names"]
    if len(set(approved)) != len(approved):
        out.append("corpus.approved names a project twice")
    for name in approved:
        if name not in projects:
            out.append(f"corpus.approved names {name}, which has no [project.{name}]")
        elif projects[name].get("status") == "rejected":
            out.append(f"corpus.approved names {name}, which is rejected")

    lock = manifest.get("lock")
    amendments = manifest.get("amendment", [])
    if state == "proposed":
        # Approving is one act: the list, the lock and the state together.
        if approved:
            out.append("corpus.approved names projects while the corpus is only proposed")
        if lock is not None:
            out.append("there's a [lock] while the corpus is only proposed")
        if amendments:
            out.append("there's an [[amendment]] while the corpus is only proposed")
        return out
    if state == "approved":
        # The list is chosen and nothing is locked: fixing is one act, the state and the lock together.
        if len(approved) < MIN_PROJECTS:
            out.append(f"an approved corpus has at least {MIN_PROJECTS} projects, not {len(approved)}")
        on = corpus.get("approved_on")
        if not isinstance(on, str) or not re.fullmatch(r"\d{4}-\d\d-\d\d", on):
            out.append("corpus.approved_on isn't a date, YYYY-MM-DD: an approved corpus says when it was")
        if not isinstance(corpus.get("decided_in"), str) or not corpus["decided_in"]:
            out.append("corpus.decided_in is empty: an approved corpus says where the decision is recorded")
        if lock is not None:
            out.append("there's a [lock] while the corpus is only approved: fixing sets both at once")
        if amendments:
            out.append("there's an [[amendment]] while the corpus is only approved: nothing is fixed")
        return out
    if state != "fixed":
        return out

    if len(approved) < MIN_PROJECTS:
        out.append(
            f"a fixed corpus has at least {MIN_PROJECTS} projects, as S3's bar asks, not {len(approved)}"
        )
    out += unchecked(manifest)
    if not isinstance(lock, dict):
        return [*out, "the corpus is fixed and has no [lock]"]
    for key in ("sha256", "approved_on", "approved_in"):
        if not isinstance(lock.get(key), str) or not lock[key]:
            out.append(f"lock has no {key}")
    if isinstance(lock.get("sha256"), str) and not SHA256.fullmatch(lock["sha256"]):
        out.append("lock.sha256 isn't a SHA-256")
    if isinstance(lock.get("approved_on"), str) and not re.fullmatch(r"\d{4}-\d\d-\d\d", lock["approved_on"]):
        out.append("lock.approved_on isn't a date, YYYY-MM-DD")

    # The digest approved, then each amendment from the last one's digest to its own, ending at today's.
    now = digest(manifest)
    at = lock.get("sha256")
    if not isinstance(amendments, list):
        return [*out, "amendment isn't a list of tables"]
    for n, a in enumerate(amendments, 1):
        if not isinstance(a, dict):
            out.append(f"amendment {n} isn't a table")
            continue
        for key in ("on", "reason", "approved_in", "from", "to"):
            if not isinstance(a.get(key), str) or not a[key]:
                out.append(f"amendment {n} has no {key}")
        if a.get("from") != at:
            out.append(f"amendment {n} starts from {a.get('from')}, not from {at}, where the corpus stood")
        at = a.get("to")
    if at != now:
        out.append(
            f"the fixed corpus changed: its digest is {now}, and the lock and its amendments end at {at}. "
            "A change to a fixed corpus needs an [[amendment]] with its date, its reason and both digests"
        )
    return out


def _slug(heading: str) -> str:
    """A heading's anchor, as GitHub makes it."""
    return "".join(c for c in heading.lower().replace(" ", "-") if c.isalnum() or c in "-_")


def section(text: str, anchor: str) -> str | None:
    """The section of a Markdown document under the heading whose anchor is `anchor`, to the next heading at
    its level or above, or None if there's no such heading. A line in a fenced code block isn't a heading."""
    lines = text.splitlines()
    levels: list[int] = []
    fenced = False
    for line in lines:
        if line.startswith("```"):
            fenced = not fenced
        level = len(line) - len(line.lstrip("#"))
        levels.append(level if level and not fenced and line[level:].startswith(" ") else 0)
    for n, level in enumerate(levels):
        if level and _slug(lines[n][level:].strip()) == anchor:
            end = next((m for m in range(n + 1, len(lines)) if 0 < levels[m] <= level), len(lines))
            return "\n".join(lines[n:end])
    return None


def recorded(manifest: dict[str, Any]) -> list[str]:
    """What's wrong with a fixed corpus's lock as a record: its digest has to be in the section of the doc
    `lock.approved_in` points to, docs/roadmap.md's record of the decision. The lock is the digest approved,
    and every amendment starts from it, so replacing it means changing a decision that was reviewed."""
    lock = manifest.get("lock")
    if manifest.get("corpus", {}).get("state") != "fixed" or not isinstance(lock, dict):
        return []
    where, sha256 = lock.get("approved_in"), lock.get("sha256")
    path, _, anchor = where.partition("#") if isinstance(where, str) else ("", "", "")
    if not path or not anchor or path.startswith("/") or ".." in Path(path).parts:
        return [f"lock.approved_in {where!r} isn't PATH#HEADING, a section of a doc in this repository"]
    if not (ROOT / path).is_file():
        return [f"lock.approved_in names {path}, which doesn't exist"]
    text = section((ROOT / path).read_text(), anchor)
    if text is None:
        return [f"lock.approved_in names #{anchor}, which isn't a heading of {path}"]
    if not isinstance(sha256, str) or sha256 not in text:
        return [
            f"lock.sha256 {sha256} isn't in {where}, the record of the decision it locks: the lock is the "
            "digest approved, and a change from it is an [[amendment]] that starts from it"
        ]
    return []


def fixed(manifest: dict[str, Any], names: list[str], on: str, where: str) -> dict[str, Any]:
    """`manifest` as it stands once the maintainer approves `names`: fixed, with its lock."""
    m = copy.deepcopy(manifest)
    m["corpus"]["state"] = "fixed"
    m["corpus"]["approved"] = list(names)
    m.pop("amendment", None)
    m["lock"] = {"sha256": digest(m), "approved_on": on, "approved_in": where}
    return m


def stored(project: dict[str, Any]) -> Path | None:
    """Where the Nix store holds a source with this hash, if it does. Asks no network: a source's path is a
    function of its hash."""
    digest = base64.b64decode(project["nix_hash"].removeprefix("sha256-")).hex()
    r = proc.run(["nix-store", "--print-fixed-path", "--recursive", "sha256", digest, "source"], timeout=60)
    if not r.ok or not r.out.strip().startswith("/nix/store/"):
        return None
    path = Path(r.out.strip())
    return (
        path if proc.run(["nix-store", "--check-validity", path], timeout=60).ok and path.is_dir() else None
    )


def source(name: str, project: dict[str, Any], offline: bool = False) -> Path | None:
    """A project's source in the Nix store, at its pin and checked against its hash, or one of its `dep`s',
    which has the same fields. Fetches it unless `offline`, when it's None if the store doesn't hold it.
    Raises RuntimeError if Nix can't give it."""
    if offline:
        return stored(project)
    m = REPOSITORY.fullmatch(project["repository"])
    if m is None:
        raise RuntimeError(f"{name}: can't fetch {project['repository']}")
    expr = (
        f'(builtins.fetchTree {{ type = "github"; owner = "{m[1]}"; repo = "{m[2]}"; '
        f'rev = "{project["rev"]}"; narHash = "{project["nix_hash"]}"; }}).outPath'
    )
    r = proc.run(["nix", "eval", "--raw", "--expr", expr], timeout=1800)
    path = Path(r.out.strip()) if r.ok and r.out.strip().startswith("/nix/store/") else None
    if path is not None and path.is_dir():
        return path
    raise RuntimeError(f"{name}: nix couldn't fetch it at its pin\n{r.err[-2000:]}")


def inputs(manifest: dict[str, Any], where: Path, names: list[str]) -> list[Path]:
    """Fetches the workload inputs of the projects named through Nix, each checked against the manifest's
    SHA-256, and links them into `where` by the names the manifest gives them. A zip is also unpacked beside
    itself as a tar, the same bytes every time: names sorted, no times or owners."""
    where.mkdir(parents=True, exist_ok=True)
    out: list[Path] = []
    seen: dict[str, str] = {}
    for name in names:
        for i in manifest["project"][name].get("input", []):
            if seen.setdefault(i["name"], i["sha256"]) != i["sha256"]:
                raise RuntimeError(f"two inputs are named {i['name']}, with different hashes")
            link = where / i["name"]
            if link not in out:
                expr = f'builtins.fetchurl {{ url = "{i["url"]}"; sha256 = "{i["sha256"]}"; }}'
                r = proc.run(["nix", "eval", "--raw", "--expr", expr], timeout=3600)
                if not r.ok or not r.out.strip().startswith("/nix/store/"):
                    raise RuntimeError(
                        f"{name}: nix couldn't fetch {i['url']} with that hash\n{r.err[-2000:]}"
                    )
                link.unlink(missing_ok=True)
                link.symlink_to(r.out.strip())
                out.append(link)
            if link.suffix == ".zip" and (tar := link.with_suffix(".tar")) not in out:
                with zipfile.ZipFile(link) as z, tarfile.open(tar, "w", format=tarfile.USTAR_FORMAT) as t:
                    for member in sorted(z.namelist()):
                        data = z.read(member)
                        info = tarfile.TarInfo(member)
                        info.size, info.mode = len(data), 0o644
                        t.addfile(info, io.BytesIO(data))
                out.append(tar)
    return out


def main(argv: list[str]) -> int:
    if argv and argv[0] == "inputs" and len(argv) >= 2:
        manifest = load()
        # llama.cpp's model is over a gigabyte, so it's fetched only when asked for by name.
        default = [
            n for n, p in manifest["project"].items() if p["status"] != "rejected" and n != "llama.cpp"
        ]
        if unknown := [n for n in argv[2:] if n not in manifest["project"]]:
            print(f"no project {', '.join(unknown)}", file=sys.stderr)
            return 2
        for path in inputs(manifest, Path(argv[1]), argv[2:] or default):
            print(f"{hashing.sha256_file(path)}  {path}")
        return 0
    if not argv or argv[0] not in ("check", "digest", "source"):
        print(__doc__, file=sys.stderr)
        return 2
    manifest = load()
    if argv[0] == "digest":
        print(digest(manifest, argv[1:] or None))
        return 0
    if argv[0] == "source":
        if len(argv) != 2 or argv[1] not in manifest.get("project", {}):
            print(__doc__, file=sys.stderr)
            return 2
        print(source(argv[1], manifest["project"][argv[1]]))
        return 0
    found = problems(manifest) + recorded(manifest)
    for line in found:
        print(f"FAIL {line}")
    if found:
        return 1
    corpus, projects = manifest["corpus"], manifest["project"]
    by = {s: sorted(n for n, p in projects.items() if p["status"] == s) for s in STATUSES}
    print(f"ok   {MANIFEST.relative_to(ROOT)}: {corpus['state']}, {len(projects)} projects")
    for status in STATUSES:
        print(f"     {status}: {', '.join(by[status]) or 'none'}")
    if corpus["state"] == "approved":
        print(f"     approved on {corpus['approved_on']}, not fixed: {', '.join(corpus['approved'])}")
    if corpus["state"] == "fixed":
        print(f"     approved: {', '.join(corpus['approved'])}, digest {digest(manifest)}")
        workloads = [w for n in corpus["approved"] for w in projects[n]["workload"]]
        rates = sum(w["measure"] == "rate" for w in workloads)
        by = {k: sum(any(c["kind"] == k for c in w["check"]) for w in workloads) for k in CHECKS}
        print(
            f"     {len(workloads)} workloads, {rates} of them rates, checked by "
            + ", ".join(f"{k}: {n}" for k, n in by.items())
        )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
