#!/usr/bin/env python3
"""BIND-03's acceptance: tools/verify_claims.py accepts every claim the scorer accepts, and refuses forged
ones.

The scorer's claims are the 87 functions of LLVM's own code that tests/llvm.py proves, from
tests/llvm/targets.toml, with the theorem each names. This builds one piece of evidence holding all of them,
and the verifier has to replay it. So does every control tools/verify.py, the scorer's checker, certifies in
tests/verification_negative, and tools/verify.py has to prove each of those here too, so the two are seen to
agree on the same inputs.

Then each forged claim breaks one thing about a good one, and has to be refused for that reason, never
another: a wrong statement, stale anchors, an extra axiom, `sorry`, a theorem added past the kernel, and the
rest in CASES. Claims that can't be complete, or whose coverage nothing can decide yet, are refused before any
replay.

And its guard, docs/verdicts.md's test 8: a replay is `replayed` only with every check of REPLAYED passed
once, over every module it planned, and a claim `verified` only with each evidence file's replay so. A check
skipped, passed twice or over a module short is `error`, `incomplete`; IRLEAN_DENY_ALL takes every grant away,
with a non-zero exit; and files changed while the evidence's code ran are `error`, exit 5.

And evidence identity, docs/verify-claims.md's: each file a replay rests on is read once, through read_once,
and nothing reads its path again. A claim naming one evidence file twice, by an alias or a copy, is refused
before any replay; `verified` counts replays by the hash of the bytes replayed; a file rewritten right after
it's read, or a header swapped for a symlink while clang runs, changes nothing; and a lint fails on any other
read.

usage: tests/verify_claims_test.py [--tier static|live|all] [--only NAME ...] [--jobs N]

`static` needs only Python. `live` needs the dev shell, build/ir-lean and `lake build IRLean`.
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import copy
import io
import json
import os
import re
import shutil
import sys
import tempfile
import time
import tomllib
from collections import Counter
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any, cast
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import verify_claims as vc  # noqa: E402
from irlean import hashing, proc  # noqa: E402

TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
WORK = ROOT / "build" / "verify-claims-test"
DENY_ALL = "IRLEAN_DENY_ALL"


def sha(path: Path) -> str:
    return hashing.sha256_file(path)


def unit(config: dict[str, Any], target: dict[str, Any]) -> dict[str, Any]:
    flags = config["flags"][target["flags"]]
    return {
        "source": target["source"],
        "source_in": "repo" if target.get("wrapper") else "llvm-project",
        "language": "c++" if flags.get("cxx") else "c",
        "flags": [*flags.get("args", []), *target.get("args", [])],
        "include": flags.get("include", []),
        "local_include": flags.get("local_include", []),
        "llvm_config": bool(flags.get("llvm_config")),
        "extract": [],
        "namespace": target["module"],
        "translate": ["--no-code"],
        "anchors": {},
        "repo_files": {},
        "ir_sha256": "",
        "lean_sha256": "",
    }


def corpus(only: list[str] | None = None, model_proofs: bool = True) -> dict[str, Any]:
    """Evidence, to be recorded, for every function tests/llvm.py proves, or the targets in `only`. With
    `model_proofs`, a statement may use its proof module's definitions, as tests/llvm.py's do."""
    config = tomllib.loads(TARGETS.read_text())
    targets = [t for t in config["target"] if not only or t["module"] in only]
    files = dict.fromkeys(config["support"], "") | {t["proof"]: "" for t in targets}
    theorems = [
        {"module": t["proof"], "name": d["theorem"], "about": [d.get("symbol", f)], "statement": "",
         "statement_sha256": ""}
        for t in targets
        for f, d in t["functions"].items()
    ]  # fmt: skip
    return {
        "schema": vc.EVIDENCE_SCHEMA,
        "llvm": {k: config["project"][k] for k in ("tag", "commit", "nix_hash")},
        "lean_version": "",
        "units": [unit(config, t) for t in targets],
        # tests/llvm.py reads each statement with its proof module's definitions, such as LEB128's `Encoded`.
        "lean": {
            "root": "tests/llvm",
            "files": files,
            "model": list(files) if model_proofs else list(config["support"]),
        },
        "theorems": theorems,
        "cuts": [],
        "contexts": "all",
    }


# --- Static cases: claims refused before anything is replayed ---------------------------------------------


def claim(**over: Any) -> dict[str, Any]:
    c = {
        "item": "pass:instcombine",
        "dimension": "code-binding",
        "contexts": "all",
        "status": "complete",
        "evidence": [{"kind": "binding-check", "path": "tests/llvm_scope/coverage.json", "sha256": "0" * 64}],
        "anchors": {},
        "gaps": [],
    }
    return c | over


def static_cases() -> list[tuple[str, dict[str, Any], str]]:
    inv = json.loads(vc.INVENTORY.read_text())
    anchors = next(i for i in inv["items"] if i["id"] == "pass:instcombine")["anchors"]
    good_anchors = claim(anchors=anchors)
    return [
        ("partial", claim(status="partial", anchors=anchors), "not_complete"),
        ("admitted", claim(status="admitted", anchors=anchors), "not_complete"),
        ("some contexts", claim(contexts=["opt:default<O2>"], anchors=anchors), "contexts_uncovered"),
        ("gaps", claim(gaps=["vectors"], anchors=anchors), "gaps_listed"),
        (
            "translation validation",
            claim(dimension="translation-validation", anchors=anchors),
            "dimension_unverifiable",
        ),
        ("unknown pass", claim(item="pass:no-such-pass"), "claim_invalid"),
        ("all-input with no rewrite list", claim(dimension="all-input"), "coverage_undecidable"),
        ("composition", claim(dimension="composition"), "coverage_undecidable"),
        (
            "code binding, stale anchors",
            claim(anchors={**anchors, next(iter(anchors)): "0" * 64}),
            "stale_anchors",
        ),
        ("code binding, anchors left out", claim(anchors={}), "stale_anchors"),
        ("code binding with no closure", good_anchors, "coverage_undecidable"),
    ]


def run_static() -> list[str]:
    failures = []
    for name, c, want in static_cases():
        v = vc.decide_claim(c)
        ok = v["status"] == "refused" and v["reason"] == want
        print(f"{'ok  ' if ok else 'FAIL'} static: {name}: {v['status']} {v['reason']}")
        if not ok:
            failures.append(
                f"static {name}: wanted refused {want}, got {v['status']} {v['reason']}: {v['detail']}"
            )
    # A process that ran out of memory says nothing about the evidence: unknown, never refused. A fork that
    # fails with ENOMEM, as bv_decide's can on a CI runner, reads this way.
    enomem = "Proof.lean:1:1: error: resource exhausted (error code: 12, not enough memory)"
    ran = vc.Ran(["lean"], 1, "", enomem, False, 0.0)
    try:
        vc.need(ran, "proof_compile_failed", "lean Proof")
        got = "passed"
    except vc.Stop as stop:
        got = stop.status
    print(f"{'ok  ' if got == 'unknown' else 'FAIL'} static: a process out of memory is {got}")
    if got != "unknown":
        failures.append(f"a process out of memory is {got}, not unknown")
    # tests/llvm_scope.py asks this verifier, and only for a complete claim.
    sys.path.insert(0, str(ROOT / "tests"))
    import llvm_scope

    ok = llvm_scope.VERIFIERS.get("binding-check") is vc.check_claim
    print(
        f"{'ok  ' if ok else 'FAIL'} static: tests/llvm_scope.py asks this verifier for code-binding claims"
    )
    if not ok:
        failures.append("tests/llvm_scope.py's VERIFIERS doesn't use tools/verify_claims.py")
    return failures + run_guard() + run_identity()


# --- The guard: only a whole replay grants, docs/verdicts.md's test 8 ---------------------------------------

# The checks a replay needs, each passed exactly once, fixed here so that taking one off vc.REPLAYED fails.
REPLAYED = (
    "pin", "anchors", "ir_replay", "translation_replay", "compile_generated", "compile_evidence",
    "statements", "axioms", "kernel_replay", "unchanged",
)  # fmt: skip
# A plan of one generated module and two of the evidence's own, and what each check over modules has to cover.
PLAN = {"units": [{"namespace": "Gen"}], "lean": {"files": {"Kit": "", "Proof": ""}}}
WHOLE = {
    "compile_generated": ["Gen"],
    "compile_evidence": ["Kit", "Proof"],
    "kernel_replay": ["Gen", "Kit", "Proof"],
}
INCOMPLETE = ("error", "incomplete")


def replay_of(checks: Sequence[str] = REPLAYED, modules: dict[str, list[str]] = WHOLE) -> vc.Replay:
    """A replay of PLAN that passed `checks` and covered `modules`, with no process run."""
    nowhere = Path("/nonexistent")
    t = vc.Tools(nowhere, nowhere, nowhere, nowhere, "", [])
    r = vc.Replay(copy.deepcopy(PLAN), t, nowhere, 1, 1, 1.0, False, copy.deepcopy(PLAN))
    for c in checks:
        r.passed(c)
    for step, done in modules.items():
        r.observed[step] += done
    return r


def outcome(f: Callable[[], Any], deny: str = "") -> tuple[str, str]:
    """The status and reason `f` gives with IRLEAN_DENY_ALL set to `deny`, or the exception it raises."""
    try:
        with mock.patch.dict(os.environ, {DENY_ALL: deny}):
            v = f()
            v = v.verdict if isinstance(v, vc.Replayed) else v
    except vc.Stop as s:
        return s.status, s.reason
    except Exception as e:
        return "raised", type(e).__name__
    return v["status"], v["reason"]


def read(name: str, data: bytes) -> vc.Read:
    """An evidence file `name`, as read_once would give it, holding `data`."""
    return vc.Read(Path("/claims") / name, data, hashing.sha256(data))


def replayed(r: vc.Read) -> vc.Replayed:
    """A whole replay's result, of the bytes `r` read, asked with IRLEAN_DENY_ALL unset."""
    with mock.patch.dict(os.environ, {DENY_ALL: ""}):
        return vc.complete(replay_of(), "x", path=r.path.name, digest=r.sha256)


def guard_cases() -> list[tuple[str, Callable[[], Any], str, tuple[str, str]]]:
    """(name, what's asked, IRLEAN_DENY_ALL, the status and reason it gives) for the guard's functions."""
    whole = ("replayed", "replayed")
    cases: list[tuple[str, Callable[[], Any], str, tuple[str, str]]] = [
        ("a whole replay", lambda: vc.complete(replay_of(), "x"), "", whole),
        ("a whole replay, IRLEAN_DENY_ALL=0", lambda: vc.complete(replay_of(), "x"), "0", whole),
        (
            "a whole replay, IRLEAN_DENY_ALL=1",
            lambda: vc.complete(replay_of(), "x"),
            "1",
            ("error", "denied"),
        ),
        ("a check no one lists", lambda: vc.complete(replay_of([*REPLAYED, "extra"]), "x"), "", INCOMPLETE),
    ]
    for c in REPLAYED:
        rest = [k for k in REPLAYED if k != c]
        cases.append((f"{c} left out", lambda rest=rest: vc.complete(replay_of(rest), "x"), "", INCOMPLETE))
        twice = [*REPLAYED, c]
        cases.append((f"{c} passed twice", lambda t=twice: vc.complete(replay_of(t), "x"), "", INCOMPLETE))
    for step, done in WHOLE.items():
        changed = [(f"{step} on a module not planned", WHOLE | {step: [*done, "Other"]})]
        for m in done:
            changed.append((f"{step} without {m}", WHOLE | {step: [k for k in done if k != m]}))
            changed.append((f"{step} on {m} twice", WHOLE | {step: [*done, m]}))
        for name, modules in changed:
            cases.append((name, lambda ms=modules: vc.complete(replay_of(modules=ms), "x"), "", INCOMPLETE))
    raised = ("raised", "ValueError")
    for word in ("replayed", "verified"):
        cases.append((f"verdict asked for {word}", lambda w=word: vc.verdict(w, w, "x"), "", raised))
    # A claim is verified only with each evidence file it plans replayed, each by complete, by the hash of the
    # bytes read: a path says nothing about which bytes were replayed.
    A, B, C = read("a.json", b"a"), read("b.json", b"b"), read("c.json", b"c")
    B2 = read("b.json", b"b, changed")  # B's path, other bytes
    a, b, c, b2 = (replayed(r) for r in (A, B, C, B2))
    ab = [A, B]
    for name, results, planned, deny, want in [
        ("verified, each evidence file replayed", [b, a], ab, "", ("verified", "verified")),
        ("verified, IRLEAN_DENY_ALL=1", [a, b], ab, "1", ("error", "denied")),
        ("verified, an evidence file planned and not replayed", [a], ab, "", INCOMPLETE),
        ("verified, another file's replay in a planned one's place", [a, c], ab, "", INCOMPLETE),
        ("verified, one file's replay twice", [a, a], ab, "", INCOMPLETE),
        ("verified, a planned path's replay, of other bytes", [a, b2], ab, "", INCOMPLETE),
        ("verified, a plan naming one file twice, replayed once", [a], [A, A], "", INCOMPLETE),
        ("verified, a plan naming one file twice, replayed twice", [a, a], [A, A], "", INCOMPLETE),
        ("verified, a plan of paths, not reads", [a, b], ["a.json", "b.json"], "", INCOMPLETE),
        ("verified, a verdict saying replayed, not complete's result", [a, b.verdict], ab, "", INCOMPLETE),
        ("verified, no evidence", [], [], "", INCOMPLETE),
        ("verified, one refused", [vc.verdict("refused", "x", "y")], [A], "", INCOMPLETE),
    ]:  # fmt: skip
        # A plan of paths is a caller's mistake the guard has to refuse, so it's passed as it is.
        cases.append(
            (name, lambda r=results, p=planned: vc.verified(r, cast(list[vc.Read], p), "x"), deny, want)
        )
    return cases


def run_guard() -> list[str]:
    failures = []
    fixed = getattr(vc, "REPLAYED", None) == REPLAYED
    print(f"{'ok  ' if fixed else 'FAIL'} static: guard: REPLAYED is the design's fixed list of checks")
    if not fixed:
        failures.append(f"guard: vc.REPLAYED is {getattr(vc, 'REPLAYED', None)}, not {REPLAYED}")
    for name, f, deny, want in guard_cases():
        got = outcome(f, deny)
        print(f"{'ok  ' if got == want else 'FAIL'} static: guard: {name}: {' '.join(got)}")
        if got != want:
            failures.append(f"guard {name}: wanted {' '.join(want)}, got {' '.join(got)}")
    return failures


# --- Evidence identity: each file read once, and known by its bytes' hash ----------------------------------

# Evidence a stubbed replay accepts, and the same evidence for only some contexts, which a second read would
# find.
PLAIN = json.dumps({"contexts": "all", "units": []}).encode()
NARROWED = json.dumps({"contexts": ["opt:default<O2>"], "units": []}).encode()


def plan_claim(*entries: tuple[str, bytes]) -> dict[str, Any]:
    """A complete code-binding claim for pass:toy, whose closure is empty, naming each (path, bytes) as
    evidence, so only its evidence decides it."""
    evidence = [{"kind": "binding-check", "path": p, "sha256": hashing.sha256(data)} for p, data in entries]
    return {"item": "pass:toy", "dimension": "code-binding", "contexts": "all", "status": "complete",
            "anchors": {}, "gaps": [], "evidence": evidence}  # fmt: skip


def decide_planned(claim: dict[str, Any], root: Path, after_read: Callable[[vc.Read], None] = lambda r: None
                   ) -> tuple[tuple[str, str], list[bytes], list[Path], list[str]]:  # fmt: skip
    """decide_claim on `claim`, under `root`, with pass:toy's inventory and closure, and replay_evidence
    stubbed to accept what it's given. The status and reason, the bytes each replay was given, each path
    read_once read, and each path opened any other way."""
    d = Path(tempfile.mkdtemp(prefix="verify-claims-plan-"))
    try:
        inv = {"pin": {"tag": vc.pinned()["tag"]},
               "items": [{"id": "pass:toy", "anchors": {}, "unresolved_classes": []}]}  # fmt: skip
        (d / "closure").mkdir()
        (d / "inventory.json").write_text(json.dumps(inv))
        closure = {"schema": vc.CLOSURE_SCHEMA, "complete": True, "files": {}, "functions": []}
        (d / "closure" / "toy.json").write_text(json.dumps(closure))
        given: list[bytes] = []
        read_by_once: list[Path] = []
        opened: list[str] = []

        def replay(data: bytes, *, path: str = "", **_: Any) -> tuple[vc.Replayed, Any]:
            given.append(data)
            return vc.complete(
                replay_of(), "x", path=path, digest=hashing.sha256(data), theorems=[]
            ), json.loads(data)

        real_read, real_open, real_os_open = vc.read_once, open, os.open

        def read_once(path: Path, *args: Any, **kw: Any) -> vc.Read:
            with mock.patch("builtins.open", real_open), mock.patch("os.open", real_os_open):
                r = real_read(path, *args, **kw)
            read_by_once.append(r.path)
            after_read(r)
            return r

        def counted(opener: Callable[..., Any]) -> Callable[..., Any]:
            def f(file: Any, *args: Any, **kw: Any) -> Any:
                if isinstance(file, (str, Path)) and Path(file).absolute().is_relative_to(root):
                    opened.append(str(file))
                return opener(file, *args, **kw)

            return f

        with (mock.patch.object(vc, "replay_evidence", replay), mock.patch.object(vc, "read_once", read_once),
              mock.patch("builtins.open", counted(real_open)),
              mock.patch("os.open", counted(real_os_open))):  # fmt: skip
            v = vc.decide_claim(claim, root=root, inventory=d / "inventory.json", closures=d / "closure")
        return (v["status"], v["reason"]), given, read_by_once, opened
    finally:
        shutil.rmtree(d, ignore_errors=True)


def run_identity() -> list[str]:
    """The design's tests 1 to 5: a plan by identity, each file read once, and the trees held still."""
    failures: list[str] = []

    def expect(name: str, ok: bool, got: str) -> None:
        print(f"{'ok  ' if ok else 'FAIL'} static: identity: {name}: {got}")
        if not ok:
            failures.append(f"identity {name}: {got}")

    root = Path(tempfile.mkdtemp(prefix="verify-claims-root-"))
    try:
        (root / "ev").mkdir()
        (root / "ev" / "a.json").write_bytes(PLAIN)
        (root / "ev" / "copy.json").write_bytes(PLAIN)
        (root / "ev" / "link.json").symlink_to(root / "ev" / "a.json")
        (root / "outside.json").write_bytes(PLAIN)
        refused = ("refused", "claim_invalid")
        got, given, _, _ = decide_planned(plan_claim(("ev/a.json", PLAIN)), root)
        expect(
            "one evidence file",
            got == ("verified", "verified") and given == [PLAIN],
            f"{got}, {len(given)} replays",
        )
        for name, other in [("an alias with ./", "./ev/a.json"), ("an alias through ..", "ev/x/../a.json"),
                            ("an alias by a symlink", "ev/link.json"),
                            ("a copy of the same bytes", "ev/copy.json"),
                            ("the same path twice", "ev/a.json")]:  # fmt: skip
            got, given, _, _ = decide_planned(plan_claim(("ev/a.json", PLAIN), (other, PLAIN)), root)
            expect(
                f"{name}: refused, nothing replayed",
                (got, given) == (refused, []),
                f"{got}, {len(given)} replays",
            )
        got, given, _, _ = decide_planned(plan_claim(("ev/../outside.json", PLAIN)), root / "ev")
        expect("evidence outside the root", (got, given) == (refused, []), f"{got}, {len(given)} replays")

        # Read once: rewritten right after its read, as an editor saving it would, the evidence still replays
        # as the bytes read, and a second read, of the narrowed evidence, would refuse it.
        def rewrite(r: vc.Read) -> None:
            if r.path == root / "ev" / "a.json":
                r.path.write_bytes(NARROWED)

        got, given, by_once, opened = decide_planned(plan_claim(("ev/a.json", PLAIN)), root, rewrite)
        once = [p for p in by_once if p == root / "ev" / "a.json"]
        expect("rewritten right after its read", got == ("verified", "verified") and given == [PLAIN]
               and len(once) == 1 and not opened, f"{got}, {len(once)} reads, opened {opened}")  # fmt: skip
    finally:
        shutil.rmtree(root, ignore_errors=True)

    # read_once itself: normalizing a path can't change which file it names, and with `held`, a file is read
    # once for the whole replay.
    t = Path(tempfile.mkdtemp(prefix="verify-claims-read-"))
    try:
        (t / "real" / "sub").mkdir(parents=True)
        (t / "empty").mkdir()
        (t / "common.h").write_text("#define V 7\n")
        (t / "real" / "common.h").write_text("#define V 9\n")
        (t / "link").symlink_to(t / "real" / "sub")
        for name, path, want in [
            ("a symlink, then ..", t / "link" / ".." / "common.h", ("refused", "r")),
            ("an empty directory, then ..", t / "empty" / ".." / "common.h", ("ok", "#define V 7\n")),
        ]:
            try:
                got = ("ok", vc.read_once(path, t, "r", "x").data.decode())
            except vc.Stop as stop:
                got = (stop.status, stop.reason)
            expect(f"read_once: {name}", got == want, " ".join(got))
        held, opens = vc.Held(), []
        real_os_open = os.open
        with mock.patch("os.open", lambda f, *a, **k: opens.append(f) or real_os_open(f, *a, **k)):
            first = vc.read_once(t / "common.h", t, "r", "x", held=held)
            (t / "common.h").write_text("#define V 8\n")
            second = vc.read_once(t / "empty" / ".." / "common.h", t, "r", "x", held=held)
        expect("read_once: a file read twice in one replay", second is first and len(opens) == 1,
               f"{len(opens)} opens, the same bytes: {second.data == first.data}")  # fmt: skip
    finally:
        shutil.rmtree(t, ignore_errors=True)

    # The trees: llvm-project has to be the Nix store's, and the work area outside both trees.
    writable = Path(tempfile.mkdtemp(prefix="verify-claims-src-"))
    try:
        in_tree, outside = ("error", "work_in_tree"), Path(tempfile.gettempdir())
        for name, f, want in [
            ("a writable llvm-project", lambda: vc.immutable(writable), ("error", "toolchain_missing")),
            ("a work area in the repo", lambda: vc.outside_trees(ROOT / "build" / "w", writable), in_tree),
            ("a work area in llvm-project", lambda: vc.outside_trees(writable / "w", writable), in_tree),
            ("a work area outside both", lambda: vc.outside_trees(outside, writable), ("ok", "")),
        ]:  # fmt: skip
            try:
                f()
                got = ("ok", "")
            except vc.Stop as stop:
                got = (stop.status, stop.reason)
            expect(name, got == want, " ".join(got))
        src = os.environ.get("LLVM_PROJECT_SRC")
        if src:
            ok = vc.immutable(Path(src)).is_relative_to(vc.STORE)
            expect("the dev shell's llvm-project, in the Nix store", ok, src)
    finally:
        shutil.rmtree(writable, ignore_errors=True)
    return failures + run_lint()


# --- The lint: no read of a file's content gets around read_once -----------------------------------------

# Where tools/verify_claims.py may read or copy a file's content other than through read_once, by function and
# primitive, and how many times. Every one but read_once's own reads a file the run wrote in its private work
# area.
READS = {
    ("read_once", "open"): 1,  # os.open, with O_NOFOLLOW when asked, then fstat for a regular file
    ("read_once", "fdopen"): 1,
    ("sha256", "open"): 1,  # the hash of a file the run wrote, for `unchanged`
    ("Replay.hashes", "sha256"): 1,  # the run's directory, before and after the evidence's code runs
    ("Replay.compile_source", "read_text"): 2,  # clang's -M and -MD lists, which it writes in the work area
    ("Replay.build", "copyfile"): 1,  # the compiled IR, in the work area, when nothing is extracted from it
    ("Replay.build", "sha256"): 2,  # the IR llvm-extract wrote, and the Lean ir-lean wrote, in the work area
    ("Replay.waves", "read_text"): 1,  # the evidence's modules, as the run wrote them from read_once's bytes
}
# The primitives that read or copy a file's content: attributes on anything; shutil's own, which dict.copy
# shares a name with; names; and the modules whose aliases would hide them.
ATTRS = {"open", "fdopen", "read_bytes", "read_text", "load", "copyfile", "copyfileobj", "copytree", "copy2"}
SHUTIL = {"copy", "move"}
NAMES = {"open", "sha256"}
MODULES = {"shutil", "os", "io", "json", "tomllib", "pathlib", "builtins", "codecs"}


def reads(source: str) -> Counter[tuple[str, str]]:
    """Each use of a primitive that reads or copies a file in `source`, by the function it's in (a method as
    Class.method; a nested function or lambda counts as the function it's in) and the primitive. It's
    syntactic: it sees calls and references to these names, and imports that would rename them, not a read
    made through a name it doesn't list."""
    found: Counter[tuple[str, str]] = Counter()

    def walk(node: ast.AST, path: tuple[str, ...], in_function: bool) -> None:
        for child in ast.iter_child_nodes(node):
            p, f = path, in_function
            if isinstance(child, ast.ClassDef) and not in_function:
                p = (*path, child.name)
            elif isinstance(child, ast.FunctionDef | ast.AsyncFunctionDef) and not in_function:
                p, f = (*path, child.name), True
            where = ".".join(p) or "<module>"
            if isinstance(child, ast.Attribute) and (
                child.attr in ATTRS
                or (child.attr in SHUTIL and isinstance(child.value, ast.Name) and child.value.id == "shutil")
            ):
                found[(where, child.attr)] += 1
            elif isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load) and child.id in NAMES:
                found[(where, child.id)] += 1
            elif isinstance(child, ast.ImportFrom) and (child.module or "").split(".")[0] in MODULES:
                for a in child.names:
                    if a.name in ATTRS | SHUTIL | NAMES | {"*"}:
                        found[(where, f"from {child.module} import {a.name}")] += 1
            elif isinstance(child, ast.Import):
                for a in child.names:
                    if a.asname and a.name.split(".")[0] in MODULES:
                        found[(where, f"import {a.name} as {a.asname}")] += 1
            walk(child, p, f)

    walk(ast.parse(source), (), False)
    return found


def run_lint() -> list[str]:
    """The design's test 6, and the lint tested: a read added in a new helper, a second read in a function
    allowed one, and an alias that hides a primitive each have to fail it."""
    failures: list[str] = []
    source = (ROOT / "tools" / "verify_claims.py").read_text()
    got = reads(source)
    ok = got == Counter(READS)
    extra = {k: n for k, n in got.items() if n != READS.get(k)} | {k: 0 for k in READS if k not in got}
    print(
        f"{'ok  ' if ok else 'FAIL'} static: lint: every read of a file goes through read_once, or is listed"
    )
    if not ok:
        failures.append(f"lint: reads not through read_once, or not as listed: {extra}")
    waves = "    def waves(self, files: dict[str, str]) -> list[list[str]]:\n"
    second = waves + "        Path('x').read_bytes()\n"
    for name, changed in [
        ("a read in a new helper", source + "\n\ndef helper(p):\n    return p.read_text()\n"),
        ("a second read in a function allowed one", source.replace(waves, second)),
        ("a primitive imported by name", source + "\nfrom shutil import copyfile as cp\n"),
        ("a module imported as another name", source + "\nimport shutil as sh\n"),
        ("shutil.copy", source + "\n\ndef helper(p):\n    shutil.copy(p, 'x')\n"),
    ]:  # fmt: skip
        caught = changed != source and reads(changed) != Counter(READS)
        print(f"{'ok  ' if caught else 'FAIL'} static: lint: catches {name}")
        if not caught:
            failures.append(f"lint: doesn't catch {name}")
    return failures


# --- Live cases -------------------------------------------------------------------------------------------

ASHLDI3 = """import CrtAshldi3
import Kit

namespace Llvm

theorem ashldi3_correct (a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshldi3._ashldi3 (some a) (some b) =
      IRLean.Outcome.ok (some (a <<< b)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtAshldi3._ashldi3
  all_goals llvm_close
"""

STATEMENT = """(a : BitVec 64) (b : BitVec 32) (h : b < 64#32) :
    CrtAshldi3._ashldi3 (some a) (some b) = IRLean.Outcome.ok (some (a <<< b))"""


def proof(body: str) -> str:
    return f"import CrtAshldi3\nimport Kit\nimport Lean\n\nnamespace Llvm\n\n{body}\n\nend Llvm\n"


# Each forged proof module stands in for tests/llvm/Ashldi3.lean, with its hash recorded, so only what it says
# can refuse it.
TACTICS = "  simp only [IRLean.Outcome.ok]\n  llvm_exec CrtAshldi3._ashldi3\n  all_goals llvm_close"
WEAKER = proof(f"theorem ashldi3_correct {STATEMENT.replace('64#32)', '1#32)')} := by\n{TACTICS}")
AXIOM = proof(f"axiom shifts {STATEMENT}\n\ntheorem ashldi3_correct {STATEMENT} := shifts a b h")
SORRY = proof(f"theorem ashldi3_correct {STATEMENT} := by sorry")
SKIPPED = proof(
    "open Lean Elab Command in\nset_option debug.skipKernelTC true in\n"
    "run_cmd liftCoreM <| addDecl <| .thmDecl {\n"
    "  name := `Llvm.oops, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n\n"
    f"theorem ashldi3_correct {STATEMENT} := oops.elim"
)
OWN_DEFINITION = proof(
    "def shifted (a : BitVec 64) (b : BitVec 32) : BitVec 64 := a <<< b\n\n"
    f"theorem ashldi3_correct {STATEMENT.replace('(a <<< b)', '(shifted a b)')} := by\n"
    "  simp only [IRLean.Outcome.ok, shifted]\n  llvm_exec CrtAshldi3._ashldi3\n  all_goals llvm_close"
)
# The proof defines the generated function's name itself, and imports nothing ir-lean generated.
NAMED_LIKE_TARGET = (
    "import Kit\n\nnamespace CrtAshldi3\n\n"
    "def _ashldi3 (a : Option (BitVec 64)) (b : Option (BitVec 32)) :\n"
    "    IRLean.Outcome (Option (BitVec 64)) :=\n"
    "  IRLean.Outcome.ok (match a, b with | some a, some b => some (a <<< b) | _, _ => none)\n\n"
    f"end CrtAshldi3\n\nnamespace Llvm\n\ntheorem ashldi3_correct {STATEMENT} := rfl\n\nend Llvm\n"
)
REWRITES_GENERATED = (
    ASHLDI3 + "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/CrtAshldi3.lean") "-- rewritten\\n"\n'
)
MAKES_INIT = (
    ASHLDI3 + "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/Shadow.olean") "x"\n'
)
SLEEPS = ASHLDI3 + "\n#eval IO.sleep 120000\n"


def edit_proof(text: str) -> Callable[[dict[str, Any], Path], None]:
    def edit(ev: dict[str, Any], lean_dir: Path) -> None:
        (lean_dir / "Ashldi3.lean").write_text(text)
        ev["lean"]["files"]["Ashldi3"] = sha(lean_dir / "Ashldi3.lean")

    return edit


def edit_evidence(change: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any], Path], None]:
    def edit(ev: dict[str, Any], lean_dir: Path) -> None:
        change(ev)

    return edit


def set_anchor(ev: dict[str, Any]) -> None:
    anchors = ev["units"][0]["anchors"]
    anchors["compiler-rt/lib/builtins/ashldi3.c"] = "0" * 64


def drop_anchor(ev: dict[str, Any]) -> None:
    ev["units"][0]["anchors"].pop("compiler-rt/lib/builtins/int_lib.h")


def other_pin(ev: dict[str, Any]) -> None:
    ev["llvm"]["commit"] = "0" * 40


def other_flags(ev: dict[str, Any]) -> None:
    ev["units"][0]["flags"] = [f if f != "-O3" else "-O0" for f in ev["units"][0]["flags"]]


def edited_lean(ev: dict[str, Any]) -> None:
    ev["units"][0]["lean_sha256"] = "0" * 64


def other_statement(ev: dict[str, Any]) -> None:
    ev["theorems"][0]["statement_sha256"] = hashing.sha256(b"(c 1:_ [])")


def reworded(ev: dict[str, Any]) -> None:
    ev["theorems"][0]["statement"] = ev["theorems"][0]["statement"].replace("64#32", "64")


def extra_field(ev: dict[str, Any]) -> None:
    ev["units"][0]["trusted"] = True


def cut(ev: dict[str, Any]) -> None:
    ev["cuts"] = ["__ashlti3"]


def listed_twice(ev: dict[str, Any]) -> None:
    ev["theorems"].append(copy.deepcopy(ev["theorems"][0]) | {"about": ["__ashlti3"]})


def plugin(ev: dict[str, Any]) -> None:
    ev["units"][0]["flags"].append("-fplugin=/tmp/anything.so")


def stand_in(ev: dict[str, Any], lean_dir: Path) -> None:
    """A unit of hand-written IR defining the same symbol, listed first, so it could stand in for the compiled
    function in a closure's coverage."""
    ll = lean_dir / "StandIn.ll"
    layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
    ll.write_text(
        f'target datalayout = "{layout}"\ntarget triple = "x86_64-unknown-linux-gnu"\n\n'
        "define i64 @__ashldi3(i64 noundef %a, i32 noundef %b) {\n  ret i64 %a\n}\n"
    )
    ir = copy.deepcopy(ev["units"][0]) | {
        "source": str(ll.relative_to(ROOT)), "source_in": "repo", "language": "ir", "flags": [],
        "include": [], "local_include": [], "llvm_config": False, "namespace": "StandIn", "translate": [],
        "anchors": {}, "repo_files": {str(ll.relative_to(ROOT)): sha(ll)}, "ir_sha256": sha(ll),
    }  # fmt: skip
    # Its own translation's hash, recorded as a forger would, so only the symbol defined twice is wrong.
    argv = [str(ROOT / "build" / "ir-lean"), "StandIn.ll", "--namespace", "StandIn", "-o", "StandIn.lean"]
    r = proc.run(argv, cwd=lean_dir, timeout=300)
    if r.exit != 0:
        raise SystemExit(f"FAIL ir-lean on the stand-in: {r.stderr.decode(errors='replace')}")
    ir["lean_sha256"] = sha(lean_dir / "StandIn.lean")
    ev["units"].insert(0, ir)


# name, how the good evidence is changed, the status and reason it has to get.
CASES: list[tuple[str, Callable[[dict[str, Any], Path], None], str, str]] = [
    ("wrong statement: a weaker hypothesis", edit_proof(WEAKER), "refused", "statement_mismatch"),
    (
        "wrong statement: another statement's hash",
        edit_evidence(other_statement),
        "refused",
        "statement_mismatch",
    ),
    ("wrong statement: printed differently", edit_evidence(reworded), "refused", "statement_mismatch"),
    (
        "wrong statement: a definition of the proof's own",
        edit_proof(OWN_DEFINITION),
        "refused",
        "foreign_constant",
    ),
    (
        "wrong statement: about a function named like the target",
        edit_proof(NAMED_LIKE_TARGET),
        "refused",
        "foreign_constant",
    ),
    ("stale anchors: the source's hash", edit_evidence(set_anchor), "refused", "stale_anchors"),
    ("stale anchors: a header left out", edit_evidence(drop_anchor), "refused", "stale_anchors"),
    ("stale anchors: another llvm-project", edit_evidence(other_pin), "refused", "stale_anchors"),
    ("extra axiom", edit_proof(AXIOM), "refused", "disallowed_axiom"),
    ("sorry", edit_proof(SORRY), "refused", "sorry"),
    ("kernel check skipped", edit_proof(SKIPPED), "refused", "kernel_replay_failed"),
    ("other flags", edit_evidence(other_flags), "refused", "ir_replay_mismatch"),
    ("edited translation", edit_evidence(edited_lean), "refused", "translation_replay_mismatch"),
    ("an extra field", edit_evidence(extra_field), "refused", "evidence_invalid"),
    ("proof rewrites a generated module", edit_proof(REWRITES_GENERATED), "error", "artifacts_modified"),
    ("proof adds a module where Lean looks", edit_proof(MAKES_INIT), "error", "artifacts_modified"),
    ("a call cut out", edit_evidence(cut), "partial", "cut"),
    (
        "a theorem listed twice, about another function",
        edit_evidence(listed_twice),
        "refused",
        "evidence_invalid",
    ),
    ("a flag that loads a plugin into clang", edit_evidence(plugin), "refused", "evidence_invalid"),
    ("the function also defined by hand-written IR", stand_in, "refused", "evidence_invalid"),
]


def slug(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name)


# What read_once's file is overwritten with, right after it's read, by its suffix: bytes no replay could pass
# with.
OTHER = {
    ".lean": SORRY.encode(),
    ".ll": b"define i32 @other() {\n  ret i32 0\n}\n",
    ".c": b"#error rewritten after its read\n",
    ".h": b"#error rewritten after its read\n",
    ".json": b"{}",
}


class Live:
    def __init__(self, jobs: int) -> None:
        self.jobs = jobs
        WORK.mkdir(parents=True, exist_ok=True)
        # What evidence names has to be in the repo, and where a replay works has to be outside it.
        self.tree = Path(tempfile.mkdtemp(prefix="run-", dir=WORK))
        self.work = Path(tempfile.mkdtemp(prefix="verify-claims-test-"))

    def replay(self, ev: dict[str, Any], name: str, record: bool = False, **opts: Any) -> tuple[dict, Any]:
        started = time.monotonic()
        d = self.work / slug(name)
        d.mkdir(parents=True, exist_ok=True)
        data = json.dumps(ev).encode()
        v, out = vc.replay_evidence(data, work=d, jobs=self.jobs, record=record, **opts)
        v = v.verdict if isinstance(v, vc.Replayed) else v
        print(f"     {name}: {v['status']} {v['reason']} in {time.monotonic() - started:.1f} s")
        return v, out

    def cli(self, ev: dict[str, Any], name: str, *args: str, deny: str = "", work: Path | None = None,
            env: dict[str, str] | None = None) -> tuple[dict[str, Any], int]:  # fmt: skip
        """Replays `ev` as a reader does, with tools/verify_claims.py evidence and IRLEAN_DENY_ALL set to
        `deny`, working in `work`: the verdict it prints, and its exit code."""
        started = time.monotonic()
        d = self.work / slug(name)
        d.mkdir(parents=True, exist_ok=True)
        (d / "evidence.json").write_text(json.dumps(ev))
        argv = [str(ROOT / "tools" / "verify_claims.py"), "evidence", str(d / "evidence.json"),
                "--work", str(work or d / "work"), "--jobs", str(self.jobs), *args]  # fmt: skip
        r = proc.run(argv, env={**os.environ, DENY_ALL: deny, **(env or {})}, timeout=1800)
        try:
            v = json.loads(r.out)
        except json.JSONDecodeError:
            v = {"status": "no answer", "reason": f"exit {r.exit}", "detail": r.err[-2000:]}
        took = time.monotonic() - started
        print(f"     {name}: {v['status']} {v['reason']}, exit {r.exit}, in {took:.1f} s")
        return v, r.exit

    def good(self) -> dict[str, Any]:
        v, ev = self.replay(corpus(["CrtAshldi3"], model_proofs=False), "record ashldi3", record=True)
        if v["status"] != "replayed":
            raise SystemExit(f"FAIL recording the good evidence: {v['reason']}: {v['detail']}")
        return ev

    def corpus(self, failures: list[str]) -> None:
        """Every function tests/llvm.py proves, replayed as one piece of evidence."""
        ev = corpus()
        v, recorded = self.replay(ev, "every target tests/llvm.py proves", record=True)
        n = len(ev["theorems"])
        if v["status"] != "replayed":
            failures.append(f"corpus: {v['status']} {v['reason']}: {v['detail'][:3000]}")
            print(f"FAIL corpus: the verifier refuses what tests/llvm.py proves: {v['reason']}")
            return
        print(f"ok   corpus: {n} theorems about {len(recorded['units'])} units of LLVM's code replay")

    def scorer(self, failures: list[str]) -> None:
        """Every control tools/verify.py, the scorer's checker, certifies in tests/verification_negative, with
        the same IR and proof: the verifier has to replay each, and tools/verify.py has to prove each here
        too."""
        pin = tomllib.loads(TARGETS.read_text())["project"]
        cases = sorted((ROOT / "tests" / "verification_negative" / "cases").glob("control_*"))
        if not cases:
            failures.append("scorer: no controls in tests/verification_negative")
        for case in cases:
            manifest = json.loads((case / "case.json").read_text())
            if not manifest["expect"]["certified"]:
                continue
            request = manifest["request"]
            d = self.tree / f"scorer-{case.name}"
            shutil.copytree(case, d)
            (d / "request.json").write_text(json.dumps(request))
            r = proc.run([str(ROOT / "tools" / "verify.py"), "check", str(d / "request.json")], timeout=900)
            try:
                scored = json.loads(r.out)["status"]
            except (json.JSONDecodeError, KeyError):
                scored = f"no answer: {r.err[-2000:]}"
            proof = request["proof"].removesuffix(".lean")
            ir = unit({"flags": {"none": {}}}, {"source": "", "flags": "none", "module": ""})
            ir |= {"source": str((case / request["input"]["ir"]).relative_to(ROOT)), "source_in": "repo",
                   "language": "ir", "namespace": request["namespace"], "translate": []}  # fmt: skip
            about = [n.removeprefix(request["namespace"] + ".") for n in manifest["names"]]
            ev = {
                "schema": vc.EVIDENCE_SCHEMA,
                "llvm": {k: pin[k] for k in ("tag", "commit", "nix_hash")},
                "lean_version": "",
                "units": [ir],
                "lean": {"root": str(case.relative_to(ROOT)), "files": {proof: ""}, "model": []},
                "theorems": [{"module": proof, "name": request["theorem"], "about": about, "statement": "",
                              "statement_sha256": ""}],
                "cuts": [],
                "contexts": "all",
            }  # fmt: skip
            v, _ = self.replay(ev, f"verifier on {case.name}", record=True)
            ok = scored == "proved" and v["status"] == "replayed"
            mark = "ok  " if ok else "FAIL"
            print(f"{mark} scorer: tools/verify.py says {scored}, the verifier {v['status']}, on {case.name}")
            if not ok:
                got = f"verify.py {scored}, verifier {v['status']} {v['reason']}: {v['detail'][:2000]}"
                failures.append(f"scorer {case.name}: {got}")

    def cases(self, good: dict[str, Any], only: list[str] | None, failures: list[str]) -> None:
        for name, change, status, reason in CASES:
            if only and not any(o in name for o in only):
                continue
            ev = copy.deepcopy(good)
            lean_dir = self.tree / ("lean-" + str(abs(hash(name))))
            shutil.copytree(ROOT / "tests" / "llvm", lean_dir)
            ev["lean"]["root"] = str(lean_dir.relative_to(ROOT))
            change(ev, lean_dir)
            v, code = self.cli(ev, name)
            ok = (v["status"], v["reason"], code) == (status, reason, vc.EXIT[status])
            print(f"{'ok  ' if ok else 'FAIL'} forged: {name}: {v['status']} {v['reason']}, exit {code}")
            if not ok:
                got = f"{v['status']} {v['reason']}, exit {code}: {v['detail'][:2000]}"
                want = f"{status} {reason}, exit {vc.EXIT[status]}"
                failures.append(f"forged {name}: wanted {want}, got {got}")

    def guard(self, good: dict[str, Any], only: list[str] | None, failures: list[str]) -> None:
        """docs/verdicts.md's test 8, through replay_evidence and main: a replay that skipped a step, by a bug
        here or a caller's, isn't replayed, and IRLEAN_DENY_ALL takes the grant away, with no record and a
        non-zero exit."""
        kernel, passed = vc.Replay.kernel, vc.Replay.passed

        def one_short(r: vc.Replay) -> None:
            # leanchecker replays every module but the evidence's last, as a list built short would.
            files = r.ev["lean"]["files"]
            last = list(files)[-1]
            h = files.pop(last)
            try:
                kernel(r)
            finally:
                files[last] = h

        def twice(r: vc.Replay, name: str, detail: str = "") -> None:
            # The anchors' check counted twice, as one passed in a loop over units would be.
            for _ in range(1 + (name == "anchors")):
                passed(r, name, detail)

        for name, method, step in [("the kernel's replay skipped", "kernel", lambda r: None),
                                   ("the kernel's replay a module short", "kernel", one_short),
                                   ("a check passed twice", "passed", twice)]:  # fmt: skip
            if only and not any(o in name for o in only):
                continue
            with mock.patch.object(vc.Replay, method, step):
                v, _ = self.replay(good, name)
            ok = (v["status"], v["reason"]) == INCOMPLETE
            print(f"{'ok  ' if ok else 'FAIL'} guard: {name}: {v['status']} {v['reason']}")
            if not ok:
                failures.append(f"guard {name}: wanted error incomplete, got {v['status']} {v['reason']}")
        if only and not any(o in DENY_ALL for o in only):
            return
        for deny, want, code in [("", ("replayed", "replayed"), 0), ("1", ("error", "denied"), 5)]:
            record = self.work / f"deny-{deny or 'unset'}.json"
            v, got = self.cli(good, f"{DENY_ALL}={deny}", "--record", str(record), deny=deny)
            ok = (v["status"], v["reason"], got, record.exists()) == (*want, code, code == 0)
            said = (
                f"{v['status']} {v['reason']}, exit {got}, record {'written' if record.exists() else 'none'}"
            )
            print(f"{'ok  ' if ok else 'FAIL'} guard: {DENY_ALL}={deny}: {said}")
            if not ok:
                failures.append(f"guard {DENY_ALL}={deny}: wanted {' '.join(want)}, exit {code}, got {said}")

    def limits(self, good: dict[str, Any], failures: list[str]) -> None:
        """A proof that outlasts the time it's given is unknown, never refused or replayed."""
        ev = copy.deepcopy(good)
        lean_dir = self.tree / "lean-sleeps"
        shutil.copytree(ROOT / "tests" / "llvm", lean_dir)
        ev["lean"]["root"] = str(lean_dir.relative_to(ROOT))
        edit_proof(SLEEPS)(ev, lean_dir)
        v, _ = self.replay(ev, "a proof that sleeps past the time limit", timeout=20)
        ok = v["status"] == "unknown"
        print(f"{'ok  ' if ok else 'FAIL'} limit: a proof past its time limit is {v['status']} {v['reason']}")
        if not ok:
            failures.append(f"limit: wanted unknown, got {v['status']} {v['reason']}")

    def claims(self, good: dict[str, Any], failures: list[str]) -> None:
        """A complete code-binding claim for a pass whose closure is one function: verified, and refused when
        the closure has a function no theorem is about, or the evidence is for some contexts or changed."""
        inv = json.loads(vc.INVENTORY.read_text())
        anchors = good["units"][0]["anchors"]
        item = {"id": "pass:toy-shift", "name": "toy-shift", "anchors": anchors, "unresolved_classes": []}
        inv["items"] = [item]
        d = self.tree / "claims"
        (d / "closure").mkdir(parents=True)
        (d / "inventory.json").write_text(json.dumps(inv))
        evidence = d / "toy-shift.evidence.json"
        evidence.write_text(json.dumps(good))
        source = "compiler-rt/lib/builtins/ashldi3.c"
        functions: list[dict[str, str]] = [{"symbol": "__ashldi3", "file": source}]
        closure = {"schema": vc.CLOSURE_SCHEMA, "complete": True, "files": anchors, "functions": functions}
        c = {"item": "pass:toy-shift", "dimension": "code-binding", "contexts": "all", "status": "complete",
             "anchors": anchors, "gaps": [], "evidence": [{"kind": "binding-check",
             "path": str(evidence.relative_to(ROOT)), "sha256": sha(evidence)}]}  # fmt: skip
        uncovered = closure | {"functions": [*functions, {"symbol": "__ashlti3", "file": source}]}
        some = copy.deepcopy(good) | {"contexts": ["opt:default<O2>"]}
        some_path = evidence.with_name("toy-shift-some.evidence.json")
        some_path.write_text(json.dumps(some))
        c_some = c | {"evidence": [{"kind": "binding-check", "path": str(some_path.relative_to(ROOT)),
                                    "sha256": sha(some_path)}]}  # fmt: skip
        for name, cl, clo, want in [
            ("a pass whose closure is one proved function", c, closure, ("verified", "verified")),
            ("a closure function no theorem is about", c, uncovered, ("refused", "closure_uncovered")),
            ("evidence for only some contexts", c_some, closure, ("refused", "contexts_uncovered")),
            ("evidence changed since the claim", c | {"evidence": [{**c["evidence"][0], "sha256": "0" * 64}]},
             closure, ("refused", "stale_evidence")),
        ]:  # fmt: skip
            (d / "closure" / "toy-shift.json").write_text(json.dumps(clo))
            v = vc.decide_claim(cl, inventory=d / "inventory.json", closures=d / "closure",
                                replay_options={"jobs": self.jobs})  # fmt: skip
            ok = (v["status"], v["reason"]) == want
            print(f"{'ok  ' if ok else 'FAIL'} claim: {name}: {v['status']} {v['reason']}")
            if not ok:
                failures.append(
                    f"claim {name}: wanted {want}, got {v['status']} {v['reason']}: {v['detail'][:2000]}"
                )


class Identity:
    """The design's tests 7 to 9, over real replays: each file read_once reads is overwritten right after,
    and the replay is still `replayed`, having read exactly the files it rests on; the repo changed while
    clang runs changes nothing; and changed between `clang -M` and the copy, it's never `replayed`."""

    def __init__(self, live: Live, good: dict[str, Any], failures: list[str]) -> None:
        self.live, self.failures = live, failures
        self.c = live.tree / "repo-c"  # the good evidence, with a unit of the repo's own C and its own header
        self.ir = live.tree / "ir-only"  # a tests/verification_negative control: IR, and a proof of it
        self.lay_out()
        ev = copy.deepcopy(good)
        ev["lean"]["root"] = str((self.c / "lean").relative_to(ROOT))
        c_unit = copy.deepcopy(good["units"][0]) | {
            "source": str((self.c / "src" / "k.c").relative_to(ROOT)), "source_in": "repo", "language": "c",
            "flags": ["-O2"], "include": [], "local_include": [], "llvm_config": False, "extract": [],
            "namespace": "ReproK", "anchors": {}, "repo_files": {}, "ir_sha256": "", "lean_sha256": "",
        }  # fmt: skip
        ev["units"].append(c_unit)
        self.c_ev = self.record(ev, "record the evidence with the repo's own C")
        # Two more units: one including the same header, and one reaching it through an empty directory and
        # `..`. Each file has to be read once for the whole replay, and the copy has to have the empty
        # directory.
        ev = copy.deepcopy(self.c_ev)
        for n, unit_ in enumerate(["k2.c", "k3.c"]):
            ev["units"].append(c_unit | {"source": str((self.c / "src" / unit_).relative_to(ROOT)),
                                         "namespace": f"ReproK{n + 2}"})  # fmt: skip
        self.many_ev = self.record(ev, "record three units of the repo's C sharing a header")
        # A header reached through a symlink to a directory, then `..`, which the kernel resolves to another
        # file than the path's normal form names. A copy can't reproduce that, so it's refused, not replayed.
        ev = copy.deepcopy(self.c_ev)
        ev["units"].append(
            c_unit | {"source": str((self.c / "src" / "k4.c").relative_to(ROOT)), "namespace": "ReproV"}
        )
        self.lay_out()
        v, _ = self.live.replay(ev, "record a header through a symlink, then ..", record=True)
        self.check("a header through a symlink, then ..: refused when recording", v["status"] == "refused",
                   f"{v['status']} {v['reason']}: {v['detail'][:500]}")  # fmt: skip
        case = sorted((ROOT / "tests" / "verification_negative" / "cases").glob("control_*"))[0]
        manifest = json.loads((case / "case.json").read_text())
        request, pin = manifest["request"], tomllib.loads(TARGETS.read_text())["project"]
        self.proof = request["proof"].removesuffix(".lean")
        self.ir_file = self.ir / request["input"]["ir"]
        ir = unit({"flags": {"none": {}}}, {"source": "", "flags": "none", "module": ""}) | {
            "source": str(self.ir_file.relative_to(ROOT)), "source_in": "repo", "language": "ir",
            "namespace": request["namespace"], "translate": [],
        }  # fmt: skip
        about = [n.removeprefix(request["namespace"] + ".") for n in manifest["names"]]
        ev = {"schema": vc.EVIDENCE_SCHEMA, "llvm": {k: pin[k] for k in ("tag", "commit", "nix_hash")},
              "lean_version": "", "units": [ir],
              "lean": {"root": str(self.ir.relative_to(ROOT)), "files": {self.proof: ""}, "model": []},
              "theorems": [{"module": self.proof, "name": request["theorem"], "about": about, "statement": "",
                            "statement_sha256": ""}], "cuts": [], "contexts": "all"}  # fmt: skip
        self.case = case
        self.lay_out()
        self.ir_ev = self.record(ev, "record the evidence with IR only")

    def lay_out(self) -> None:
        """Writes the trees the two pieces of evidence name, afresh."""
        for d in (self.c, self.ir):
            shutil.rmtree(d, ignore_errors=True)
        shutil.copytree(ROOT / "tests" / "llvm", self.c / "lean")
        (self.c / "src" / "inc").mkdir(parents=True)
        (self.c / "src" / "inc" / "k.h").write_text("#define K 7\n")
        (self.c / "src" / "k.c").write_text('#include "inc/k.h"\nint plus_k(int a) { return a + K; }\n')
        (self.c / "src" / "k2.c").write_text('#include "inc/k.h"\nint times_k(int a) { return a * K; }\n')
        (self.c / "src" / "empty").mkdir()
        (self.c / "src" / "k3.c").write_text(
            '#include "empty/../inc/k.h"\nint minus_k(int a) { return a - K; }\n'
        )
        (self.c / "src" / "real" / "sub").mkdir(parents=True)
        (self.c / "src" / "real" / "sub" / "inside.h").write_text('#include "../common.h"\n')
        (self.c / "src" / "real" / "common.h").write_text("#define V 9\n")
        (self.c / "src" / "common.h").write_text("#define V 7\n")
        (self.c / "src" / "link").symlink_to(self.c / "src" / "real" / "sub")
        (self.c / "src" / "k4.c").write_text('#include "link/inside.h"\nint v(void) { return V; }\n')
        if hasattr(self, "case"):
            shutil.copytree(self.case, self.ir)

    def record(self, ev: dict[str, Any], name: str) -> dict[str, Any]:
        v, recorded = self.live.replay(ev, name, record=True)
        if v["status"] != "replayed":
            raise SystemExit(f"FAIL {name}: {v['status']} {v['reason']}: {v['detail'][:3000]}")
        return recorded

    def check(self, name: str, ok: bool, got: str) -> None:
        print(f"{'ok  ' if ok else 'FAIL'} identity: {name}: {got}")
        if not ok:
            self.failures.append(f"identity {name}: {got}")

    def rewritten(self, name: str, ev: dict[str, Any], mine: Path, expect: set[Path]) -> None:
        """Test 7: tools/verify_claims.py evidence, in this process, with each file under `mine` that
        read_once reads overwritten right after its read. It has to be `replayed`, and read_once has to have
        read exactly `expect` under `mine`, and the pin, each once."""
        self.lay_out()
        evidence = mine / "evidence.json"
        evidence.write_text(json.dumps(ev))
        reads: dict[Path, list[vc.Read]] = {}
        real = vc.read_once

        def read_once(path: Path, *args: Any, **kw: Any) -> vc.Read:
            r = real(path, *args, **kw)
            # A read from the file gives a new Read; one the replay holds gives the same one again. Units run
            # at once, so that's the only way to tell them apart that doesn't race.
            known = reads.setdefault(r.path, [])
            if not any(x is r for x in known):
                known.append(r)
                if r.path.is_relative_to(mine):
                    r.path.write_bytes(OTHER.get(r.path.suffix, b"rewritten after its read\n"))
            return r

        out = io.StringIO()
        work = self.live.work / slug(name)
        work.mkdir(parents=True, exist_ok=True)
        argv = [
            "verify_claims.py",
            "evidence",
            str(evidence),
            "--work",
            str(work),
            "--jobs",
            str(self.live.jobs),
        ]
        with (mock.patch.object(vc, "read_once", read_once), mock.patch.object(sys, "argv", argv),
              contextlib.redirect_stdout(out)):  # fmt: skip
            code = vc.main()
        v = json.loads(out.getvalue())
        seen = Counter({p: len(rs) for p, rs in reads.items()})
        read = {p for p in seen if p.is_relative_to(mine)} | ({vc.PIN} & set(seen))
        want = expect | {evidence, vc.PIN}
        missed, extra = sorted(map(str, want - read)), sorted(map(str, read - want))
        twice = sorted(str(p) for p in read if seen[p] != 1)
        self.check(f"{name}: each file rewritten right after its read, and read once",
                   (v["status"], code, read, twice) == ("replayed", 0, want, []),
                   f"{v['status']} {v['reason']}, exit {code}: unread {missed}, extra {extra}, "
                   f"twice {twice}")  # fmt: skip

    def during_clang(
        self, name: str, flag: str, change: Callable[[], None], want: set[tuple[str, str]]
    ) -> None:
        """Tests 8 and 9: `change` runs right after clang's `flag` pass over the repo's C."""
        self.lay_out()
        real = vc.run

        def run(argv: list[str], **kw: Any) -> vc.Ran:
            r = real(argv, **kw)
            if argv[0] == "clang" and flag in argv and argv[-1].endswith("k.c"):
                change()
            return r

        with mock.patch.object(vc, "run", run):
            v, _ = self.live.replay(self.c_ev, name)
        self.check(
            name, (v["status"], v["reason"]) in want, f"{v['status']} {v['reason']}: {v['detail'][:500]}"
        )

    def run(self) -> None:
        lean = {self.c / "lean" / f"{m.replace('.', '/')}.lean" for m in self.c_ev["lean"]["files"]}
        self.rewritten(
            "the repo's C", self.c_ev, self.c, lean | {self.c / "src" / "k.c", self.c / "src" / "inc" / "k.h"}
        )
        self.rewritten("IR only", self.ir_ev, self.ir, {self.ir / f"{self.proof}.lean", self.ir_file})
        src = self.c / "src"
        self.rewritten("three units of the repo's C sharing a header", self.many_ev, self.c,
                       lean | {src / "k.c", src / "k2.c", src / "k3.c", src / "inc" / "k.h"})  # fmt: skip
        inc = self.c / "src" / "inc"

        def swapped() -> None:
            # The header's directory moved away, and in its place, the header a symlink to other text.
            inc.rename(self.c / "src" / "inc.old")
            (self.c / "src" / "elsewhere").mkdir()
            (self.c / "src" / "elsewhere" / "k.h").write_text("#define K 8\n")
            inc.mkdir()
            (inc / "k.h").symlink_to(self.c / "src" / "elsewhere" / "k.h")

        def rewrite_header() -> None:
            (inc / "k.h").write_text("#define K 9\n")

        self.during_clang("the header swapped for a symlink, in a new directory, while clang compiles", "-MD",
                          swapped, {("replayed", "replayed")})  # fmt: skip
        self.during_clang("the header rewritten between clang -M and the copy", "-M",
                          rewrite_header,
                          {("refused", "stale_evidence"), ("error", "artifacts_modified")})  # fmt: skip
        # The trees: llvm-project has to be the Nix store's, and the work area outside both trees.
        writable = Path(tempfile.mkdtemp(prefix="verify-claims-src-"))
        try:
            for name, work, env, want in [
                ("a work area in the repo", self.live.tree / "work", {}, ("error", "work_in_tree", 5)),
                ("a writable llvm-project", None, {"LLVM_PROJECT_SRC": str(writable)},
                 ("error", "toolchain_missing", 5)),
            ]:  # fmt: skip
                v, code = self.live.cli(self.c_ev, name, work=work, env=env)
                self.check(
                    name,
                    (v["status"], v["reason"], code) == want,
                    f"{v['status']} {v['reason']}, exit {code}",
                )
        finally:
            shutil.rmtree(writable, ignore_errors=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tier", choices=["static", "live", "all"], default="all")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("LEAN_JOBS", "4")))
    args = ap.parse_args()
    # Set where this runs, it would take every grant away the tests expect.
    os.environ.pop(DENY_ALL, None)
    failures: list[str] = []
    if args.tier in ("static", "all"):
        failures += run_static()
    if args.tier in ("live", "all"):
        live = Live(args.jobs)
        try:
            good = live.good()
            if not args.only:
                live.corpus(failures)
                live.scorer(failures)
                live.limits(good, failures)
                live.claims(good, failures)
            live.guard(good, args.only, failures)
            live.cases(good, args.only, failures)
            if not args.only or any("identity" in o for o in args.only):
                Identity(live, good, failures).run()
        finally:
            shutil.rmtree(live.work, ignore_errors=True)
            shutil.rmtree(live.tree, ignore_errors=True)
    for f in failures:
        print(f"FAIL {f}", file=sys.stderr)
    print(f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
