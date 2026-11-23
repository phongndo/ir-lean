#!/usr/bin/env python3
"""bench/kernels/variants.py, without a build: docs/kernels.md's "what a variant is".

On evidence written here, as bench/kernels/builder.py writes it: evidence that's whole and right is a variant;
every change of one leaf to its shape, a key dropped or added or a value of another type, is refused; a
result that was there before, one that's missing, a check's command or a run that failed, a table the build
didn't follow, each take the variant away; a result or an output that's another one is the named negative,
and only where the build is whole and every check and run completed; a command that was stopped is unknown;
and IRLEAN_DENY_ALL takes both grants away.

On a scratch repository: a checkout whose tracked files differ from HEAD is refused, and a commit archives to
its own bytes, whatever the checkout holds by then. On the manifest, altered: a `run` of two commands, a
program outside the build, a placeholder a build doesn't fill in, and a known-answers check with no `run`
don't evaluate. And a section that's missing or empty is an error.

It needs git, nix, clang and llvm-objcopy, which the dev shell has, and builds nothing with Nix.
"""

import copy
import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "bench" / "kernels"
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(HERE))
from irlean import proc, schemas  # noqa: E402
from irlean.verdict import DENY_ALL, Step  # noqa: E402


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


variants = load("variants", HERE / "variants.py")
PIC, OTHER = "src/libsodium/a/.libs/x.o", "src/libsodium/a/x.o"
UNIT = "/nix/store/s-source/src/libsodium/a/x.c"
STEPS = {name: Step(name, 0) for name in ("snapshot", "evaluate", "realize")}


def sha(digit: str) -> str:
    return digit * 64


PLACEHOLDER, OUT = "/1rz-placeholder", "/nix/store/o"
CHECK = [["make", "clean"], ["make", "check"]]
BUILD = [["/nix/store/s-source/configure"], ["make"], ["make", "bench"]]


def planned() -> dict[str, Any]:
    """What variants.nix plans, with the output named by its placeholder."""
    return copy.deepcopy(
        {
            "out": PLACEHOLDER,
            "table": [PIC, OTHER],
            "replace": {PIC: "/ir/pic", OTHER: "/ir/other"},
            "attempt": "default",
            "build": BUILD,
            "workloads": [
                {
                    "name": "argon2id",
                    "run": {
                        "env": {"LD_LIBRARY_PATH": f"{PLACEHOLDER}/lib"},
                        "argv": [f"{PLACEHOLDER}/bench"],
                    },
                    "checks": [
                        {
                            "run": CHECK,
                            "expected": "/nix/store/s-source/x.exp",
                            "result": f"{PLACEHOLDER}/x.res",
                        }
                    ],
                    "outputs": [],
                },
                {
                    "name": "secretstream",
                    "run": {"env": {}, "argv": [f"{PLACEHOLDER}/secretstream"]},
                    "checks": [],
                    "outputs": [sha("b")],
                },
            ],
        }
    )


def evidence() -> dict[str, Any]:
    """What a build that follows `planned` and is right writes down."""
    return copy.deepcopy(
        {
            "schema": schemas.KERNELS_EVIDENCE,
            "out": OUT,
            "attempt": "default",
            "dispatch": {"avx2": True, "avx512f": True},
            "build": [{"argv": argv, "exit": 0, "limit": None} for argv in BUILD],
            "replaced": {PIC: sha("1"), OTHER: sha("2")},
            "compiled": {
                PIC: UNIT,
                OTHER: UNIT,
                "src/libsodium/b/y.o": "/nix/store/s-source/src/libsodium/b/y.c",
            },
            "checks": [
                {
                    "workload": "argon2id",
                    "comparison": "equal",
                    "commands": [{"argv": argv, "exit": 0, "limit": None} for argv in CHECK],
                    "expected": "/nix/store/s-source/x.exp",
                    "expected_sha256": sha("a"),
                    "expected_size": 9,
                    "result": f"{OUT}/x.res",
                    "result_before": False,
                    "result_sha256": sha("a"),
                    "result_size": 9,
                }
            ],
            "runs": [
                {
                    "workload": "argon2id",
                    "env": {"LD_LIBRARY_PATH": f"{OUT}/lib"},
                    "program": f"{OUT}/bench",
                    "argv": [f"{OUT}/bench"],
                    "exit": 0,
                    "limit": None,
                    "stdout_sha256": sha("c"),
                    "stdout_size": 30,
                },
                {
                    "workload": "secretstream",
                    "env": {},
                    "program": f"{OUT}/secretstream",
                    "argv": [f"{OUT}/secretstream"],
                    "exit": 0,
                    "limit": None,
                    "stdout_sha256": sha("b"),
                    "stdout_size": 65,
                },
            ],
        }
    )


def said(e: Any = None, p: Any = None, steps: Any = None) -> tuple[str, str]:
    """The status and reason of a build with this evidence, plan and steps, each as above unless given."""
    try:
        with mock.patch.object(variants, "verify_artifacts", return_value=True):
            answer, _ = variants.answer_of(
                planned() if p is None else p,
                evidence() if e is None else e,
                STEPS if steps is None else steps,
            )
    except variants.Refused as refused:
        answer = variants.said(None, refused.reason, refused.detail)
    return answer["status"], answer["reason"]


def at(root: Any, path: tuple[Any, ...]) -> Any:
    for step in path:
        root = root[step]
    return root


def nodes(value: Any, path: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
    """The path of every value in `value`, itself and whatever it holds."""
    inner = value.items() if isinstance(value, dict) else enumerate(value) if isinstance(value, list) else []
    return [path, *(found for key, held in inner for found in nodes(held, (*path, key)))]


# A value of another type than each a leaf can have. A bool is never an int here, nor an int a bool.
OTHER_TYPES: dict[type, list[Any]] = {
    str: [7, None, ["x"]],
    int: ["0", False, None, 0.0],
    bool: [0, "false", None],
    type(None): [0, False, ["time_limit"]],
    list: [{}, "x", None],
    dict: [[], "x", None],
}
# The records whose keys are fixed, by where they are: a key added to one, or dropped, isn't its schema's.
FIXED = [(), ("build", 0), ("checks", 0), ("checks", 0, "commands", 0), ("runs", 0), ("runs", 1)]


class Shape(unittest.TestCase):
    def test_evidence_that_is_whole_and_right_is_a_variant(self) -> None:
        with mock.patch.object(variants, "verify_artifacts", return_value=True):
            answer, granted = variants.answer_of(planned(), evidence(), STEPS)
        self.assertEqual(
            (answer["status"], answer["reason"], answer["exit_code"]), ("variant", "built_and_checked", 0)
        )
        self.assertTrue(granted)
        self.assertNotIn("path", answer)

    def test_a_value_of_another_type_is_refused_wherever_it_is(self) -> None:
        tried = 0
        for path in nodes(evidence())[1:]:
            for other in OTHER_TYPES[type(at(evidence(), path))]:
                if other is None and path[-1] in (
                    "comparison",
                    "expected_sha256",
                    "result_sha256",
                    "expected_size",
                    "result_size",
                ):
                    # A file that isn't there has no hash, which is its schema's, and not a variant: below.
                    continue
                e = evidence()
                at(e, path[:-1])[path[-1]] = other
                self.assertEqual(said(e), ("error", "evidence_malformed"), (path, other))
                tried += 1
        self.assertGreater(tried, 100)

    def test_a_key_dropped_or_added_is_refused(self) -> None:
        for where in FIXED:
            for key in list(at(evidence(), where)):
                e = evidence()
                del at(e, where)[key]
                self.assertEqual(said(e), ("error", "evidence_malformed"), (where, key))
            e = evidence()
            at(e, where)["more"] = "x"
            self.assertEqual(said(e), ("error", "evidence_malformed"), where)
        for broken in ({"table": []}, {**planned(), "more": 1}, {**planned(), "table": "x"}, []):
            self.assertEqual(said(p=broken), ("error", "evidence_malformed"), broken)

    def test_a_hash_that_is_not_one_is_refused(self) -> None:
        for path in (("replaced", PIC), ("checks", 0, "result_sha256"), ("runs", 1, "stdout_sha256")):
            e = evidence()
            at(e, path[:-1])[path[-1]] = "A" * 64
            self.assertEqual(said(e), ("error", "evidence_malformed"), path)


def change(path: tuple[Any, ...], value: Any, e: dict[str, Any] | None = None) -> dict[str, Any]:
    e = copy.deepcopy(evidence() if e is None else e)
    at(e, path[:-1])[path[-1]] = value
    return e


RESULT, OUTPUT = ("checks", 0, "result_sha256"), ("runs", 1, "stdout_sha256")
# Evidence with one thing changed, and what it comes to.
CHANGED: list[tuple[str, dict[str, Any], tuple[str, str]]] = [
    (
        "a result that's another",
        change(("checks", 0, "comparison"), "different", change(RESULT, sha("f"))),
        ("wrong_answer", "answer_differs"),
    ),
    (
        "an expected file that's another",
        change(("checks", 0, "comparison"), "different", change(("checks", 0, "expected_sha256"), sha("f"))),
        ("wrong_answer", "answer_differs"),
    ),
    ("an output that's another", change(OUTPUT, sha("f")), ("wrong_answer", "answer_differs")),
    (
        "an output the manifest gives no hash for",
        change(("runs", 0, "stdout_sha256"), sha("f")),
        ("variant", "built_and_checked"),
    ),
    (
        "a check's command that failed",
        change(("checks", 0, "commands", 1, "exit"), 2),
        ("error", "checks_completed"),
    ),
    ("a run that failed", change(("runs", 0, "exit"), 1), ("error", "runs_completed")),
    (
        "a result that was there before",
        change(("checks", 0, "result_before"), True),
        ("error", "checks_completed"),
    ),
    ("no result", change(RESULT, None), ("error", "checks_completed")),
    ("no expected file", change(("checks", 0, "expected_sha256"), None), ("error", "checks_completed")),
    ("no build steps were recorded", change(("build",), []), ("error", "build_failed")),
    ("a check with no commands", change(("checks", 0, "commands"), []), ("error", "not_the_plan")),
    ("no check", change(("checks",), []), ("error", "not_the_plan")),
    ("a check twice", change(("checks",), evidence()["checks"] * 2), ("error", "not_the_plan")),
    ("a run missing", change(("runs",), evidence()["runs"][:1]), ("error", "not_the_plan")),
    ("a run twice", change(("runs",), evidence()["runs"] * 2), ("error", "not_the_plan")),
    # Review 1's findings 1 to 4: a run that failed isn't an answer, an empty file isn't one, and the
    # evidence has to be what was planned.
    *[
        (
            f"a run exiting {code} with no output",
            change(("runs", 1, "stdout_size"), 0, change(("runs", 1, "exit"), code)),
            ("error", "runs_completed"),
        )
        for code in (2, 7)
    ],
    ("a run exiting 0 with no output", change(("runs", 1, "stdout_size"), 0), ("error", "runs_completed")),
    ("an empty result", change(("checks", 0, "result_size"), 0), ("error", "checks_completed")),
    ("an empty expected file", change(("checks", 0, "expected_size"), 0), ("error", "checks_completed")),
    (
        "a check's command dropped",
        change(("checks", 0, "commands"), evidence()["checks"][0]["commands"][:1]),
        ("error", "not_the_plan"),
    ),
    (
        "a check's command another",
        change(("checks", 0, "commands", 1, "argv"), ["true"]),
        ("error", "not_the_plan"),
    ),
    ("a result elsewhere", change(("checks", 0, "result"), "/tmp/x.res"), ("error", "not_the_plan")),
    ("a run with no words", change(("runs", 0, "argv"), []), ("error", "not_the_plan")),
    ("a run with another environment", change(("runs", 0, "env"), {}), ("error", "not_the_plan")),
    (
        "a program outside the build",
        change(("runs", 1, "program"), "/usr/bin/env"),
        ("error", "not_the_plan"),
    ),
    (
        "a program beside the build",
        change(("runs", 1, "program"), f"{OUT}-other/x"),
        ("error", "not_the_plan"),
    ),
    ("evidence of another build", change(("out",), "/nix/store/p"), ("error", "not_the_plan")),
    (
        "a build step that failed",
        change(
            ("build",),
            [{"argv": BUILD[0], "exit": 0, "limit": None}, {"argv": BUILD[1], "exit": 2, "limit": None}],
        ),
        ("error", "build_failed"),
    ),
    (
        "a build step stopped",
        change(("build",), [{"argv": BUILD[0], "exit": -9, "limit": "time_limit"}]),
        ("unknown", "time_limit"),
    ),
    ("a build step not the plan's", change(("build", 1, "argv"), ["make", "-n"]), ("error", "not_the_plan")),
    ("a build that stopped short", change(("build",), evidence()["build"][:2]), ("error", "build_failed")),
    ("an object not replaced", change(("replaced",), {PIC: sha("1")}), ("error", "replaced_once")),
    (
        "an object replaced that isn't the table's",
        change(("replaced", "src/z.o"), sha("3")),
        ("error", "replaced_once"),
    ),
    (
        "a check's command stopped at a limit",
        change(("checks", 0, "commands", 0, "limit"), "time_limit"),
        ("unknown", "time_limit"),
    ),
    ("a run that was killed", change(("runs", 1, "exit"), -9), ("unknown", "killed")),
]


class Decided(unittest.TestCase):
    def test_one_thing_changed(self) -> None:
        for what, e, want in CHANGED:
            self.assertEqual(said(e), want, what)

    def test_a_unit_is_replaced_whole(self) -> None:
        half = {**planned(), "table": [OTHER], "replace": {OTHER: "/ir/other"}}
        self.assertEqual(said(change(("replaced",), {OTHER: sha("2")}), half), ("error", "units_whole"))
        unused = {**planned(), "table": ["src/no/such.o"], "replace": {"src/no/such.o": "/ir/no"}}
        self.assertEqual(said(change(("replaced",), {}), unused), ("error", "replaced_once"))
        none = {**planned(), "table": [], "replace": {}}
        self.assertEqual(said(change(("replaced",), {}), none), ("variant", "built_and_checked"))

    def test_a_wrong_answer_needs_the_build_whole_and_every_check_and_run_completed(self) -> None:
        wrong = change(("checks", 0, "comparison"), "different", change(RESULT, sha("f")))
        self.assertEqual(said(wrong), ("wrong_answer", "answer_differs"))
        for what, path, value, reason in (
            ("a result that was there before", ("checks", 0, "result_before"), True, "checks_completed"),
            ("a run missing", ("runs",), evidence()["runs"][:1], "not_the_plan"),
            ("a run that crashed", ("runs", 0, "exit"), 2, "runs_completed"),
            ("an empty result", ("checks", 0, "result_size"), 0, "checks_completed"),
            ("an object not replaced", ("replaced",), {PIC: sha("1")}, "replaced_once"),
        ):
            self.assertEqual(said(change(path, value, wrong)), ("error", reason), what)
        for e in (None, wrong):
            failed = {**STEPS, "realize": Step("realize", 1)}
            self.assertEqual(said(e, steps=failed), ("error", "realize"))
            limited = {**STEPS, "realize": Step("realize", -9, limit="time_limit")}
            self.assertEqual(said(e, steps=limited), ("unknown", "time_limit"))
            absent = {name: step for name, step in STEPS.items() if name != "evaluate"}
            self.assertEqual(said(e, steps=absent), ("error", "internal_error"))

    def test_deny_all_takes_both_grants_away(self) -> None:
        with mock.patch.dict(os.environ, {DENY_ALL: "1"}):
            self.assertEqual(said(), ("error", "denied"))
            self.assertEqual(
                said(change(("checks", 0, "comparison"), "different", change(RESULT, sha("f")))),
                ("error", "denied"),
            )
            self.assertEqual(said(change(("runs", 0, "exit"), 1)), ("error", "runs_completed"))

    def test_incomplete_controls_never_grant_a_negative(self) -> None:
        mismatch = change(OUTPUT, sha("f"))
        for idx in (0, 1):
            for code in (1, 2, 99, 124, 137, -9):
                status, _ = said(change(("checks", 0, "commands", idx, "exit"), code, mismatch))
                self.assertIn(status, {"unknown", "error"}, (idx, code))
        self.assertEqual(
            said(change(("checks", 0, "comparison"), None, mismatch)), ("error", "checks_completed")
        )
        self.assertEqual(
            said(change(("dispatch", "avx512f"), False, mismatch)), ("unknown", "missing_features")
        )
        self.assertEqual(
            said(change(("runs", 1, "limit"), "launch_failed", mismatch)), ("error", "launch_failed")
        )

    def test_a_key_given_twice_is_refused(self) -> None:
        with self.assertRaises(variants.Refused) as refused:
            variants.parsed('{"a": true, "a": false}', "the evidence", "evidence_malformed")
        self.assertEqual(refused.exception.reason, "evidence_malformed")

    def test_a_command_line_that_is_not_this_tools_is_never_a_grants_exit(self) -> None:
        for argv in ([], ["realize"], ["measure", "baseline"]):
            ran = proc.run(
                [sys.executable, HERE / "variants.py", *argv], timeout=60, env={**os.environ, DENY_ALL: "1"}
            )
            self.assertEqual((ran.exit, json.loads(ran.out)["reason"]), (1, "invalid_request"), argv)

    def test_no_cpuinfo_is_every_feature_missing(self) -> None:
        with mock.patch.object(Path, "read_text", side_effect=FileNotFoundError):
            self.assertEqual(variants.missing_features(), list(variants.FEATURES))

    def test_every_reason_has_a_status_and_an_exit_code(self) -> None:
        for reason, (status, _) in variants.REASONS.items():
            self.assertIn(status, variants.EXIT_CODES, reason)
        self.assertEqual({s for s, _ in variants.REASONS.values()}, set(variants.EXIT_CODES))


def run(*argv: str | Path, cwd: Path | None = None) -> proc.Ran:
    ran = proc.run([str(a) for a in argv], timeout=600, cwd=cwd)
    assert ran.ok, (argv, ran.output[-2000:])
    return ran


class StoredArtifacts(unittest.TestCase):
    def test_reader_binds_the_plan_to_bytes_and_native_completion(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            out = Path(scratch) / "build"
            logs = out / "logs"
            logs.mkdir(parents=True)
            plan, record = planned(), evidence()
            record["out"] = str(out)
            expected = Path(scratch) / "known.exp"
            result = out / "x.res"
            expected.write_bytes(b"a" * 310 + b"\nOK\n")
            result.write_bytes(expected.read_bytes())
            check = record["checks"][0]
            plan["workloads"][0]["checks"][0]["expected"] = check["expected"] = str(expected)
            check["result"] = str(result)
            marker = logs / "check-argon2id-0.comparison"
            marker.write_text("equal\n")
            for key in plan["table"]:
                ir = Path(scratch) / Path(key).parent.name
                ir.write_bytes(key.encode())
                plan["replace"][key] = str(ir)
                record["replaced"][key] = variants.hashing.sha256_file(ir)
            for launch in record["runs"]:
                program = out / Path(launch["program"]).name
                program.touch()
                launch.update(program=str(program), argv=[str(program)])
                launch["env"] = {k: v.replace(OUT, str(out)) for k, v in launch["env"].items()}
                stdout = logs / f"run-{launch['workload']}.stdout"
                stdout.write_bytes(b"ok\n")
                launch.update(stdout_size=3, stdout_sha256=variants.hashing.sha256_file(stdout))
            plan["workloads"][1]["outputs"] = [record["runs"][1]["stdout_sha256"]]

            def observe() -> None:
                for field, path in (("expected", expected), ("result", result)):
                    check[field + "_size"] = path.stat().st_size
                    check[field + "_sha256"] = variants.hashing.sha256_file(path)

            def answer() -> str:
                return variants.answer_of(plan, record, STEPS)[0]["status"]

            observe()
            self.assertEqual(answer(), "variant")
            for path, forged in (
                (("checks", 0, "expected_sha256"), sha("c")),
                (("checks", 0, "result_size"), 1),
                (("replaced", PIC), sha("d")),
                (("runs", 0, "program"), str(out) + "/../outside"),
                (("runs", 1, "stdout_sha256"), sha("f")),
            ):
                bad = change(path, forged, record)
                with self.assertRaises(variants.Refused, msg=str(path)):
                    variants.answer_of(plan, bad, STEPS)
            result.write_bytes(b"f" * 310 + b"\nadditional diagnostic\nOK\n")
            check["comparison"] = "different"
            marker.write_text("different\n")
            observe()
            self.assertEqual(answer(), "wrong_answer")
            result.write_bytes(b"[tv] pwhash failure (maybe intentional): [0]\nOK\n")
            observe()
            self.assertEqual(answer(), "error")
            marker.unlink()
            check["comparison"] = None
            result.write_bytes(b"12345")
            observe()
            # Even alongside an independently wrong workload, preparation failure/partial output cannot grant.
            plan["workloads"][1]["outputs"] = [sha("e")]
            check["commands"][0]["exit"] = 2
            self.assertEqual(answer(), "error")


class Snapshot(unittest.TestCase):
    def test_a_commit_archives_to_its_own_bytes_and_a_dirty_checkout_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            repo = Path(scratch).resolve()
            (repo / "flake.nix").write_text("{\n  outputs = _: { };\n}\n")
            (repo / "file").write_text("first\n")
            git = ("git", "-C", repo, "-c", "user.name=t", "-c", "user.email=t@example.invalid")
            run(*git, "init", "-q")
            run(*git, "add", "flake.nix", "file")
            run(*git, "commit", "-q", "-m", "first")
            first = variants.commit_of(repo)
            self.assertRegex(first, variants.COMMIT)
            (repo / "file").write_text("second\n")
            with self.assertRaises(variants.Refused) as refused:
                variants.commit_of(repo)
            self.assertEqual(refused.exception.reason, "checkout_dirty")
            # The first commit's bytes, while the checkout holds the second's, and once that's committed.
            for committed in (False, True):
                if committed:
                    run(*git, "commit", "-q", "-am", "second")
                ran, path = variants.archive(repo, first)
                self.assertTrue(ran.ok and path is not None, ran.err[-500:])
                assert path is not None
                self.assertEqual((path / "file").read_text(), "first\n")
                self.assertRegex(variants.nar_hash(path), r"^sha256-")
            self.assertNotEqual(variants.commit_of(repo), first)
            ran, path = variants.archive(repo, "0" * 40)
            self.assertFalse(ran.ok)
            self.assertIsNone(path)

            # A copy of the command in the checkout can be absent from both archived commits.
            scripts = repo / "bench" / "kernels"
            scripts.mkdir(parents=True)
            script = scripts / "variants.py"
            script.write_bytes((HERE / "variants.py").read_bytes())
            (scripts / "kernels.py").symlink_to(HERE / "kernels.py")
            (repo / "tools").symlink_to(ROOT / "tools")
            ran = proc.run([sys.executable, script, "realize", "baseline"], timeout=60)
            self.assertEqual((ran.exit, json.loads(ran.out)["reason"]), (1, "snapshot_failed"))


def evaluates(manifest: str) -> proc.Ran:
    """Evaluates bench/kernels/variants.nix's plan for the baseline, of a repository with this manifest."""
    with tempfile.TemporaryDirectory() as scratch:
        (Path(scratch) / "bench" / "kernels").mkdir(parents=True)
        (Path(scratch) / "bench" / "kernels" / "manifest.toml").write_text(manifest)
        lock = json.dumps(json.loads((ROOT / "flake.lock").read_text())["nodes"]["nixpkgs"]["locked"])
        pkgs = (
            "import (builtins.fetchTree (builtins.fromJSON ''" + lock + "'')) { system = \"x86_64-linux\"; }"
        )
        expression = (
            f"(import {HERE}/variants.nix {{ repo = {scratch}; pkgs = {pkgs}; }}).libsodium.baseline.planned"
        )
        return proc.run(["nix", "eval", "--impure", "--json", "--expr", expression], timeout=600)


class Manifest(unittest.TestCase):
    def test_what_a_build_cannot_follow_does_not_evaluate(self) -> None:
        text = (HERE / "manifest.toml").read_text()
        ran = evaluates(text)
        self.assertTrue(ran.ok, ran.err[-800:])
        self.assertEqual([w["name"] for w in json.loads(ran.out)["workloads"]], ["argon2id", "secretstream"])
        run_line = 'run = [["{build}/secretstream"]]\n'
        answers = 'test = ["test/default/pwhash_argon2id.c", "test/default/pwhash_argon2id.exp"]\n'
        start = text.index(answers) + len(answers)
        self.assertEqual((text.count(run_line), text.count(answers)), (1, 1))
        self.assertTrue(text[start:].startswith("run = [\n"))
        output_check = '[[project.libsodium.workload.check]]\nkind = "output"'
        self.assertEqual(text.count(output_check), 1)
        for what, broken, says in (
            (
                "a workload with setup",
                text.replace(run_line, 'setup = [["false"]]\n' + run_line),
                "needs setup commands",
            ),
            (
                "a separate output check",
                text.replace(output_check, output_check + '\nrun = [["false"]]'),
                "runs a separate output check",
            ),
            (
                "two commands",
                text.replace(run_line, 'run = [["{build}/secretstream"], ["{build}/secretstream"]]\n'),
                "isn't one command",
            ),
            (
                "a program outside the build",
                text.replace(run_line, 'run = [["/bin/sh"]]\n'),
                "doesn't run a program under {build}",
            ),
            (
                "a placeholder a build doesn't fill in",
                text.replace(run_line, 'run = [["{build}/secretstream", "{input:x}"]]\n'),
                "placeholder",
            ),
            ("a check with no run", text[:start] + text[text.index("\n]\n", start) + 3 :], "has no `run`"),
        ):
            ran = evaluates(broken)
            self.assertFalse(ran.ok, what)
            self.assertIn(says, ran.err, what)


class Section(unittest.TestCase):
    # The object is compiled for this host, and the sections it reads are an ELF object's.
    @unittest.skipUnless(sys.platform == "linux", "the object's sections are ELF's")
    def test_a_section_that_is_missing_or_empty_is_an_error(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            work = Path(scratch)
            (work / "f.c").write_text('const char s[] = "abc";\n')
            (work / "none.c").write_text("int x;\n")
            run("clang", "-c", "f.c", "-o", "f.o", cwd=work)
            run("clang", "-c", "none.c", "-o", "none.o", cwd=work)
            run("llvm-objcopy", "--remove-section=.rodata", "f.o", "removed.o", cwd=work)
            self.assertEqual(variants.section(work / "f.o", ".rodata"), b"abc\0")
            # A section that isn't there, and one that's there and holds nothing.
            for obj, name in (("removed.o", ".rodata"), ("none.o", ".text")):
                with self.assertRaises(RuntimeError, msg=obj):
                    variants.section(work / obj, name)
            self.assertEqual(variants.objects(work).keys(), {"f.o", "none.o", "removed.o"})


if __name__ == "__main__":
    # Set where this runs, it would take every grant away the tests expect.
    os.environ.pop(DENY_ALL, None)
    unittest.main()
