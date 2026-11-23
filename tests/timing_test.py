#!/usr/bin/env python3
"""Checks bench/kernels/timing.py, the harness that times a candidate by the corpus's protocol, and the rule
it reads sessions by, bench/kernels/protocol.py. docs/kernels.md, "The harness".

It builds a tiny project of its own: a library whose one function spins a set number of times and then
returns a fixed answer, and a program that calls it. Builds differ in how long the library spins, in its
answer, or in whose library the program loads, so every session here is seconds long, and each fault is
planted:

- a run that exits non-zero, in the warm-up or in the second pair, fails its session, which records no pair;
- a candidate that loads the baseline's library is refused unless the session is a control;
- a wrong answer fails each kind of check before or while anything is timed, in a later pair too;
- a library that changes while the session runs fails it;
- sessions are pooled by the rule, and only confirmation sessions of one seed each count.

It lowers the rule's minimums alone, so no session here is by the protocol, and none is shown faster. What
sessions come to is read on records it makes, by the protocol, through irlean.verdict.

usage: tests/timing_test.py
"""

import json
import os
import random
import shutil
import statistics
import sys
import tempfile
import typing
import unittest
from pathlib import Path
from typing import Any, ClassVar
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(ROOT / "bench" / "kernels"))
import kernels  # noqa: E402
import protocol  # noqa: E402
import timing  # noqa: E402
from irlean import hashing, proc, schemas, verdict  # noqa: E402

LIBRARY = """
unsigned long work(unsigned long x) {
  for (volatile unsigned long i = 0; i < LOOPS; i++) {}
  return 3 * x + 1 + WRONG;
}
"""
PROGRAM = """
#include <stdio.h>
#include <string.h>
unsigned long work(unsigned long);
/* Which call this is, counted in a file. */
static int call(const char *path) {
  int n = 0;
  FILE *f = fopen(path, "r");
  if (f) { fscanf(f, "%d", &n); fclose(f); }
  f = fopen(path, "w");
  fprintf(f, "%d", n + 1);
  fclose(f);
  return n + 1;
}
int main(int argc, char **argv) {
  unsigned long r = work(7);
  const char *mode = argc > 1 ? argv[1] : "";
  if (!strcmp(mode, "--check")) return r == 22 ? 0 : 1;
  if (!strcmp(mode, "--fail")) return 3;
  /* The third call fails, or prints another answer. */
  if (!strcmp(mode, "--flaky") && call(argv[2]) == 3) return 4;
  if (!strcmp(mode, "--drift") && call(argv[2]) == 3) r += 1;
  /* Writes its file on its first call, and not again. */
  if (!strcmp(mode, "--once") && call(argv[3]) != 1) return 0;
  if (!strcmp(mode, "--once")) mode = "--write";
  if (!strcmp(mode, "--reads")) {
    /* Fails unless it can open its input. */
    FILE *f = fopen(argv[2], "r");
    if (!f) return 5;
    fclose(f);
  }
  if (!strcmp(mode, "--write")) {
    FILE *f = fopen(argv[2], "w");
    fprintf(f, "%lu\\n", r);
    fclose(f);
  }
  if (!strcmp(mode, "--append")) {
    FILE *f = fopen(argv[2], "a");
    fputc(0, f);
    fclose(f);
  }
  printf("%lu\\n", r);
  return 0;
}
"""
KNOWN = '[[project.NAME.workload.check]]\nkind = "known-answers"\nrun = [["{build}/bench", "--check"]]\n'
WORK = '[[project.NAME.workload]]\nname = "work"\nrun = [["{build}/bench"]]\nmeasure = "time"\n' + KNOWN
PRINT = (
    '[[project.NAME.workload]]\nname = "print"\nrun = [["env", "TINY=1", "{build}/bench"]]\n'
    'measure = "time"\n'
    '[[project.NAME.workload.check]]\nkind = "output"\noutput = ["stdout"]\n'
)
MANIFEST = (
    "[corpus]\n"
    # A project with an input, pinned by its hash: the SHA-256 of "data\n".
    + '[[project.fed.input]]\nname = "data"\n'
    + 'sha256 = "6667b2d1aab6a00caa5aee5af8ad9f1465e567abf1c209d15727d57b3e8f6e5f"\n'
    + '[[project.fed.workload]]\nname = "work"\nrun = [["{build}/bench", "--reads", "{input:data}"]]\n'
    + 'measure = "time"\n'
    + KNOWN.replace("NAME", "fed")
    # One that changes its input.
    + '[[project.fed.workload]]\nname = "eats"\nrun = [["{build}/bench", "--append", "{input:data}"]]\n'
    + 'measure = "time"\n'
    + KNOWN.replace("NAME", "fed")
    + WORK.replace("NAME", "solo")
    + (WORK + PRINT).replace("NAME", "two")
    + (WORK + PRINT).replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "file"
run = [["{build}/bench", "--write", "{out}/answer"]]
measure = "time"
[[project.tiny.workload.check]]
kind = "output"
output = ["{out}/answer"]

[[project.tiny.workload]]
name = "own-check"
run = [["{build}/bench"]]
measure = "time"
[[project.tiny.workload.check]]
kind = "output"
run = [["{build}/bench", "--write", "{out}/checked"]]
output = ["{out}/checked"]

[[project.tiny.workload]]
name = "fails"
run = [["{build}/bench", "--fail"]]
measure = "time"
"""
    + KNOWN.replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "flaky"
run = [["{build}/bench", "--flaky", "{out}/calls"]]
measure = "time"
"""
    + KNOWN.replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "drifts"
run = [["{build}/bench", "--drift", "{out}/calls"]]
measure = "time"
[[project.tiny.workload.check]]
kind = "output"
output = ["stdout"]

[[project.tiny.workload]]
name = "once"
run = [["{build}/bench", "--once", "{out}/answer", "{out}/calls"]]
measure = "time"
[[project.tiny.workload.check]]
kind = "output"
output = ["{out}/answer"]

[[project.tiny.workload]]
name = "clean"
run = [["{build}/bench"]]
measure = "time"
[[project.tiny.workload.check]]
kind = "known-answers"
run = [["sh", "-c", 'test -z "$MAKEFLAGS$LD_PRELOAD" && exec "$0" --check', "{build}/bench"]]

[[project.tiny.workload]]
name = "mutates"
run = [["{build}/bench", "--append", "{build}/libwork.so"]]
measure = "time"
"""
    + KNOWN.replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "rate"
run = [["{build}/bench"]]
measure = "rate"
rate = "A figure nothing reads"
"""
    + KNOWN.replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "unchecked"
run = [["{build}/bench"]]
measure = "time"

[[project.tiny.workload]]
name = "elsewhere"
run = [["true"]]
measure = "time"
"""
    + KNOWN.replace("NAME", "tiny")
    + """
[[project.tiny.workload]]
name = "option"
run = [["env", "-i", "{build}/bench"]]
measure = "time"
"""
    + KNOWN.replace("NAME", "tiny")
)
# The protocol's rule with its minimums lowered, so a session is seconds long. Nothing else differs.
RULE = protocol.Rule(min_pairs=6, min_sessions=2, min_seconds=0.03, resamples=2000)
# How long a run of each build's program is said to take. The programs really run, and the harness is told
# these, so that nothing here depends on how fast the machine is: a run of `base` is four of any other's.
SECONDS = {"base": 0.02, "half": 0.01}
QUICK = 0.005


def told(real: Any) -> Any:
    """`proc.run`, with each timed run's time as SECONDS has it."""

    def run(argv: Any, **kw: Any) -> proc.Ran:
        r = real(argv, **kw)
        if argv[0] == "taskset":
            r.seconds = SECONDS.get(Path(argv[3]).parent.name, QUICK)
        return r

    return run


def sh(*argv: Any) -> None:
    r = proc.run(argv, timeout=300)
    if not r.ok:
        raise RuntimeError(f"{' '.join(map(str, argv))}\n{r.output}")


@unittest.skipUnless(sys.platform.startswith("linux"), "the harness pins with taskset and reads ldd")
class Timing(unittest.TestCase):
    root: ClassVar[Path]
    manifest: ClassVar[dict[str, Any]]
    cpu: ClassVar[str]
    seeds: ClassVar[Any]

    @classmethod
    def setUpClass(cls) -> None:
        cls.root = Path(tempfile.mkdtemp(prefix="timing-test-"))
        cls.addClassCleanup(shutil.rmtree, cls.root, True)
        (cls.root / "work.c").write_text(LIBRARY)
        (cls.root / "bench.c").write_text(PROGRAM)
        (cls.root / "manifest.toml").write_text(MANIFEST)
        cls.manifest = kernels.load(cls.root / "manifest.toml")
        cls.cpu = str(min(os.sched_getaffinity(0)))
        cls.seeds = iter(range(1000, 100000))
        # A base, a candidate that spins a quarter as long, and one whose answer is wrong.
        cls.build("base", loops=40_000_000)
        cls.build("fast", loops=10_000_000)
        cls.build("half", loops=20_000_000)
        cls.build("wrong", loops=10_000_000, wrong=1)
        # A candidate whose program loads the base's library, as a link that kept the old path would.
        cls.build("stolen", loops=10_000_000, loads="base")
        # One whose program is told where its library is by LD_LIBRARY_PATH, and by nothing in itself.
        cls.build("loose", loops=10_000_000, loads="")
        clock = mock.patch.object(proc, "run", told(proc.run))
        clock.start()
        cls.addClassCleanup(clock.stop)

    @classmethod
    def build(cls, name: str, loops: int, wrong: int = 0, loads: str | None = None) -> None:
        b = cls.root / name
        b.mkdir()
        macros = (f"-DLOOPS={loops}UL", f"-DWRONG={wrong}")
        sh("clang", "-O1", "-shared", "-fPIC", *macros, cls.root / "work.c", "-o", b / "libwork.so")
        rpath = [] if loads == "" else [f"-Wl,-rpath,{cls.root / (loads or name)}"]
        sh("clang", "-O1", cls.root / "bench.c", f"-L{b}", "-lwork", *rpath, "-o", b / "bench")

    def plan(self, project: str, workload: str, candidate: str, **options: Any) -> timing.Session:
        work = Path(tempfile.mkdtemp(prefix="session-", dir=self.root))
        options.setdefault("seed", next(self.seeds))
        options.setdefault("sessions", self.root / "sessions" / self.id())
        return timing.Session(
            self.manifest,
            self.root / "manifest.toml",
            project,
            workload,
            {
                "baseline": timing.Variant(self.root / "base"),
                "candidate": timing.Variant(self.root / candidate, options.pop("env", {})),
            },
            options.pop("cpus", self.cpu),
            pairs=options.pop("pairs", 3),
            kind=options.pop("kind", protocol.CONFIRMATION),
            control=options.pop("control", False),
            work=work,
            rule=options.pop("rule", RULE),
            **options,
        )

    def session(self, *args: Any, **options: Any) -> tuple[Path, dict[str, Any]]:
        return timing.session(self.plan(*args, **options))

    def failed(self, *args: Any, **options: Any) -> dict[str, Any]:
        """A session that fails: its record, which has to say so and hold no pair."""
        path, record = self.session(*args, **options)
        self.assertEqual(record["status"], timing.FAILED, record)
        self.assertEqual(record["pairs"], [])
        self.assertEqual(schemas.read(path, schemas.KERNELS_SESSION), record)
        return record

    # A session, and what it records.

    def test_a_session_records_what_it_ran_and_is_read_by_the_rule(self) -> None:
        paths = [self.session("solo", "work", "fast")[0] for _ in range(2)]
        self.assertEqual(paths[0].parent, paths[1].parent)
        self.assertEqual([p.name for p in paths], ["001.json", "002.json"])
        record = schemas.read(paths[0], schemas.KERNELS_SESSION)
        self.assertEqual(record["status"], timing.COMPLETE)
        self.assertEqual(len(record["pairs"]), 3)
        # Each pair's order is the seed's.
        rng = random.Random(record["seed"])
        self.assertEqual(
            [p["order"] for p in record["pairs"]], [rng.sample(timing.VARIANTS, 2) for _ in range(3)]
        )
        # A run shorter than the rule's minimum is repeated until it's a fifth over it: 0.005 s, 8 times.
        self.assertEqual(record["repeat"], 8)
        for p in record["pairs"]:
            self.assertAlmostEqual(p["candidate"]["seconds"], 0.04)
            self.assertAlmostEqual(p["baseline"]["seconds"], 0.16)
            self.assertAlmostEqual(p["ratios"]["seconds"], 4.0)
            for v in timing.VARIANTS:
                self.assertEqual((p[v]["exit"], p[v]["limit"]), (0, None))
                self.assertGreaterEqual(p[v]["user_s"], 0)
                self.assertIn("load1", p[v])
        self.assertEqual(record["checks"], [{"check": 1, "kind": "known-answers", "candidate": "passed"}])
        # Each variant loads its own library, which is what tells them apart.
        ids = {v: record["variants"][v]["identity"] for v in timing.VARIANTS}
        self.assertNotEqual(ids["baseline"]["id"], ids["candidate"]["id"])
        for v, name in (("baseline", "base"), ("candidate", "fast")):
            loads = {f["name"]: f["path"] for f in ids[v]["loads"]}
            self.assertEqual(loads["libwork.so"], str(self.root / name / "libwork.so"))
            self.assertEqual(loads["program"], str(self.root / name / "bench"))
        reading = timing.read(paths[0].parent, [])
        schemas.check(reading, schemas.KERNELS_READING)
        self.assertEqual([s["session"] for s in reading["sessions"]], ["001.json", "002.json"])
        self.assertAlmostEqual(reading["result"]["figures"]["seconds"]["pooled"]["median"], 4.0)
        # Every condition of the rule holds: a quarter of the time is well over half a percent faster.
        held = {name: c["held"] for name, c in reading["result"]["conditions"].items()}
        self.assertEqual(
            {n for n, h in held.items() if h},
            {"confirmation", "pairs", "interval_above"} | {"sessions_above", "others"},
        )
        # And it still isn't shown faster: the rule's minimums were lowered and the manifest isn't the
        # corpus's, so the comparison isn't by the protocol.
        self.assertEqual((reading["status"], reading["exit_code"]), ("inconclusive", 3))
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "corpus")

    def test_only_confirmation_sessions_of_enough_pairs_count(self) -> None:
        path, _ = self.session("solo", "work", "fast", kind=protocol.EXPLORATORY)
        reading = timing.read(path.parent, [])
        self.assertEqual(
            (reading["status"], reading["why"]), ("inconclusive", "no complete confirmation session")
        )
        self.assertEqual(
            reading["left_out"],
            [{"session": "001.json", "why": "exploratory: only confirmation sessions count"}],
        )
        # One confirmation session of three pairs: too few pairs, in too few sessions.
        self.session("solo", "work", "fast")
        reading = timing.read(path.parent, [])
        self.assertEqual(reading["status"], "inconclusive")
        self.assertFalse(reading["result"]["conditions"]["pairs"]["held"])
        self.assertEqual(reading["sessions"], [{"session": "002.json", "status": timing.COMPLETE}])

    def test_a_seed_is_used_once(self) -> None:
        _, record = self.session("solo", "work", "fast", seed=77)
        self.assertEqual(record["status"], timing.COMPLETE)
        with self.assertRaisesRegex(timing.Refused, "seed 77 was used"):
            self.session("solo", "work", "fast", seed=77)

    def test_a_run_under_the_minimum_fails_the_session(self) -> None:
        # The warm-ups are long enough that a run isn't repeated, and every run after is shorter.
        calls: list[int] = []
        real = proc.run

        def quicker(argv: Any, **kw: Any) -> proc.Ran:
            r = real(argv, **kw)
            if argv[0] == "taskset":
                calls.append(1)
                r.seconds = 0.05 if len(calls) <= 2 else 0.02
            return r

        plan = self.plan("solo", "work", "fast")
        with mock.patch.object(proc, "run", quicker):
            record = plan.run()
        self.assertEqual((record["status"], record["pairs"], record["repeat"]), (timing.FAILED, [], 1))
        self.assertIn("took 0.020 s, under the rule's 0.03 s", record["failure"])

    def test_cpus_are_of_one_cache(self) -> None:
        two = {"0": {"l3": "0-7"}, "8": {"l3": "8-15"}}
        with (
            mock.patch.object(timing, "topology", return_value=two),
            self.assertRaisesRegex(timing.Refused, "share no one last-level cache"),
        ):
            self.plan("solo", "work", "fast")

    # Failures.

    def test_a_run_that_fails_fails_the_session(self) -> None:
        record = self.failed("tiny", "fails", "fast")
        self.assertIn("exit code 3", record["failure"])
        self.assertNotIn("warm_up", record)
        # The third call of each variant fails. With no repeating, that's its second pair: the first pair
        # isn't kept.
        record = self.failed("tiny", "flaky", "fast", rule=protocol.Rule(min_seconds=0.0))
        self.assertIn("exit code 4", record["failure"])
        self.assertEqual(record["repeat"], 1)
        where = self.root / "sessions" / self.id() / "tiny" / "flaky"
        with self.assertRaisesRegex(timing.Refused, "no complete session"):
            timing.read(next(where.iterdir()), [])

    def test_a_time_limit_fails_the_session(self) -> None:
        plan = self.plan("solo", "work", "fast")
        original = proc.run

        def limited(argv: Any, **kw: Any) -> proc.Ran:
            r = original(argv, **kw)
            if argv[0] == "taskset":
                r.limit = "time_limit"
            return r

        with mock.patch.object(proc, "run", limited):
            record = plan.run()
        self.assertEqual((record["status"], record["pairs"]), (timing.FAILED, []))
        self.assertIn("at its time_limit", record["failure"])

    def test_a_program_that_cant_start_fails_the_session(self) -> None:
        plan = self.plan("solo", "work", "fast")
        original = proc.run

        def missing(argv: Any, **kw: Any) -> proc.Ran:
            if argv[0] == "taskset":
                raise FileNotFoundError("taskset")
            return original(argv, **kw)

        with mock.patch.object(proc, "run", missing):
            path, record = timing.session(plan)
        self.assertEqual((record["status"], record["pairs"]), (timing.FAILED, []))
        self.assertIn("the session stopped on FileNotFoundError", record["failure"])
        self.assertEqual(schemas.read(path, schemas.KERNELS_SESSION)["status"], timing.FAILED)

    def test_a_library_that_changes_fails_the_session(self) -> None:
        # Each run adds a byte to its build's library, which its program loads.
        record = self.failed("tiny", "mutates", "half")
        self.assertRegex(
            record["failure"], "what the (baseline|candidate) loads changed while the session ran"
        )

    def test_a_session_that_fails_early_is_beside_the_others(self) -> None:
        # It fails before anything says what it loads, and is still a session of this comparison: the one
        # that then completes is in the same directory, where the failed one's plan counts.
        self.build("orphan", loops=10_000_000)
        library = self.root / "orphan" / "libwork.so"
        kept = library.read_bytes()
        library.unlink()
        first, record = self.session("solo", "work", "orphan", seed=5)
        # ldd says "not found" on a line this reads as neither a library nor nothing, so it's an error.
        self.assertEqual(record["status"], timing.FAILED)
        self.assertIn("printed a line this doesn't read", record["failure"])
        self.assertIn("not found", record["failure"])
        library.write_bytes(kept)
        with self.assertRaisesRegex(timing.Refused, "seed 5 was used"):
            self.session("solo", "work", "orphan", seed=5)
        second, record = self.session("solo", "work", "orphan")
        self.assertEqual((record["status"], second.parent), (timing.COMPLETE, first.parent))
        reading = timing.read(second.parent, [])
        self.assertEqual(
            reading["sessions"],
            [
                {"session": "001.json", "status": timing.FAILED},
                {"session": "002.json", "status": timing.COMPLETE},
            ],
        )
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "incomplete")

    # What a candidate loads.

    def test_a_candidate_that_loads_the_baselines_code_is_refused(self) -> None:
        record = self.failed("solo", "work", "stolen")
        self.assertIn("libwork.so, which is in the baseline's build", record["failure"])
        self.assertNotIn("warm_up", record)

    def test_what_a_variant_loads_is_found_from_where_it_runs(self) -> None:
        # Its library is wherever LD_LIBRARY_PATH says, and that's `.`: the build, where a timed command
        # runs. From here, `.` holds no library at all.
        here = Path.cwd()
        self.addCleanup(os.chdir, here)
        os.chdir(self.root)
        _, record = self.session("solo", "work", "loose", env={"LD_LIBRARY_PATH": "."})
        os.chdir(here)
        self.assertEqual(record["status"], timing.COMPLETE, record.get("failure"))
        loads = {f["name"]: f["path"] for f in record["variants"]["candidate"]["identity"]["loads"]}
        self.assertEqual(Path(loads["libwork.so"]).resolve(), self.root / "loose" / "libwork.so")

    def test_a_control_is_declared_and_loads_the_same(self) -> None:
        elsewhere = self.root / "sessions" / "undeclared"
        record = self.failed("solo", "work", "base", sessions=elsewhere)
        self.assertIn("this isn't a control", record["failure"])
        record = self.failed("solo", "work", "fast", control=True, sessions=elsewhere)
        self.assertIn("these differ", record["failure"])
        for _ in range(2):
            path, record = self.session("solo", "work", "base", control=True)
            self.assertEqual(record["status"], timing.COMPLETE)
        reading = timing.read(path.parent, [])
        # A control says whether its interval contains 1, and nothing about faster or slower.
        self.assertEqual((reading["status"], reading["exit_code"]), ("control", 4))
        self.assertNotIn("decisions", reading)
        self.assertEqual(reading["pooled"]["seconds"]["interval"], [1.0, 1.0])
        self.assertIs(reading["control_contains_one"], True)
        # With a confirmation session of it that failed, it isn't whole, and doesn't say it contains 1.
        failed = {
            **record,
            "seed": 3,
            "status": timing.FAILED,
            "pairs": [],
            "failure": "a run didn't end well",
        }
        (path.parent / "003.json").write_text(json.dumps(failed))
        reading = timing.read(path.parent, [])
        self.assertIs(reading["control_contains_one"], False)
        self.assertEqual(reading["why"], "a confirmation session of it failed")

    # Checks.

    def test_a_wrong_answer_fails_each_kind_of_check(self) -> None:
        record = self.failed("tiny", "work", "wrong")
        self.assertIn("the project's test", record["failure"])
        self.assertNotIn("warm_up", record)
        record = self.failed("tiny", "own-check", "wrong")
        self.assertIn("the candidate's output isn't the baseline's", record["failure"])
        self.assertNotIn("warm_up", record)
        for workload in ("print", "file"):
            record = self.failed("tiny", workload, "wrong")
            self.assertIn("didn't write what the baseline's did", record["failure"])
        # An answer that's right in the warm-up and wrong on a later call is caught where it goes wrong: in a
        # repetition of a run, or, where a run is one call, in the second pair.
        record = self.failed("tiny", "drifts", "fast")
        self.assertIn("two repetitions of one run", record["failure"])
        _, record = self.session("tiny", "drifts", "fast", rule=protocol.Rule(min_seconds=0.0))
        self.assertEqual((record["status"], record["pairs"], record["repeat"]), (timing.FAILED, [], 1))
        self.assertRegex(
            record["failure"], "pair 2: the (baseline|candidate) didn't write what the baseline's warm-up"
        )
        # And the right answer passes them, with what each run wrote hashed.
        for workload in ("print", "file", "own-check"):
            _, record = self.session("tiny", workload, "fast", pairs=1)
            self.assertEqual(record["status"], timing.COMPLETE, record.get("failure"))
        self.assertEqual(record["checks"][0]["baseline"], record["checks"][0]["candidate"])

    def test_a_file_an_earlier_run_wrote_isnt_this_runs(self) -> None:
        # Its warm-up writes the file its check hashes, and no later call does.
        record = self.failed("tiny", "once", "fast")
        self.assertIn("didn't write {out}/answer", record["failure"])
        self.assertIn("warm_up", record)

    def test_a_check_gets_none_of_the_callers_environment(self) -> None:
        # Its check passes only where MAKEFLAGS and LD_PRELOAD are unset, as a `make check` is a dry run
        # under MAKEFLAGS=n.
        with mock.patch.dict(os.environ, {"MAKEFLAGS": "n", "LD_PRELOAD": "", "SOURCE_DATE_EPOCH": "1"}):
            plan = self.plan("tiny", "clean", "fast", pairs=1)
            env = plan.env("candidate")
            _, record = timing.session(plan)
        self.assertEqual(record["status"], timing.COMPLETE, record.get("failure"))
        self.assertEqual({"MAKEFLAGS", "LD_PRELOAD", "SOURCE_DATE_EPOCH"} & set(env), set())
        self.assertIn("PATH", env)

    # What it won't run.

    def test_what_it_refuses(self) -> None:
        for workload, why in (
            ("nothing", "no workload"),
            ("rate", "nothing here reads"),
            ("unchecked", "has no check"),
        ):
            with self.assertRaisesRegex(timing.Refused, why):
                self.plan("tiny", workload, "fast")
        for workload, why in (
            ("elsewhere", "isn't in the baseline's build"),
            ("option", "a command through env"),
        ):
            with self.assertRaisesRegex(timing.Refused, why):
                self.session("tiny", workload, "fast")
        with self.assertRaisesRegex(timing.Refused, "can't run on cpus"):
            self.plan("solo", "work", "fast", cpus="99999")
        with self.assertRaisesRegex(timing.Refused, "isn't a list"):
            self.plan("solo", "work", "fast", cpus="1;rm")
        with self.assertRaisesRegex(timing.Refused, "isn't a directory"):
            self.plan("solo", "work", "missing")
        with self.assertRaisesRegex(timing.Refused, "both set"):
            self.session("tiny", "print", "fast", env={"TINY": "2"})

    def test_an_input_is_the_file_the_manifest_pins(self) -> None:
        inputs = self.root / "inputs"
        inputs.mkdir()
        with self.assertRaisesRegex(timing.Refused, "needs --inputs"):
            self.session("fed", "work", "fast", pairs=1)
        (inputs / "data").write_text("data\n")
        _, record = self.session("fed", "work", "fast", pairs=1, inputs=inputs)
        self.assertEqual(record["status"], timing.COMPLETE, record.get("failure"))
        self.assertEqual(record["inputs"], {"data": hashing.sha256_text("data\n")})
        # A directory given relative to where this runs is still found from the build a command runs in.
        here = Path.cwd()
        self.addCleanup(os.chdir, here)
        os.chdir(self.root)
        _, record = self.session("fed", "work", "fast", pairs=1, inputs=Path("inputs"))
        os.chdir(here)
        self.assertEqual(record["status"], timing.COMPLETE, record.get("failure"))
        # A run that changes it fails its session, though it was right when first named.
        record = self.failed("fed", "eats", "fast", pairs=1, inputs=inputs)
        self.assertIn("the input data changed while the session ran", record["failure"])
        with self.assertRaisesRegex(timing.Refused, "isn't the data the manifest pins"):
            self.session("fed", "work", "fast", pairs=1, inputs=inputs)
        # And a directory of that name has no hash to be held to.
        (inputs / "data").unlink()
        (inputs / "data").mkdir()
        with self.assertRaisesRegex(timing.Refused, "a directory holding the file data"):
            self.session("fed", "work", "fast", pairs=1, inputs=inputs)

    # Pooling.

    def test_the_other_workloads_have_to_be_measured_and_not_slower(self) -> None:
        for _ in range(2):
            work, _ = self.session("two", "work", "fast")
            printed, _ = self.session("two", "print", "fast")
        others = timing.read(work.parent, [])["result"]["conditions"]["others"]
        self.assertFalse(others["held"])
        self.assertIn("print wasn't measured", others["says"])
        others = timing.read(work.parent, [printed.parent])["result"]["conditions"]["others"]
        self.assertTrue(others["held"], others)
        # Sessions of this workload aren't the project's other workload, and nor are two directories of it.
        with self.assertRaisesRegex(timing.Refused, "no confirmation session of another workload"):
            timing.read(work.parent, [work.parent])
        with self.assertRaisesRegex(timing.Refused, "a second directory of print's sessions"):
            timing.read(work.parent, [printed.parent, printed.parent])
        # Nor are sessions of the other workload between other builds.
        half, record = self.session("two", "print", "half")
        self.assertEqual(record["status"], timing.COMPLETE)
        self.assertNotEqual(half.parent, printed.parent)
        with self.assertRaisesRegex(timing.Refused, "isn't sessions of the same two builds"):
            timing.read(work.parent, [half.parent])

    def test_sessions_that_measured_different_things_arent_pooled(self) -> None:
        path, _ = self.session("solo", "work", "fast")
        record = json.loads(path.read_text())
        variants = record["variants"]
        elsewhere = {**variants, "candidate": {**variants["candidate"], "build": "/elsewhere"}}
        another = {**variants, "candidate": {**variants["candidate"], "env": {"OMP_PROC_BIND": "true"}}}
        for key, value in (
            ("cpus", "99"),
            ("threads", 9),
            ("control", True),
            ("topology", {}),
            ("variants", elsewhere),
            ("variants", another),
        ):
            (path.parent / "002.json").write_text(json.dumps({**record, "seed": 5, key: value}))
            with self.assertRaisesRegex(timing.Refused, "measured different things"):
                timing.read(path.parent, [])
        (path.parent / "002.json").write_text(json.dumps(record))
        with self.assertRaisesRegex(timing.Refused, "one seed"):
            timing.read(path.parent, [])
        (path.parent / "002.json").write_text(json.dumps({**record, "schema": "ir-lean.kernels.demand/1"}))
        with self.assertRaises(schemas.SchemaError):
            timing.read(path.parent, [])


class Protocol(unittest.TestCase):
    """The statistic and the rule, on numbers alone."""

    def test_the_interval_is_the_percentiles_of_resampled_medians(self) -> None:
        ratios = [1.01, 1.02, 0.99, 1.04, 1.03, 1.00, 1.05]
        rng = random.Random(9)
        medians = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(20000))
        self.assertEqual(protocol.interval(ratios, 9), (medians[499], medians[19499]))
        self.assertEqual(protocol.interval(ratios, 9), protocol.interval(ratios, 9))

    def test_a_ratio_is_above_one_when_the_candidate_is_faster(self) -> None:
        self.assertEqual(protocol.ratio(12.0, 10.0, protocol.TIME), 1.2)
        self.assertEqual(protocol.ratio(100.0, 120.0, protocol.RATE), 1.2)
        for bad in ((0.0, 1.0), (1.0, -1.0)):
            with self.assertRaises(ValueError):
                protocol.ratio(*bad, protocol.TIME)

    def held(self, ratio: float, **options: Any) -> set[str]:
        sessions = options.pop("sessions", [[ratio] * 15, [ratio] * 15])
        kinds = options.pop("kinds", [protocol.CONFIRMATION] * len(sessions))
        found = protocol.conditions({"seconds": sessions}, kinds, 1, **options)["conditions"]
        return {name for name, c in found.items() if c["held"]}

    def test_the_conditions(self) -> None:
        both = {"confirmation", "pairs", "others"}
        above, below = {"interval_above", "sessions_above"}, {"interval_below", "sessions_below"}
        self.assertEqual(self.held(1.005), both | above)
        self.assertEqual(self.held(1.0049), both | {"sessions_above"})
        self.assertEqual(self.held(1 / 1.005), both | below)
        self.assertEqual(self.held(1.0), both)
        # Each condition, broken alone.
        kinds = [protocol.CONFIRMATION, protocol.EXPLORATORY]
        self.assertEqual(self.held(1.2, kinds=kinds), (both | above) - {"confirmation"})
        self.assertEqual(self.held(1.2, sessions=[[1.2] * 29]), (both | above) - {"pairs"})
        self.assertEqual(self.held(1.2, sessions=[[1.2] * 14, [1.2] * 15]), (both | above) - {"pairs"})
        self.assertEqual(self.held(1.2, sessions=[[1.2] * 25, [0.999] * 5]), both | {"interval_above"})
        self.assertEqual(self.held(1.2, others={"w": [0.9, 0.999]}), (both | above) - {"others"})
        self.assertEqual(self.held(1.2, others={"w": None}), (both | above) - {"others"})
        self.assertEqual(self.held(1.2, others={"w": [0.99, 1.0]}), both | above)

    def test_each_figure_is_judged_alone(self) -> None:
        kinds = [protocol.CONFIRMATION] * 2
        one_slower = {"a": [[1.5] * 15] * 2, "b": [[0.9] * 15] * 2}
        held = {n for n, c in protocol.conditions(one_slower, kinds, 1)["conditions"].items() if c["held"]}
        self.assertEqual(held, {"confirmation", "pairs", "others"})
        both = {"a": [[1.5] * 15] * 2, "b": [[1.01] * 15] * 2}
        found = protocol.conditions(both, kinds, 1)
        self.assertTrue(found["conditions"]["interval_above"]["held"])
        self.assertEqual(found["figures"]["b"]["pooled"]["median"], 1.01)


def protocol_session(where: Path, ratio: float, workload: str = "argon2id", **change: Any) -> Path:
    """Writes the record of a complete confirmation session of 15 pairs by the protocol, as the next of the
    directory `where`, and returns `where`. Each run of the baseline took `ratio` times the candidate's 2
    seconds. tests/deny_all_test.py reads these too."""
    variants = {
        v: {"build": f"/builds/{v}", "env": {}, "identity": {"loads": [], "id": v}} for v in timing.VARIANTS
    }
    ran = {"exit": 0, "limit": None}
    runs = {
        "baseline": {**ran, "figures": {"seconds": 2.0 * ratio}, "seconds": 2.0 * ratio},
        "candidate": {**ran, "figures": {"seconds": 2.0}, "seconds": 2.0},
    }
    where.mkdir(parents=True, exist_ok=True)
    number = len(list(where.iterdir())) + 1
    record = {
        "schema": schemas.KERNELS_SESSION,
        "project": "libsodium",
        "workload": workload,
        "workloads": ["argon2id", "secretstream"],
        "kind": protocol.CONFIRMATION,
        "control": False,
        "seed": number,
        "cpus": "12",
        "topology": {"12": {"siblings": "12,28", "l3": "8-15,24-31"}},
        "threads": 1,
        "measure": "time",
        "rule": protocol.PROTOCOL.as_record(),
        "manifest": {"sha256": hashing.sha256_file(kernels.MANIFEST), "corpus": True},
        "variants": variants,
        "status": timing.COMPLETE,
        "planned_pairs": 15,
        "pairs": [{"pair": n, "order": list(timing.VARIANTS), **runs} for n in range(1, 16)],
        **change,
    }
    (where / f"{number:03d}.json").write_text(json.dumps(record))
    return where


class Reading(unittest.TestCase):
    """What sessions come to, which only irlean.verdict says: on records made here, by the protocol, so each
    reading is seconds of arithmetic. A record is a session's own, with its figures set."""

    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp(prefix="reading-test-"))
        self.addCleanup(shutil.rmtree, self.root, True)

    def write(self, name: str, ratio: float, workload: str = "argon2id", **change: Any) -> Path:
        return protocol_session(self.root / name, ratio, workload, **change)

    def reads(self, ratio: float = 1.01, other: float = 1.0, **change: Any) -> dict[str, Any]:
        for _ in range(2):
            mine = self.write("mine", ratio, **change)
            theirs = self.write("theirs", other, workload="secretstream")
        return timing.read(mine, [theirs])

    def test_faster_slower_and_neither(self) -> None:
        reading = self.reads(1.01)
        self.assertEqual(
            (reading["status"], reading["reason"], reading["exit_code"]), ("faster", "timing.faster", 0)
        )
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "exhaustive")
        slower = self.setUp() or self.reads(0.98)
        self.assertEqual(
            (slower["status"], slower["reason"], slower["exit_code"]), ("slower", "timing.slower", 2)
        )
        neither = self.setUp() or self.reads(1.004)
        self.assertEqual((neither["status"], neither["exit_code"]), ("inconclusive", 3))
        self.assertEqual(neither["decisions"]["timing.faster"]["reason"], "interval_above")

    def test_each_thing_that_takes_faster_away(self) -> None:
        rule = {**protocol.PROTOCOL.as_record(), "min_pairs": 6}
        changes: list[tuple[dict[str, Any], str]] = [
            ({"manifest": {"sha256": "0" * 64, "corpus": True}}, "corpus"),
            ({"manifest": {"sha256": hashing.sha256_file(kernels.MANIFEST), "corpus": False}}, "corpus"),
            ({"rule": rule}, "rule"),
            ({"planned_pairs": 16}, "incomplete"),
            ({"planned_pairs": 14}, "incomplete"),
        ]
        for change, why in changes:
            self.setUp()
            reading = self.reads(**change)
            self.assertEqual((reading["status"], reading["exit_code"]), ("inconclusive", 3), change)
            self.assertEqual(reading["decisions"]["timing.faster"]["reason"], why, change)
        # The other workload slower, or not given.
        self.setUp()
        self.assertEqual(self.reads(other=0.99)["decisions"]["timing.faster"]["reason"], "others")
        self.setUp()
        for _ in range(2):
            mine = self.write("mine", 1.01)
        self.assertEqual(timing.read(mine, [])["decisions"]["timing.faster"]["reason"], "others")
        # A run that didn't end well, however it got into a record: an exit code, a signal, or a limit.
        for exit_code, limit, why in (
            (1, None, "case_failed"),
            (-11, None, "tool_failed"),
            (0, "time_limit", "time_limit"),
        ):
            self.setUp()
            reading = self.reads()
            path = self.root / "mine" / "001.json"
            record = json.loads(path.read_text())
            record["pairs"][3]["candidate"] |= {"exit": exit_code, "limit": limit}
            path.write_text(json.dumps(record))
            reading = timing.read(path.parent, [self.root / "theirs"])
            self.assertEqual(reading["status"], "inconclusive", why)
            self.assertEqual(reading["decisions"]["timing.faster"]["reason"], why)
        # A confirmation session that failed: what it planned was never timed.
        self.setUp()
        self.reads()
        self.write(
            "mine", 1.01, status=timing.FAILED, pairs=[], failure="a run of the candidate didn't end well"
        )
        reading = timing.read(self.root / "mine", [self.root / "theirs"])
        self.assertEqual(reading["status"], "inconclusive")
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "incomplete")
        self.assertEqual(reading["sessions"][2], {"session": "003.json", "status": timing.FAILED})

    def edit(self, name: str, number: int, change: Any) -> None:
        """Changes one record of a directory in place, as `change` does to it."""
        path = self.root / name / f"{number:03d}.json"
        record = json.loads(path.read_text())
        change(record)
        path.write_text(json.dumps(record))

    def test_the_other_workload_is_held_to_what_the_workloads_own_is(self) -> None:
        def reason() -> str:
            reading = timing.read(self.root / "mine", [self.root / "theirs"])
            self.assertEqual((reading["status"], reading["exit_code"]), ("inconclusive", 3))
            return str(reading["decisions"]["timing.faster"]["reason"])

        # A confirmation session of it that failed, with or without the pairs it had.
        self.reads()
        self.write("theirs", 1.0, workload="secretstream", status=timing.FAILED, pairs=[])
        self.assertEqual(reason(), "incomplete")
        self.setUp()
        self.reads()
        self.write("theirs", 1.0, workload="secretstream", status=timing.FAILED)
        self.assertEqual(reason(), "incomplete")
        # A run of it that died of a signal, or didn't exit 0.
        for exit_code, why in ((-11, "tool_failed"), (1, "case_failed")):
            self.setUp()
            self.reads()
            self.edit("theirs", 1, lambda r, code=exit_code: r["pairs"][2]["baseline"].update(exit=code))
            self.assertEqual(reason(), why)
        # Sessions of it under another manifest, or read by another rule.
        loose = {**protocol.PROTOCOL.as_record(), "threshold": 1.0}
        for change, why in (
            ({"manifest": {"sha256": "0" * 64, "corpus": True}}, "corpus"),
            ({"rule": loose}, "rule"),
        ):
            self.setUp()
            for _ in range(2):
                self.write("mine", 1.01)
                self.write("theirs", 1.0, workload="secretstream", **change)
            self.assertEqual(reason(), why)
        # Two directories of it, one of them slower, whichever comes first.
        self.setUp()
        self.reads()
        for _ in range(2):
            slow = self.write("slow", 0.9, workload="secretstream")
        for order in ([self.root / "theirs", slow], [slow, self.root / "theirs"]):
            with self.assertRaisesRegex(timing.Refused, "a second directory of secretstream's sessions"):
                timing.read(self.root / "mine", order)

    def test_only_what_each_run_measured_is_read(self) -> None:
        # A ratio a record states for itself isn't read: these runs took the same time.
        self.reads(1.0)
        for number in (1, 2):
            self.edit("mine", number, lambda r: [p.update(ratios={"seconds": 1.5}) for p in r["pairs"]])
        reading = timing.read(self.root / "mine", [self.root / "theirs"])
        self.assertEqual(reading["status"], "inconclusive")
        self.assertEqual(reading["result"]["figures"]["seconds"]["pooled"]["median"], 1.0)
        # A session that says it failed has no pairs, whatever it holds.
        self.setUp()
        self.write("mine", 1.01)
        self.write("mine", 1.01, status=timing.FAILED)
        self.write("mine", 1.01, status=timing.FAILED)
        for _ in range(2):
            self.write("theirs", 1.0, workload="secretstream")
        reading = timing.read(self.root / "mine", [self.root / "theirs"])
        self.assertEqual(reading["result"]["figures"]["seconds"]["pooled"]["pairs"], 15)
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "incomplete")
        # The project's other workloads are the manifest's, not what a record lists.
        self.setUp()
        for _ in range(2):
            mine = self.write("mine", 1.01, workloads=["argon2id"])
        self.assertEqual(timing.read(mine, [])["decisions"]["timing.faster"]["reason"], "others")
        # Every run measured the same figures, each a positive, finite number.
        for change, why in (
            (lambda r: r["pairs"][4]["candidate"]["figures"].update(extra=1.0), "didn't all measure"),
            (lambda r: r["pairs"][4]["candidate"]["figures"].update(seconds=float("inf")), "finite"),
            (lambda r: r["pairs"][4]["baseline"]["figures"].update(seconds=0.0), "positive"),
            (lambda r: r["pairs"][4]["baseline"]["figures"].update(seconds="2.0"), "positive"),
        ):
            self.setUp()
            self.reads()
            self.edit("mine", 2, change)
            with self.assertRaisesRegex(timing.Refused, why):
                timing.read(self.root / "mine", [self.root / "theirs"])
        for bad in (float("inf"), float("nan"), 0.0, -1.0, True, "1"):
            with self.assertRaises(ValueError):
                protocol.ratio(1.0, typing.cast("float", bad), protocol.RATE)

    def test_deny_all_takes_faster_away(self) -> None:
        os.environ[verdict.DENY_ALL] = "1"
        self.addCleanup(os.environ.pop, verdict.DENY_ALL)
        reading = self.reads(1.01)
        self.assertEqual((reading["status"], reading["reason"], reading["exit_code"]), ("error", "denied", 1))


if __name__ == "__main__":
    unittest.main()
