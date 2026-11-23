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


def sh(*argv: Any) -> None:
    r = proc.run(argv, timeout=300)
    if not r.ok:
        raise RuntimeError(f"{' '.join(map(str, argv))}\n{r.output}")


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
        # The base again, byte for byte, in another directory: a control.
        shutil.copytree(cls.root / "base", cls.root / "same")
        # A candidate whose program loads the base's library, as a link that kept the old path would.
        cls.build("stolen", loops=10_000_000, loads="base")

    @classmethod
    def build(cls, name: str, loops: int, wrong: int = 0, loads: str | None = None) -> None:
        b = cls.root / name
        b.mkdir()
        sh(
            "clang",
            "-O1",
            "-shared",
            "-fPIC",
            f"-DLOOPS={loops}UL",
            f"-DWRONG={wrong}",
            cls.root / "work.c",
            "-o",
            b / "libwork.so",
        )
        where = cls.root / (loads or name)
        sh("clang", "-O1", cls.root / "bench.c", f"-L{b}", "-lwork", f"-Wl,-rpath,{where}", "-o", b / "bench")

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
                "candidate": timing.Variant(self.root / candidate),
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
        # A run shorter than the rule's minimum is repeated until it isn't.
        self.assertGreater(record["repeat"], 1)
        for p in record["pairs"]:
            for v in timing.VARIANTS:
                self.assertGreaterEqual(p[v]["seconds"], RULE.min_seconds * 0.5)
                self.assertGreaterEqual(p[v]["user_s"], 0)
                self.assertIn("load1", p[v])
            self.assertEqual(p["ratios"], {"seconds": p["baseline"]["seconds"] / p["candidate"]["seconds"]})
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
        # Every condition of the rule holds: a quarter of the work is well over half a percent faster.
        held = {name: c["held"] for name, c in reading["result"]["conditions"].items()}
        self.assertEqual(
            {n for n, h in held.items() if h},
            {"confirmation", "pairs", "interval_above"} | {"sessions_above", "others"},
        )
        # And it still isn't shown faster: the rule's minimums were lowered and the manifest isn't the
        # corpus's, so the comparison isn't by the protocol, which is the first thing irlean.verdict asks.
        self.assertEqual((reading["status"], reading["exit_code"]), ("inconclusive", 3))
        self.assertEqual(reading["decisions"]["timing.faster"]["reason"], "corpus")

    def test_only_confirmation_sessions_of_enough_pairs_count(self) -> None:
        path, _ = self.session("solo", "work", "fast", kind=protocol.EXPLORATORY)
        reading = timing.read(path.parent, [])
        self.assertEqual(
            (reading["status"], reading["why"]), ("inconclusive", "no confirmation session with pairs")
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

    # Failures.

    def test_a_run_that_fails_fails_the_session(self) -> None:
        record = self.failed("tiny", "fails", "fast")
        self.assertIn("exit code 3", record["failure"])
        self.assertNotIn("warm_up", record)
        # The third call of each variant fails, which is its second pair: the first pair isn't kept.
        record = self.failed("tiny", "flaky", "fast")
        self.assertIn("exit code 4", record["failure"])
        self.assertIn("warm_up", record)
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

    def test_a_library_that_changes_fails_the_session(self) -> None:
        shutil.copytree(self.root / "fast", self.root / "appended")
        record = self.failed("tiny", "mutates", "appended")
        self.assertIn("changed while the session ran", record["failure"])

    # What a candidate loads.

    def test_a_candidate_that_loads_the_baselines_code_is_refused(self) -> None:
        record = self.failed("solo", "work", "stolen")
        self.assertIn("loads what the baseline loads", record["failure"])
        self.assertNotIn("warm_up", record)

    def test_a_library_that_isnt_found_fails_the_session(self) -> None:
        # ldd says "not found" on a line this reads as neither a library nor nothing, so it's an error.
        self.build("orphan", loops=10_000_000)
        (self.root / "orphan" / "libwork.so").unlink()
        record = self.failed("solo", "work", "orphan")
        self.assertIn("printed a line this doesn't read", record["failure"])
        self.assertIn("not found", record["failure"])

    def test_a_control_is_declared_and_loads_the_same(self) -> None:
        record = self.failed("solo", "work", "same")
        self.assertIn("this isn't a control", record["failure"])
        record = self.failed("solo", "work", "fast", control=True)
        self.assertIn("these differ", record["failure"])
        for _ in range(2):
            path, record = self.session("solo", "work", "same", control=True)
            self.assertEqual(record["status"], timing.COMPLETE)
        reading = timing.read(path.parent, [])
        # A control says whether its interval contains 1, and nothing about faster or slower.
        self.assertEqual((reading["status"], reading["exit_code"]), ("control", 4))
        self.assertNotIn("decisions", reading)
        self.assertIn(reading["control_contains_one"], (True, False))
        self.assertLess(abs(reading["pooled"]["seconds"]["median"] - 1), 0.5)

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
            plan = self.plan("tiny", "print", "fast")
            plan.variants["candidate"].env["TINY"] = "2"
            timing.session(plan)

    def test_an_input_is_the_one_the_manifest_pins(self) -> None:
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
        (inputs / "data").write_text("other data\n")
        with self.assertRaisesRegex(timing.Refused, "isn't the data the manifest pins"):
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
        # Sessions of other builds, or of this workload, aren't the project's other workload.
        other, _ = self.session(
            "two", "print", "wrong", pairs=1, sessions=self.root / "sessions" / "elsewhere"
        )
        self.assertEqual(schemas.read(other, schemas.KERNELS_SESSION)["status"], timing.FAILED)
        with self.assertRaisesRegex(timing.Refused, "no confirmation session of another workload"):
            timing.read(work.parent, [work.parent])
        # Nor are sessions of the other workload between other builds.
        half, record = self.session("two", "print", "half")
        self.assertEqual(record["status"], timing.COMPLETE)
        with self.assertRaisesRegex(timing.Refused, "isn't sessions of the same two builds"):
            timing.read(work.parent, [half.parent])
        # A copy of the candidate loads the same bytes from another place, so its sessions go beside the
        # candidate's, and reading them together is refused: one directory is sessions of two builds.
        shutil.copytree(self.root / "fast", self.root / "fast-again")
        again, record = self.session("two", "print", "fast-again")
        self.assertEqual((record["status"], again.parent), (timing.COMPLETE, printed.parent))
        with self.assertRaisesRegex(timing.Refused, "measured different things: .*candidate's build"):
            timing.read(work.parent, [printed.parent])

    def test_sessions_that_measured_different_things_arent_pooled(self) -> None:
        path, _ = self.session("solo", "work", "fast")
        record = json.loads(path.read_text())
        for key, value in (("cpus", "99"), ("threads", 9), ("control", True)):
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
    """Writes the record of a complete confirmation session of 15 pairs, each of `ratio`, by the protocol,
    as the next of the directory `where`, and returns `where`. tests/deny_all_test.py reads two of these."""
    variants = {
        v: {"build": f"/builds/{v}", "env": {}, "identity": {"loads": [], "id": v}} for v in timing.VARIANTS
    }
    run = {"exit": 0, "limit": None, "figures": {"seconds": 2.0}, "seconds": 2.0}
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
        "threads": 1,
        "measure": "time",
        "rule": protocol.PROTOCOL.as_record(),
        "manifest": {"sha256": hashing.sha256_file(kernels.MANIFEST), "corpus": True},
        "variants": variants,
        "status": timing.COMPLETE,
        "planned_pairs": 15,
        "pairs": [
            {"pair": n, "order": list(timing.VARIANTS), "baseline": run, "candidate": run}
            | {"ratios": {"seconds": ratio}}
            for n in range(1, 16)
        ],
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

    def test_deny_all_takes_faster_away(self) -> None:
        os.environ[verdict.DENY_ALL] = "1"
        self.addCleanup(os.environ.pop, verdict.DENY_ALL)
        reading = self.reads(1.01)
        self.assertEqual((reading["status"], reading["reason"], reading["exit_code"]), ("error", "denied", 1))


if __name__ == "__main__":
    unittest.main()
