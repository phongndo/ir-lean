#!/usr/bin/env python3
"""Checks the kernel corpus's manifest, bench/kernels/manifest.toml, against the rules in
bench/kernels/kernels.py, without LLVM, Lean or the network. docs/kernels.md.

It fails if the manifest breaks a rule, if a corpus that's only proposed approves anything, if an approved one
isn't the maintainer's list of 2026-11-10 with its date and where it's recorded, or if a fixed corpus's digest
isn't the one its lock and amendments end at: so a pin, a hash, a flag, a kernel, a workload, its check or an
input of an approved project, or the driver a workload runs, can't change without an amendment that says why.
The corpus is fixed: the six of 2026-11-10, each workload saying what's measured, rates among them, and how a
candidate is checked, by its output or by the project's own test against known answers. Cases built to break
each rule show it's refused. It also checks docs/kernels.md names every project with its commit and standing,
that bench/kernels/results/demand.json is about the manifest's pins and kernels, and how
bench/kernels/demand.py reads IR and the emitter's refusals. Only the standard library and tools/irlean, in
under a second.

usage: tests/kernels_test.py
"""

import copy
import importlib.util
import sys
import typing
import unittest
from collections.abc import Callable
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "bench" / "kernels"
sys.path.append(str(ROOT / "tools"))
# bench/kernels/demand.py imports kernels.py as a script beside it does.
sys.path.append(str(HERE))
from irlean import schemas  # noqa: E402


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


kernels = load("kernels", HERE / "kernels.py")
demand = load("demand", HERE / "demand.py")
reference = load("reference", HERE / "libsodium" / "reference.py")
MANIFEST = kernels.load()
DOC = ROOT / "docs" / "kernels.md"
RESULTS = HERE / "results" / "demand.json"
WORD = {"recommended": "**Recommended**", "alternate": "Alternate", "rejected": "Rejected"}
# What the maintainer approved on 2026-11-10: the proposal's six recommended projects. docs/roadmap.md.
APPROVED_ON = "2026-11-10"
SIX = ["flac", "libsodium", "libwebp", "llama.cpp", "xxhash", "zlib-ng"]
# The workloads whose own figure is the measure, because the benchmark runs for a fixed time: docs/kernels.md.
RATES = {("llama.cpp", "pp512"), ("llama.cpp", "tg128"), ("xxhash", "bench")}
# Those that print only timings, which the project's own test checks against known answers.
TIMINGS = {("libsodium", "argon2id"), ("xxhash", "bench")}


def names(status: str) -> list[str]:
    return sorted(n for n, p in MANIFEST["project"].items() if p["status"] == status)


def workload(m: dict[str, Any], project: str, name: str) -> dict[str, Any]:
    return next(w for w in m["project"][project]["workload"] if w["name"] == name)


def anchored(where: str) -> None:
    """Fails unless `where`, PATH#ANCHOR, is a heading of a file in the repo."""
    path, _, anchor = where.partition("#")
    doc = ROOT / path
    assert doc.is_file(), path
    headings = [line.lstrip("#").strip() for line in doc.read_text().splitlines() if line.startswith("#")]
    slugs = {"".join(c for c in h.lower().replace(" ", "-") if c.isalnum() or c == "-") for h in headings}
    assert anchor in slugs, f"{path} has no heading #{anchor}"


def proposed() -> dict[str, Any]:
    """The manifest as it stood before the maintainer approved a list."""
    m = copy.deepcopy(MANIFEST)
    m["corpus"].update(state="proposed", approved=[])
    for key in ("approved_on", "decided_in"):
        m["corpus"].pop(key, None)
    m.pop("lock", None)
    m.pop("amendment", None)
    return m


def fixed() -> dict[str, Any]:
    """The manifest as it would stand with the recommended projects approved."""
    return kernels.fixed(MANIFEST, names("recommended"), "2026-11-10", "#0")


def changed(manifest: dict[str, Any], change: Callable[[dict[str, Any]], Any]) -> dict[str, Any]:
    m = copy.deepcopy(manifest)
    change(m)
    return m


def amended(before: dict[str, Any], after: dict[str, Any], **fields: str) -> dict[str, Any]:
    """`after`, with an amendment from where `before` stood to where it stands."""
    m = copy.deepcopy(after)
    at = m.get("amendment", [])[-1]["to"] if m.get("amendment") else before["lock"]["sha256"]
    entry = {"on": "2026-12-01", "reason": "the pin moved", "approved_in": "#1", "from": at}
    entry["to"] = kernels.digest(m)
    m.setdefault("amendment", []).append({**entry, **fields})
    return m


class Manifest(unittest.TestCase):
    def test_it_meets_every_rule(self) -> None:
        self.assertEqual(kernels.problems(MANIFEST), [])

    def test_the_proposal_recommends_at_least_three_projects_in_three_domains(self) -> None:
        recommended = names("recommended")
        self.assertGreaterEqual(len(recommended), kernels.MIN_PROJECTS)
        self.assertGreaterEqual(len({MANIFEST["project"][n]["domain"] for n in recommended}), 3)
        for domain in kernels.DOMAINS:
            self.assertTrue([n for n, p in MANIFEST["project"].items() if p["domain"] == domain], domain)

    def test_a_proposed_corpus_approves_nothing(self) -> None:
        before = proposed()
        self.assertEqual(kernels.problems(before), [])
        some = names("recommended")[:3]
        for change in (
            lambda m: m["corpus"].update(approved=some),
            lambda m: m.update(lock={"sha256": "0" * 64, "approved_on": "2026-11-10", "approved_in": "#0"}),
            lambda m: m.update(amendment=[{"on": "2026-11-10"}]),
        ):
            self.assertTrue(kernels.problems(changed(before, change)))

    def test_each_rule_refuses_what_breaks_it(self) -> None:
        live = names("recommended")[0]
        dead = names("rejected")[0]

        def project(m: dict[str, Any], name: str = live) -> dict[str, Any]:
            return m["project"][name]

        def first(m: dict[str, Any]) -> dict[str, Any]:
            return project(m)["workload"][0]

        def bench(m: dict[str, Any]) -> dict[str, Any]:
            return workload(m, "xxhash", "bench")

        def driven(m: dict[str, Any]) -> dict[str, Any]:
            return workload(m, "libsodium", "secretstream")

        def known(m: dict[str, Any]) -> dict[str, Any]:
            return workload(m, "libsodium", "argon2id")["check"][0]

        output = {"kind": "output", "what": "its output", "output": ["stdout"]}
        cases: dict[str, Callable[[dict[str, Any]], Any]] = {
            # A manifest of the first version, whose workload was one table, is refused rather than misread.
            "schema": lambda m: m.update(schema="ir-lean.kernels.manifest/1"),
            "isn't one of proposed": lambda m: m["corpus"].update(state="settled"),
            "corpus.llvm_tag": lambda m: m["corpus"].update(llvm_tag="llvmorg-99.0.0"),
            "corpus.opt": lambda m: m["corpus"].update(opt="-O2"),
            "corpus.target": lambda m: m["corpus"].update(target="aarch64-unknown-linux-gnu"),
            "rev isn't a full commit hash": lambda m: project(m).update(rev="80d2c0c"),
            "nix_hash isn't an SRI SHA-256": lambda m: project(m).update(nix_hash="sha256-abc"),
            "domain": lambda m: project(m).update(domain="parsing"),
            "status": lambda m: project(m).update(status="maybe"),
            "license": lambda m: project(m).update(license="GPL-3.0-only"),
            "repository": lambda m: project(m).update(repository="https://example.org/a/b"),
            "no unit": lambda m: project(m).pop("unit"),
            "no kernel named": lambda m: [u.update(kernels=[]) for u in project(m)["unit"]],
            "is also in": lambda m: project(m)["unit"].append(
                {"source": "other.c", "kernels": [project(m)["unit"][0]["kernels"][0]]}
            ),
            "a path inside the project": lambda m: project(m)["unit"][0].update(source="../x.c"),
            "isn't a unit's to set": lambda m: project(m)["unit"][0].update(flags=["-O2"]),
            "names the processor": lambda m: project(m).update(flags=["-march=native"]),
            "no workload": lambda m: project(m).pop("workload"),
            "no run": lambda m: first(m).pop("run"),
            "two workloads have that name": lambda m: project(m)["workload"].append(copy.deepcopy(first(m))),
            "no SHA-256": lambda m: project(m).update(
                input=[{"name": "a", "url": "https://example.org/a", "sha256": "abc"}]
            ),
            "no https url": lambda m: project(m).update(
                input=[{"name": "a", "url": "http://example.org/a", "sha256": "0" * 64}]
            ),
            "{input:nothing} in": lambda m: first(m)["run"][0].append("{input:nothing}"),
            "{nowhere} in": lambda m: first(m)["run"][0].append("{nowhere}/a"),
            "threads isn't a count": lambda m: first(m).update(threads=0),
            "measure 'cycles'": lambda m: first(m).update(measure="cycles"),
            "a rate says what figure": lambda m: bench(m).pop("rate"),
            "only a workload measured as a rate": lambda m: first(m).update(rate="MB/s"),
            "so its output check runs its own": lambda m: bench(m).update(check=[output]),
            "kind 'maybe'": lambda m: first(m)["check"][0].update(kind="maybe"),
            "no what, saying": lambda m: first(m)["check"][0].pop("what"),
            "names what's hashed": lambda m: first(m).update(check=[{**output, "output": []}]),
            "isn't stdout or a file in": lambda m: first(m).update(check=[{**output, "output": ["/tmp/a"]}]),
            "sha256 isn't a SHA-256": lambda m: first(m).update(check=[{**output, "sha256": "abc"}]),
            "only a known-answers check names a test": lambda m: first(m).update(
                check=[{**output, "test": ["a.c"]}]
            ),
            "runs the project's test, in `run`": lambda m: known(m).pop("run"),
            "names the project's test and its answers": lambda m: known(m).pop("test"),
            "isn't a path in the project": lambda m: known(m).update(test=["../a.c"]),
            "only an output check has sha256": lambda m: known(m).update(sha256="0" * 64),
            "driver_sha256 isn't the SHA-256": lambda m: driven(m).update(driver_sha256="0" * 64),
            "driver isn't a path in bench/kernels/": lambda m: driven(m).update(driver="/etc/hosts"),
            "doesn't exist": lambda m: driven(m).update(driver="bench/kernels/libsodium/nothing.c"),
            "build doesn't compile the driver": lambda m: driven(m).update(build=[["true"]]),
            "driver_sha256 without a driver": lambda m: first(m).update(driver_sha256="0" * 64),
            "no project_opt": lambda m: project(m).pop("project_opt"),
            "has no SIMD kernel to compile": lambda m: project(m).update(simd="assembly"),
            "only a rejected project has": lambda m: project(m).update(fails=[2]),
            "names the criteria it fails": lambda m: project(m, dead).pop("fails"),
            "says why": lambda m: project(m, dead).pop("why"),
            "which has no [project": lambda m: m["corpus"].update(approved=["nothing"]),
        }
        for message, change in cases.items():
            found = kernels.problems(changed(MANIFEST, change))
            self.assertTrue([line for line in found if message in line], f"{message}: {found}")


class Approved(unittest.TestCase):
    def test_the_approval_points_to_where_its_recorded(self) -> None:
        anchored(MANIFEST["corpus"]["decided_in"])

    def test_an_approved_corpus_needs_three_projects_its_date_and_where_and_no_lock(self) -> None:
        m = changed(
            proposed(),
            lambda m: m["corpus"].update(
                state="approved", approved=SIX, approved_on=APPROVED_ON, decided_in="docs/roadmap.md"
            ),
        )
        self.assertEqual(kernels.problems(m), [])
        lock = {"sha256": "0" * 64, "approved_on": APPROVED_ON, "approved_in": "#0"}
        cases: dict[str, Callable[[dict[str, Any]], Any]] = {
            "an approved corpus has at least 3 projects": lambda m: m["corpus"].update(approved=SIX[:2]),
            "corpus.approved_on isn't a date": lambda m: m["corpus"].update(approved_on="today"),
            "corpus.decided_in is empty": lambda m: m["corpus"].pop("decided_in"),
            "while the corpus is only approved: fixing": lambda m: m.update(lock=lock),
            "while the corpus is only approved: nothing": lambda m: m.update(amendment=[{"on": APPROVED_ON}]),
            "which is rejected": lambda m: m["corpus"]["approved"].append(names("rejected")[0]),
        }
        for message, change in cases.items():
            found = kernels.problems(changed(m, change))
            self.assertTrue([line for line in found if message in line], f"{message}: {found}")


class Locked(unittest.TestCase):
    """The corpus as it was fixed on 2026-11-10, once decision 7's driver was written."""

    def test_the_six_of_2026_11_10_are_fixed_by_the_lock(self) -> None:
        corpus, lock = MANIFEST["corpus"], MANIFEST["lock"]
        self.assertEqual(corpus["state"], "fixed")
        self.assertEqual(sorted(corpus["approved"]), SIX)
        self.assertEqual(sorted(corpus["approved"]), names("recommended"))
        self.assertEqual(corpus["approved_on"], APPROVED_ON)
        self.assertEqual(lock["approved_on"], APPROVED_ON)
        anchored(lock["approved_in"])
        if not MANIFEST.get("amendment"):
            self.assertEqual(lock["sha256"], kernels.digest(MANIFEST))

    def test_every_workload_of_the_six_says_whats_measured_and_how_its_checked(self) -> None:
        rates, timings = set(), set()
        for name in SIX:
            for w in MANIFEST["project"][name]["workload"]:
                self.assertIn(w["measure"], kernels.MEASURES, (name, w["name"]))
                self.assertTrue(w["check"], (name, w["name"]))
                if w["measure"] == "rate":
                    rates.add((name, w["name"]))
                if any(c["kind"] == "known-answers" for c in w["check"]):
                    timings.add((name, w["name"]))
        self.assertEqual(rates, RATES)
        self.assertEqual(timings, TIMINGS)

    def test_libsodiums_workloads_are_decision_7s(self) -> None:
        workloads = MANIFEST["project"]["libsodium"]["workload"]
        self.assertEqual([w["name"] for w in workloads], ["argon2id", "secretstream"])
        driver = workload(MANIFEST, "libsodium", "secretstream")
        self.assertEqual(driver["driver"], "bench/kernels/libsodium/secretstream.c")
        self.assertIn("crypto_secretstream_xchacha20poly1305_push", (ROOT / driver["driver"]).read_text())
        # Its check compares output, and benchmark mode's is checked by the test in its checking mode.
        self.assertEqual([c["kind"] for c in driver["check"]], ["output"])
        argon2id = workload(MANIFEST, "libsodium", "argon2id")
        self.assertIn("CPPFLAGS=-DBENCHMARKS -DITERATIONS=200", argon2id["build"][-1])
        check = argon2id["check"][0]["run"]
        self.assertEqual(check[0][-1], "clean")
        self.assertFalse([arg for command in check for arg in command if "BENCHMARKS" in arg])

    def test_a_fixed_corpus_needs_a_check_and_a_measure_for_every_workload(self) -> None:
        for m in (MANIFEST, fixed()):
            for message, change in {
                "it has no check": lambda m: workload(m, "zlib-ng", "decompress").pop("check"),
                "says what's measured": lambda m: workload(m, "flac", "encode-8").pop("measure"),
            }.items():
                found = kernels.problems(changed(m, change))
                self.assertTrue([line for line in found if message in line], f"{message}: {found}")
        # An alternate isn't in the fixed corpus, and needs neither until an amendment adds it.
        self.assertFalse([w for w in MANIFEST["project"]["zstd"]["workload"] if "check" in w])


class Fixed(unittest.TestCase):
    def test_approving_the_recommended_list_meets_every_rule(self) -> None:
        self.assertEqual(kernels.problems(fixed()), [])

    def test_a_fixed_corpus_needs_its_lock_three_projects_and_no_rejected_one(self) -> None:
        m = fixed()
        two = kernels.fixed(MANIFEST, names("recommended")[:2], "2026-11-10", "#0")
        with_rejected = kernels.fixed(
            MANIFEST, [*names("recommended"), names("rejected")[0]], "2026-11-10", "#0"
        )
        cases = {
            "has no [lock]": changed(m, lambda m: m.pop("lock")),
            "lock has no approved_on": changed(m, lambda m: m["lock"].pop("approved_on")),
            "lock.approved_on isn't a date": changed(m, lambda m: m["lock"].update(approved_on="today")),
            "at least 3 projects": two,
            "which is rejected": with_rejected,
        }
        for message, broken in cases.items():
            found = kernels.problems(broken)
            self.assertTrue([line for line in found if message in line], f"{message}: {found}")

    def test_any_change_to_what_was_approved_fails(self) -> None:
        other = names("alternate")[0]

        def project(m: dict[str, Any]) -> dict[str, Any]:
            return m["project"][m["corpus"]["approved"][0]]

        def first(m: dict[str, Any]) -> dict[str, Any]:
            return project(m)["workload"][0]

        def driven(m: dict[str, Any]) -> dict[str, Any]:
            return workload(m, "libsodium", "secretstream")

        changes: dict[str, Callable[[dict[str, Any]], Any]] = {
            "the commit": lambda m: project(m).update(rev="0" * 40),
            "the hash": lambda m: project(m).update(nix_hash="sha256-" + "A" * 43 + "="),
            "the tag": lambda m: project(m).update(tag="v9"),
            "a project's flags": lambda m: project(m).update(flags=[*project(m).get("flags", []), "-mavx2"]),
            "a unit's flags": lambda m: project(m)["unit"][0].update(flags=["-mavx512f"]),
            "a kernel": lambda m: project(m)["unit"][0].update(kernels=["another"]),
            "a unit": lambda m: project(m)["unit"].append({"source": "new.c", "kernels": ["new"]}),
            "a workload's run": lambda m: first(m).update(run=[["true"]]),
            "a workload's setup": lambda m: first(m).update(setup=[["true"]]),
            "a workload dropped": lambda m: project(m)["workload"].pop(),
            "what's measured": lambda m: first(m).update(measure="rate", rate="runs a second"),
            "a check": lambda m: first(m)["check"][0].update(output=["{out}/another"]),
            "a check dropped": lambda m: first(m)["check"].pop(),
            "a known answer": lambda m: workload(m, "zlib-ng", "decompress")["check"][0].update(
                sha256="0" * 64
            ),
            "a known-answers test": lambda m: workload(m, "xxhash", "bench")["check"][1].update(
                run=[["true"]]
            ),
            "the driver's hash": lambda m: driven(m).update(driver_sha256="0" * 64),
            "how the driver is built": lambda m: driven(m)["build"][0].insert(1, "-O0"),
            "an input": lambda m: project(m).update(
                input=[{"name": "a", "url": "https://example.org/a", "sha256": "0" * 64}]
            ),
            "the corpus's flags": lambda m: m["corpus"].update(flags=[]),
            "the machine": lambda m: m["corpus"].update(machine="another"),
            "a project added": lambda m: m["corpus"]["approved"].append(other),
            "a project dropped": lambda m: m["corpus"]["approved"].pop(),
        }
        # The lock in the manifest, and one made the same way.
        for m in (MANIFEST, fixed()):
            for what, change in changes.items():
                found = kernels.problems(changed(m, change))
                self.assertTrue(
                    [line for line in found if "the fixed corpus changed" in line], f"{what}: {found}"
                )

    def test_what_isnt_approved_can_change(self) -> None:
        m = fixed()
        other = names("alternate")[0]
        self.assertEqual(kernels.problems(changed(m, lambda m: m["project"][other].update(rev="1" * 40))), [])
        # How the proposal ranks a project, and the order the approved are named in, aren't what's fixed.
        first = m["corpus"]["approved"][0]
        self.assertEqual(
            kernels.problems(changed(m, lambda m: m["project"][first].update(status="alternate"))), []
        )
        self.assertEqual(kernels.problems(changed(m, lambda m: m["corpus"]["approved"].reverse())), [])

    def test_an_amendment_records_a_change_and_a_broken_one_doesnt(self) -> None:
        m = fixed()
        name = m["corpus"]["approved"][0]
        moved = changed(m, lambda m: m["project"][name].update(rev="0" * 40))
        once = amended(m, moved)
        self.assertEqual(kernels.problems(once), [])
        again = amended(m, changed(once, lambda m: m["project"][name].update(rev="2" * 40)))
        self.assertEqual(kernels.problems(again), [])
        # An amendment that starts somewhere else, ends somewhere else, or gives no reason.
        for message, broken in {
            "starts from": amended(m, moved, **{"from": "0" * 64}),
            "the fixed corpus changed": amended(m, moved, to="0" * 64),
            "has no reason": amended(m, moved, reason=""),
            "has no on": amended(m, moved, on=""),
        }.items():
            found = kernels.problems(broken)
            self.assertTrue([line for line in found if message in line], f"{message}: {found}")
        # And one that records a change made after it doesn't cover the change.
        later = changed(once, lambda m: m["project"][name].update(rev="3" * 40))
        self.assertTrue([line for line in kernels.problems(later) if "the fixed corpus changed" in line])


class Driver(unittest.TestCase):
    """bench/kernels/libsodium: decision 7's driver, and reference.py, what it prints computed without
    libsodium, which libsodium's own test of crypto_secretstream doesn't give."""

    def test_the_reference_meets_its_documents_vectors(self) -> None:
        reference.check_vectors()

    def test_the_reference_starts_from_the_drivers_seeds_and_pattern(self) -> None:
        driver = (HERE / "libsodium" / "secretstream.c").read_text()
        computed = (HERE / "libsodium" / "reference.py").read_text()
        for shared in (
            '"ir-lean kernel corpus: key"',
            '"ir-lean kernel corpus: header"',
            "2654435761",
            "4096",
        ):
            self.assertIn(shared, driver)
            self.assertIn(shared, computed)


class Records(unittest.TestCase):
    def test_the_doc_names_every_project_with_its_commit_and_standing(self) -> None:
        rows = [line for line in DOC.read_text().splitlines() if line.startswith("| [")]
        for name, p in MANIFEST["project"].items():
            row = [line for line in rows if f"`{p['rev']}`" in line]
            self.assertEqual(
                len(row), 1, f"{name}: docs/kernels.md's table should name commit {p['rev']} once"
            )
            self.assertIn(p["repository"], row[0], name)
            self.assertIn(f"| {WORD[p['status']]}", row[0], f"{name} is {p['status']} in the manifest")

    def test_the_demand_results_are_about_the_manifests_pins_and_kernels(self) -> None:
        results = schemas.read(RESULTS, schemas.KERNELS_DEMAND)["projects"]
        with_units = {n: p for n, p in MANIFEST["project"].items() if p.get("unit")}
        self.assertEqual(sorted(results), sorted(with_units))
        for name, p in with_units.items():
            self.assertEqual(results[name]["rev"], p["rev"], name)
            self.assertEqual(results[name]["nix_hash"], p["nix_hash"], name)
            measured = {u["source"]: sorted(u["kernels"]) for u in results[name]["units"]}
            named = {u["source"]: sorted(u.get("kernels", [])) for u in p["unit"]}
            self.assertEqual(measured, named, f"{name}: run bench/kernels/demand.py run --project {name}")

    def test_the_manifests_tool_and_its_schemas_are_registered(self) -> None:
        self.assertEqual(MANIFEST["schema"], schemas.KERNELS_MANIFEST)
        self.assertIn(schemas.KERNELS_DEMAND, schemas.ALL)


class Provenance(unittest.TestCase):
    """A run of some projects keeps the others' counts, and each keeps the date, commit and clang it was
    measured with, so counts from two runs can't pass for one."""

    OLD: typing.ClassVar[dict[str, Any]] = {
        "date": "2026-11-09",
        "commit": "old",
        "clang": "clang 23.1.3",
        "projects": {
            "libwebp": {"totals": {}},
            "zlib-ng": {"totals": {}, "measured": {"date": "2026-11-10"}},
        },
    }

    def test_a_kept_project_keeps_the_record_it_was_measured_with(self) -> None:
        kept = demand.kept(self.OLD, ["libwebp", "zlib-ng", "flac"])
        self.assertEqual(
            kept["libwebp"]["measured"], {"date": "2026-11-09", "commit": "old", "clang": "clang 23.1.3"}
        )
        self.assertEqual(kept["zlib-ng"]["measured"], {"date": "2026-11-10"})
        self.assertNotIn("flac", kept)
        self.assertEqual(demand.kept(None, ["libwebp"]), {})

    def test_every_project_in_the_results_says_what_it_was_measured_with(self) -> None:
        record = schemas.read(RESULTS, schemas.KERNELS_DEMAND)
        for name, project in record["projects"].items():
            self.assertEqual(set(project.get("measured", {})), {"date", "commit", "clang"}, name)


class Demand(unittest.TestCase):
    KNOWN: typing.ClassVar[dict[str, dict[str, str]]] = {
        name: {} for name in ("llvm.umin", "llvm.memmove", "llvm.x86.avx2.psad.bw", "llvm.vector.reduce.add")
    }

    def test_an_intrinsic_is_named_without_the_types_its_overloaded_on(self) -> None:
        for callee, name in {
            "llvm.umin.i64": "llvm.umin",
            "llvm.memmove.p0.p0.i64": "llvm.memmove",
            "llvm.x86.avx2.psad.bw": "llvm.x86.avx2.psad.bw",
            "llvm.vector.reduce.add.v8i32": "llvm.vector.reduce.add",
            "llvm.unknown.thing": "llvm.unknown.thing",
        }.items():
            self.assertEqual(demand.base(callee, self.KNOWN), name)

    def test_refusals_of_one_kind_count_together(self) -> None:
        for raw, reason in {
            "metadata !tbaa on %28 = load i8, ptr %23, align 1, !tbaa !9": "metadata !tbaa",
            "intrinsic llvm.memmove.p0.p0.i64": "intrinsic llvm.memmove",
            "call to external @adler32_ssse3, which touches memory: F4": (
                "call to external @_, which touches memory: F4"
            ),
            "call to @CHUNKCOPY_SAFE, which isn't translated": "call to @_, which isn't translated",
            "instruction   %5 = load volatile i64, ptr @x, align 8": "instruction load volatile",
            "instruction %a = freeze <2 x i64> poison": "instruction freeze of a vector",
            "instruction %p = inttoptr i64 %x to ptr": "instruction inttoptr",
            'operand ptr asm sideeffect ".p2align 6", "~{dirflag},~{fpsr},~{flags}"': "inline assembly",
            'function attribute "no-signed-zeros-fp-math"="true"': (
                'function attribute "no-signed-zeros-fp-math"'
            ),
            "type <16 x ptr>": "type: a vector of pointers",
            "in a cycle with a function that has metadata !tbaa on %3 = load ptr, ptr %2": (
                "in a cycle with a function refused for: metadata !tbaa"
            ),
            "call return attribute dereferenceable_or_null(48)": (
                "call return attribute dereferenceable_or_null"
            ),
        }.items():
            self.assertEqual(demand.reason(raw, self.KNOWN), reason)

    def test_a_module_is_read_as_its_functions(self) -> None:
        module = """
define dso_local i32 @f(ptr noundef %p) #0 {
entry:
  %a = load <8 x i32>, ptr %p, align 1
  %s = tail call i32 @llvm.vector.reduce.add.v8i32(<8 x i32> %a)
  switch i32 %s, label %out [
    i32 1, label %one
  ]
one:                                              ; preds = %entry
  br label %out
out:
  ret i32 %s
}

define internal float @"g.1"(float %x) {
  ret float %x
}
declare i32 @llvm.vector.reduce.add.v8i32(<8 x i32>)
"""
        bodies = demand.functions(module)
        self.assertEqual(sorted(bodies), ["f", "g.1"])
        f = demand.describe(bodies["f"], self.KNOWN)
        self.assertEqual(
            f,
            {"instructions": 5, "vector": True, "float": False, "intrinsics": {"llvm.vector.reduce.add": 1}},
        )
        g = demand.describe(bodies["g.1"], self.KNOWN)
        self.assertEqual((g["instructions"], g["vector"], g["float"]), (1, False, True))


if __name__ == "__main__":
    unittest.main()
