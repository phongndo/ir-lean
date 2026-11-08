#!/usr/bin/env python3
"""Tests of tests/llvm_scope.py: what it reads from LLVM, and that nothing unproved can count as done.

Most of these are negative: a claim or a task that overstates what was shown has to be refused. They need
nothing but the files in the repo, so they run without LLVM.

usage: tests/llvm_scope_test.py
"""

import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

import llvm_scope as s

ANCHOR = "llvm/lib/Transforms/Scalar/Foo.cpp"
# Stands in for the independent verifiers BIND-03 is to write, which don't exist yet.
ACCEPT: dict[str, s.Verifier] = {kind: lambda *_: None for kind in s.NEEDS.values()}


SOURCE = {"cl_opts_in_anchor_files": 0, "target_dirs": []}


def inventory() -> dict[str, Any]:
    """A small inventory with one transform and one analysis, both in the O2 pipeline."""
    return {
        "pin": dict(s.PIN),
        "pipelines": {
            "opt": {
                "default<O2>": {"pipeline": "function(foo,require<bar>)"},
                "default<Os>": {"error": "gone"},
            },
            "llc": {"x86-64": {"O2": {"passes": "foo", "errors": []}}},
        },
        "items": [
            {
                "id": "pass:foo",
                "name": "foo",
                "kinds": ["transform"],
                "anchors": {ANCHOR: "a" * 64},
                "unresolved_classes": [],
                "registrations": [],
                "targets": [],
                "category": "transform",
            },
            {
                "id": "pass:bar",
                "name": "bar",
                "kinds": ["analysis"],
                "anchors": {},
                "unresolved_classes": ["BarAnalysis"],
                "registrations": [],
                "targets": [],
                "category": "analysis",
            },
        ],
    }


class Claims(unittest.TestCase):
    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.root = Path(self.dir.name) / "repo"
        self.root.mkdir()
        self.inv = inventory()

    def tearDown(self) -> None:
        self.dir.cleanup()

    def evidence(self, kind: str, name: str = "proof.lean") -> dict[str, str]:
        path = self.root / name
        path.write_text(f"-- {kind}\n")
        return {"kind": kind, "path": name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

    def claim(
        self, dim: str, status: str = "complete", kind: str | None = None, **extra: Any
    ) -> dict[str, Any]:
        kind = kind or s.NEEDS.get(dim, "tv-run")
        c: dict[str, Any] = {
            "item": "pass:foo",
            "dimension": dim,
            "contexts": "all",
            "status": status,
            "evidence": [self.evidence(kind, f"{dim}.txt")],
        }
        if dim == "code-binding":
            c["anchors"] = {ANCHOR: "a" * 64}
        c.update(extra)
        return c

    def run_claims(
        self, *claims: dict[str, Any], verifiers: dict[str, s.Verifier] = ACCEPT
    ) -> tuple[list[str], dict[str, Any]]:
        cov = {"schema": 1, "pin": s.PIN["tag"], "claims": list(claims)}
        return s.evaluate(self.inv, cov, self.root, verifiers)

    def full(self) -> list[dict[str, Any]]:
        return [self.claim("all-input"), self.claim("code-binding"), self.claim("composition")]

    def test_nothing_claimed_is_nothing_done(self) -> None:
        errors, standing = self.run_claims()
        self.assertEqual(errors, [])
        self.assertFalse(any(v["done"] for v in standing.values()))
        self.assertEqual(standing["pass:bar"]["dimensions"]["analysis-soundness"], "missing")

    def test_all_three_complete_is_done(self) -> None:
        # The positive control: without it, the refusals below could pass by refusing everything.
        errors, standing = self.run_claims(*self.full())
        self.assertEqual(errors, [])
        self.assertTrue(standing["pass:foo"]["done"])

    def test_a_status_and_hashes_alone_are_unverified(self) -> None:
        # Whoever writes the manifest writes the status and the hashes, so without a verifier nothing is done.
        errors, standing = self.run_claims(*self.full(), verifiers={})
        self.assertEqual(errors, [])
        self.assertFalse(standing["pass:foo"]["done"])
        self.assertEqual(set(standing["pass:foo"]["dimensions"].values()), {"unverified"})
        summary = s.summarize(self.inv | {"tools": {"targets_built": []}, "source": SOURCE}, standing)
        self.assertEqual((summary["verified_done"], summary["claimed_complete"]), (0, 1))

    def test_a_verifier_decides_with_the_contexts_it_runs_in(self) -> None:
        seen = []

        def refuse(claim: dict[str, Any], item: dict[str, Any], contexts: set[str], root: Path) -> str:
            seen.append(contexts)
            return "the proof doesn't cover llc:x86-64:O2"

        errors, standing = self.run_claims(*self.full(), verifiers={**ACCEPT, "composition-proof": refuse})
        self.assertTrue(any("verifier refused" in e for e in errors), errors)
        self.assertFalse(standing["pass:foo"]["done"])
        self.assertEqual(seen, [{"opt:default<O2>", "llc:x86-64:O2"}])

    def test_evidence_outside_the_repo_is_refused(self) -> None:
        outside = self.root.parent / "outside.lean"
        outside.write_text("theorem t : True := trivial\n")
        digest = hashlib.sha256(outside.read_bytes()).hexdigest()
        for path in ("../outside.lean", str(outside)):
            c = self.claim("all-input")
            c["evidence"] = [{"kind": "lean-proof", "path": path, "sha256": digest}]
            errors, _ = self.run_claims(c)
            self.assertTrue(any("isn't a file in the repo" in e for e in errors), (path, errors))

    def test_each_missing_dimension_leaves_it_unfinished(self) -> None:
        for n in range(3):
            claims = self.full()
            del claims[n]
            errors, standing = self.run_claims(*claims)
            self.assertEqual(errors, [])
            self.assertFalse(standing["pass:foo"]["done"], claims)

    def test_unfinished_statuses_never_count(self) -> None:
        for status in ("partial", "admitted", "timeout", "unsupported", "failed"):
            claims = self.full()
            claims[0]["status"] = status
            errors, standing = self.run_claims(*claims)
            self.assertEqual(errors, [], status)
            self.assertFalse(standing["pass:foo"]["done"], status)
            self.assertEqual(standing["pass:foo"]["dimensions"]["all-input"], status)

    def test_translation_validation_is_never_all_input(self) -> None:
        errors, standing = self.run_claims(self.claim("all-input", kind="tv-run"), *self.full()[1:])
        self.assertTrue(any("needs lean-proof" in e for e in errors), errors)
        errors, _ = self.run_claims(self.claim("translation-validation"))
        self.assertTrue(any("can't be complete" in e for e in errors), errors)
        errors, standing = self.run_claims(self.claim("translation-validation", status="partial"))
        self.assertEqual(errors, [])
        self.assertEqual(standing["pass:foo"]["translation_validation"], "partial")
        self.assertFalse(standing["pass:foo"]["done"])

    def test_complete_needs_evidence_that_still_matches(self) -> None:
        errors, _ = self.run_claims(self.claim("all-input", evidence=[]))
        self.assertTrue(any("no evidence" in e for e in errors), errors)
        c = self.claim("all-input")
        (self.root / c["evidence"][0]["path"]).write_text("edited\n")
        errors, _ = self.run_claims(c)
        self.assertTrue(any("changed since" in e for e in errors), errors)
        c = self.claim("all-input")
        c["evidence"][0]["path"] = "missing.lean"
        errors, _ = self.run_claims(c)
        self.assertTrue(any("isn't a file" in e for e in errors), errors)

    def test_complete_with_gaps_is_refused(self) -> None:
        errors, _ = self.run_claims(self.claim("all-input", gaps=["i1 only"]))
        self.assertTrue(any("gaps" in e for e in errors), errors)

    def test_a_stale_binding_is_refused(self) -> None:
        errors, _ = self.run_claims(self.claim("code-binding", anchors={ANCHOR: "b" * 64}))
        self.assertTrue(any("stale" in e for e in errors), errors)
        errors, _ = self.run_claims(self.claim("code-binding", anchors={}))
        self.assertTrue(any("stale" in e for e in errors), errors)

    def test_a_binding_needs_code_the_inventory_found(self) -> None:
        c = self.claim("code-binding", anchors={})
        c["item"] = "pass:bar"
        errors, _ = self.run_claims(c)
        self.assertTrue(any("couldn't find code" in e for e in errors), errors)

    def test_some_contexts_are_partial(self) -> None:
        claims = self.full()
        claims[2]["contexts"] = ["opt:default<O2>"]
        errors, standing = self.run_claims(*claims)
        self.assertEqual(errors, [])
        self.assertEqual(standing["pass:foo"]["dimensions"]["composition"], "partial")
        self.assertFalse(standing["pass:foo"]["done"])

    def test_contexts_must_be_ones_it_runs_in(self) -> None:
        errors, _ = self.run_claims(self.claim("composition", contexts=["opt:default<O3>"]))
        self.assertTrue(any("never saw" in e for e in errors), errors)
        errors, _ = self.run_claims(self.claim("composition", contexts=["llc:x86-64:O2", "registered"]))
        self.assertEqual(errors, [])

    def test_malformed_claims_are_refused(self) -> None:
        cases = [
            ({"item": "pass:nope"}, "no such pass"),
            ({"dimension": "vibes"}, "dimension must be"),
            ({"status": "done"}, "status must be"),
            ({"assumptions": [{"text": "x", "justification": " "}]}, "justification"),
            ({"evidence": [{"kind": "blog", "path": "x", "sha256": "0" * 64}]}, "evidence kind"),
            ({"proved": True}, "keys must be"),
            ({"contexts": []}, "contexts must be"),
        ]
        for extra, message in cases:
            c = self.claim("all-input")
            c.update(extra)
            errors, _ = self.run_claims(c)
            self.assertTrue(any(message in e for e in errors), (extra, errors))
        errors, _ = self.run_claims(self.claim("all-input"), self.claim("all-input"))
        self.assertTrue(any("second claim" in e for e in errors), errors)

    def test_a_manifest_for_another_pin_is_refused(self) -> None:
        errors, _ = s.evaluate(self.inv, {"schema": 1, "pin": "llvmorg-22.1.8", "claims": []}, self.root)
        self.assertTrue(any("is for" in e for e in errors), errors)


TASK = """### {id}: A task

- **Lane:** {lane}
- **Scope:** Something.
- **Depends on:** {deps}
- **Owns:** `{owns}`
- **Acceptance:** It works.
- **Trust gaps:** None.
- **Status:** {status}
- **Evidence:** {evidence}
{extra}
"""


def task(
    id: str,
    deps: str = "none",
    status: str = "not started",
    owns: str = "a.py",
    evidence: str = "None yet.",
    extra: str = "",
) -> str:
    return TASK.format(
        id=id, lane=id.split("-")[0], deps=deps, status=status, owns=owns, evidence=evidence, extra=extra
    )


class Tasks(unittest.TestCase):
    def check(self, *tasks: str) -> list[str]:
        return s.check_tasks("# Tasks\n\n" + "\n".join(tasks), s.ROOT)

    def test_a_sound_list_passes(self) -> None:
        errors = self.check(
            task("INV-01", status="complete", evidence="`tests/llvm_scope.py`"),
            task("SEM-01", deps="INV-01", status="in progress", owns="b.py"),
            task("NEG-01", deps="SEM-01", owns="b.py"),
        )
        self.assertEqual(errors, [])

    def test_complete_needs_evidence_in_the_repo(self) -> None:
        for evidence in (
            "Trust me.",
            "`no/such/file.py`",
            "`deadbee`",
            "`/etc/hosts`",
            "`../README.md`",
            "`tests`",
        ):
            errors = self.check(task("INV-01", status="complete", evidence=evidence))
            self.assertTrue(any("complete needs evidence" in e for e in errors), errors)

    def test_a_commit_in_the_repo_is_evidence(self) -> None:
        head = subprocess.run(
            ["git", "-C", str(s.ROOT), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
        )
        errors = self.check(task("INV-01", status="complete", evidence=f"`{head.stdout.strip()[:12]}`"))
        self.assertEqual(errors, [])

    def test_complete_needs_its_dependencies_complete(self) -> None:
        errors = self.check(
            task("INV-01"), task("SEM-01", deps="INV-01", status="complete", evidence="`tests/llvm_scope.py`")
        )
        self.assertTrue(any("complete while" in e for e in errors), errors)

    def test_starting_early_needs_a_waiver(self) -> None:
        errors = self.check(task("INV-01"), task("SEM-01", deps="INV-01", status="in progress"))
        self.assertTrue(any("gate waiver" in e for e in errors), errors)
        errors = self.check(
            task("INV-01"),
            task(
                "SEM-01",
                deps="INV-01",
                status="in progress",
                extra="- **Gate waiver:** Only drafts an interface.",
            ),
        )
        self.assertEqual(errors, [])

    def test_loops_and_unknown_dependencies_are_refused(self) -> None:
        errors = self.check(task("INV-01", deps="SEM-01"), task("SEM-01", deps="INV-01"))
        self.assertTrue(any("dependency loop" in e for e in errors), errors)
        errors = self.check(task("INV-01", deps="CG-99"))
        self.assertTrue(any("isn't a task" in e for e in errors), errors)

    def test_two_active_tasks_cannot_own_one_file(self) -> None:
        errors = self.check(task("INV-01", status="in progress"), task("SEM-01", status="in review"))
        self.assertTrue(any("owned by" in e for e in errors), errors)

    def test_fields_lanes_and_statuses_are_checked(self) -> None:
        errors = self.check(task("INV-01").replace("- **Acceptance:** It works.\n", ""))
        self.assertTrue(any("no Acceptance" in e for e in errors), errors)
        errors = self.check(task("XYZ-01"))
        self.assertTrue(any("lane" in e for e in errors), errors)
        errors = self.check(task("INV-01", status="mostly done"))
        self.assertTrue(any("status" in e for e in errors), errors)
        errors = self.check(task("INV-01"), task("INV-01"))
        self.assertTrue(any("defined twice" in e for e in errors), errors)


class Reading(unittest.TestCase):
    def test_registry_entries(self) -> None:
        text = (
            "#ifndef FUNCTION_PASS\n#define FUNCTION_PASS(NAME, CREATE_PASS)\n#endif\n"
            'FUNCTION_PASS("gvn-sink", GVNSinkPass())\n'
            "#define MODULE_ALIAS_ANALYSIS(NAME, CREATE_PASS)  \\\n  MODULE_ANALYSIS(NAME, CREATE_PASS)\n"
            'FUNCTION_ANALYSIS("target-ir", TM ? TM->getTargetIRAnalysis() : TargetIRAnalysis())\n'
            "FUNCTION_PASS_WITH_PARAMS(\n"
            '    "gvn", "GVNPass", [](GVNOptions Opts) { return GVNPass(Opts); },\n'
            '    parseGVNOptions, "no-pre;"\n    "pre")\n'
            'DUMMY_MACHINE_FUNCTION_PASS("regalloc", RegAllocPass)\n'
        )
        got = dict(s.registry_entries("llvm/lib/Passes/PassRegistry.def", text))
        self.assertEqual(sorted(got), ["gvn", "gvn-sink", "regalloc", "target-ir"])
        self.assertEqual(got["gvn"]["params"], "no-pre;pre")
        self.assertEqual(got["gvn"]["class"], "GVNPass")
        self.assertEqual(got["gvn-sink"]["class"], "GVNSinkPass")
        self.assertEqual(got["target-ir"]["kind"], "analysis")
        self.assertIn("TargetIRAnalysis", got["target-ir"]["creates"])
        self.assertEqual(got["regalloc"]["kind"], "dummy")
        self.assertEqual(got["gvn-sink"]["site"], "llvm/lib/Passes/PassRegistry.def:4")

    def test_legacy_entries(self) -> None:
        text = (
            '#define DEBUG_TYPE "machine-cse"\n'
            'static const char PassName[] = "x86-thing";\n'
            'INITIALIZE_PASS_BEGIN(MachineCSELegacy, DEBUG_TYPE, "Machine CSE", false, false)\n'
            'INITIALIZE_PASS(X86Thing, PassName, "X86 thing", false, true)\n'
            'INITIALIZE_PASS(Lost, SOME_MACRO, "?", false, false)\n'
        )
        got = s.legacy_entries("llvm/lib/Target/X86/X.cpp", text)
        self.assertEqual(
            [n for n, _ in got], ["machine-cse", "x86-thing", "?SOME_MACRO@llvm/lib/Target/X86/X.cpp"]
        )
        self.assertEqual(got[1][1]["kind"], "analysis")
        self.assertEqual(got[0][1]["class"], "MachineCSELegacy")
        self.assertEqual(s.target_of(got[1][1]["site"]), "X86")

    def test_register_pass(self) -> None:
        # The other way into the legacy registry, as llvm/lib/Transforms/Utils/Debugify.cpp uses it here.
        text = (
            'static RegisterPass<DebugifyModulePass> DM("debugify",\n'
            '                                          "Attach debug info to everything");\n'
            "static RegisterPass<CheckDebugifyModulePass>\n"
            '    CDM("check-debugify", "Check debug info from -debugify");\n'
            'static RegisterPass<llvm::Probe> P(PassArg, "Probe", false, true);\n'
            'INITIALIZE_PASS_WITH_OPTIONS(Opts, "with-options", "Options", false, false)\n'
            "template <typename T> RegisterPass(StringRef PassArg, StringRef Name);\n"
        )
        got = s.legacy_entries("llvm/lib/Transforms/Utils/D.cpp", '#define PassArg "probe"\n' + text)
        self.assertEqual([n for n, _ in got], ["debugify", "check-debugify", "probe", "with-options"])
        self.assertEqual([e["macro"] for _, e in got], ["RegisterPass"] * 3 + ["INITIALIZE_PASS"])
        self.assertEqual(got[1][1]["class"], "CheckDebugifyModulePass")
        self.assertEqual([e["kind"] for _, e in got], ["transform", "transform", "analysis", "transform"])
        self.assertEqual(got[1][1]["site"], "llvm/lib/Transforms/Utils/D.cpp:4")

    def test_selector_entries(self) -> None:
        # Registries an option picks from by name. Their names clash with passes and with each other.
        options = s.selector_options(
            {
                "a.cpp": "static cl::opt<RegisterRegAlloc::FunctionPassCtor, false,\n"
                "               RegisterPassParser<RegisterRegAlloc>>\n"
                '    RegAlloc("regalloc", cl::Hidden, cl::init(&useDefault));\n',
                "b.cpp": "cl::opt<Ctor, false, RegisterPassParser<MachineSchedRegistry>>\n"
                'MachineSchedOpt("misched", cl::Hidden);\n',
            }
        )
        self.assertEqual(options, {"RegisterRegAlloc": "regalloc", "MachineSchedRegistry": "misched"})
        text = (
            "  RegisterRegAlloc(const char *N, const char *D, FunctionPassCtor C)\n"
            'static RegisterRegAlloc greedyRegAlloc("greedy", "greedy register allocator",\n'
            "                                       createGreedyRegisterAllocator);\n"
            "static MachineSchedRegistry\n"
            '    DefaultSchedRegistry("default", "Use the target\'s default scheduler choice.",\n'
            "                         useDefaultMachineSched);\n"
        )
        got = s.selector_entries("llvm/lib/CodeGen/X.cpp", text, options)
        self.assertEqual(sorted(n for n, _ in got), ["misched=default", "regalloc=greedy"])
        self.assertEqual({e["registry"] for _, e in got}, {"selector"})
        help_text = (
            "  --regalloc=<value>   - Register allocator to use\n"
            "      =basic           -   basic register allocator\n"
            "      =greedy          -   greedy register allocator\n"
            "  --other              - Something else\n"
            "      =stray           -   not an entry of regalloc\n"
        )
        self.assertEqual(dict(s.selector_values(help_text)), {"regalloc": {"basic", "greedy"}})

    def test_pipeline_leaves(self) -> None:
        text = (
            "verify,function<eager-inv>(sroa<modify-cfg>,early-cse<>),cgscc(devirt<4>(inline,function("
            "loop-mssa(licm<allowspeculation>),require<memoryssa>))),invalidate<aa>"
        )
        leaves, adaptors, analyses = s.pipeline_leaves(text)
        self.assertEqual(leaves, ["verify", "sroa", "early-cse", "inline", "licm"])
        self.assertEqual(adaptors, ["function", "cgscc", "devirt", "function", "loop-mssa"])
        self.assertEqual(analyses, ["memoryssa", "aa"])


class Repo(unittest.TestCase):
    """The files in the repo hold together, without LLVM."""

    def test_the_manifest_and_tasks_hold(self) -> None:
        inv = s.load(s.INVENTORY)
        errors, standing = s.evaluate(inv, s.load(s.COVERAGE))
        self.assertEqual(errors, [])
        self.assertEqual(s.check_tasks(s.TASKS.read_text()), [])
        self.assertEqual(inv["pin"], s.PIN)
        ids = [i["id"] for i in inv["items"]]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(set(ids), set(standing))
        # Each way the pinned source registers a pass is in the inventory.
        macros = {r["macro"] for i in inv["items"] for r in i["registrations"]}
        self.assertLessEqual(
            {"INITIALIZE_PASS", "RegisterPass", "RegisterRegAlloc", "MachineSchedRegistry"}, macros
        )

    def test_the_doc_states_the_measured_scope(self) -> None:
        inv = s.load(s.INVENTORY)
        summary = s.summarize(inv, s.evaluate(inv, s.load(s.COVERAGE))[1])
        doc = s.TASKS.read_text()
        self.assertEqual(s.check_scope(doc, summary), [])
        for number, what in ((summary["registered_names"], "names"), (summary["verified_done"], "done")):
            self.assertRegex(doc, rf"\b{number}\b", what)
        line = s.scope_line(summary)
        for wrong in (doc.replace(line, ""), doc.replace(line, "<!-- scope: {} -->"), doc + line):
            self.assertTrue(s.check_scope(wrong, summary))

    def test_every_lane_the_plan_needs_has_a_task(self) -> None:
        lanes = {t.split("-")[0] for t in s.parse_tasks(s.TASKS.read_text())}
        self.assertEqual(lanes, set(s.LANES))


if __name__ == "__main__":
    if "--scope-line" in sys.argv:
        inv = s.load(s.INVENTORY)
        print(s.scope_line(s.summarize(inv, s.evaluate(inv, s.load(s.COVERAGE))[1])))
        sys.exit(0)
    unittest.main()
