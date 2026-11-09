#!/usr/bin/env python3
"""Checks that tools/binding.py binds a certificate to what it's about, and refuses evidence that doesn't
match.

One real rewrite, `instcombine` folding `add i8 %x, 0` in tests/binding/add_zero.ll, with a certificate that
the functions ir-lean generates before and after are equal. Its bundle has to come back `bound`. Then each
case breaks one thing, as someone handing over wrong evidence would, and the verdict has to be the status and
reason given, never `bound`: a theorem of another type, a changed file, a changed configuration, a manifest
from another toolchain, a cache entry that isn't for this evidence, and claims nothing here can check. Two
more have to be bound: `loop-deletion` deleting a loop under `mustprogress`, which only the promise makes
right, and a module whose intrinsic declaration carries `willreturn`, which this tool once refused for the
whole module. Four `freeze` runs have to be bound too, since F3 made `freeze` of poison a value the run
chooses.

It runs one process at a time, each capped by tools/binding.py, in build/binding/tests, and needs
`nix develop`, build/ir-lean and `lake build`.

A case belongs to one of `--shard I/N`'s shards by a hash of its name, so CI can run the cases in N jobs, and
a case added later lands in one of them without being listed anywhere. A case run behind `args.only` alone,
not `runs()`, runs in every shard: twice, not never.

usage: tests/binding.py [--keep] [--only NAME ...] [--shard I/N]
"""

import argparse
import base64
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any
from zlib import crc32

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "binding"
WORK = ROOT / "build" / "binding" / "tests"
TOOL = [sys.executable, str(ROOT / "tools" / "binding.py")]

HEADER = "import Fx.Src\nimport Fx.Tgt\nopen IRLean\n\n"
GOOD = (HERE / "AddZero.lean").read_text()
# The claim tools/binding_check.lean builds for add_zero.ll, as a certificate states it.
CLAIM = (
    "Fx.Src.f = Fx.Tgt.f ∧\n"
    "    ∀ (x : IRLean.Val 8) (s : IRLean.ModelStop), Fx.Src.f x ≠ some (.error (.model s))"
)
assert CLAIM in GOOD
# The good certificate's theorem as `Fx.good`, for certificates that state something else and still compile.
GOOD_LEMMA = GOOD.split("open IRLean\n", 1)[1].replace("theorem Fx.cert", "theorem Fx.good")
# The same rewrite, with a certificate of the refinement claim.
REFINES = (HERE / "AddZeroRefines.lean").read_text()
assert "theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f :=" in REFINES
# loop-deletion on loop_deleted.ll: the target refines the source because the source promised to progress.
LOOP_DELETED = (HERE / "LoopDeletedRefines.lean").read_text()
assert "theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f :=" in LOOP_DELETED

# `freeze` in the model, F3: four real instcombine runs, each bound as a refinement. On freeze.ll it keeps a
# `freeze` of a shift that's poison for x of 8 or more. Until F3 the model stopped there on both sides, so the
# two were equal in the model and equality was all a certificate could prove, which isn't the claim. The other
# three are `freeze (freeze y)` to `freeze y`, a `freeze` of a `noundef` argument dropped, and a frozen poison
# made 0. In the last two only the source makes a choice, so the claim lifts the target with
# `IRLean.Outcomes.det`.
FREEZE = (HERE / "FreezeRefines.lean").read_text()
FREEZE_FREEZE = (HERE / "FreezeFreezeRefines.lean").read_text()
FREEZE_NOUNDEF = (HERE / "FreezeNoundefRefines.lean").read_text()
FREEZE_POISON = (HERE / "FreezePoisonRefines.lean").read_text()
for certificate in (FREEZE, FREEZE_FREEZE):
    assert "theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f :=" in certificate
for certificate in (FREEZE_NOUNDEF, FREEZE_POISON):
    assert (
        "theorem Fx.cert : IRLean.Refines Fx.Src.f fun x => IRLean.Outcomes.det (Fx.Tgt.f x) :="
        in certificate
    )

# A certificate that takes longer than the limit tests/binding.py gives it.
SLOW = GOOD + "\nexample : True := by\n  sleep 120000\n  trivial\n"
# One whose code takes more memory than the limit tests/binding.py gives it.
GREEDY = GOOD + "\n#eval (Array.replicate 400000000 (7 : UInt64)).size\n"


# A false theorem the kernel never saw, as tests/proofs.sh and tests/verify.py make one. Its type is the right
# claim, and it rests on no axiom, so only leanchecker's replay can stop it.
SKIPPED = (
    "import Fx.Src\nimport Fx.Tgt\nimport Lean\nopen IRLean Lean Elab Command\n\n"
    "set_option debug.skipKernelTC true in\n"
    "run_cmd liftCoreM <| addDecl <| .thmDecl {\n"
    "  name := `oops, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n\n"
    f"theorem Fx.cert : {CLAIM} := oops.elim\n"
)


# A certificate whose code, run while it compiles, rewrites the generated target it's checked against, found
# through LEAN_PATH. Its theorem is about the module as it was compiled, so only rehashing catches it.
REWRITES = GOOD + (
    "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/Fx/Tgt.lean") "-- rewritten\\n"\n'
)


# A certificate whose code adds a module where Lean looks first, named like one every certificate imports.
ADDS_MODULE = GOOD + (
    "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.head!\n'
    '  IO.FS.writeFile (dir ++ "/IRLean.olean") ""\n'
)
# One whose code adds a companion file Lean reads with a module to IRLean's library, through the run's link.
ADDS_COMPANION = GOOD + (
    "\nopen Lean in\n#eval show IO Unit from do\n"
    '  let dir := ((← IO.getEnv "LEAN_PATH").getD "").splitOn ":" |>.getLast!\n'
    '  IO.FS.writeFile (dir ++ "/IRLean/Basic.ir") ""\n'
)
# One whose code leaves a process running after it compiles.
LEAVES_PROCESS = GOOD + (
    '\n#eval show IO Unit from do\n  let _ ← IO.Process.spawn { cmd := "sleep", args := #["313.7"] }\n'
)


# The pinned llvm-project's NAR hash, as `nix-store --query --hash` prints it, in Nix's base-32.
PINNED_NIX32 = "1pnjmz111lj6xxv41s14s7ifj0w7z41j3mdj872gn2hvh6ymivpr"


def forged_store(t: Path, path: Path) -> dict[str, str]:
    """The environment of a user whose Nix configuration names a binary cache of its own, with a record that
    says `path` has the pinned llvm-project's NAR hash, as a certificate's code could leave for later runs."""
    cache = t / "forged-cache"
    (cache / "nar").mkdir(parents=True, exist_ok=True)
    (cache / "nix-cache-info").write_text("StoreDir: /nix/store\nWantMassQuery: 0\nPriority: 50\n")
    (cache / f"{path.name.split('-', 1)[0]}.narinfo").write_text(
        f"StorePath: {path}\nURL: nar/x.nar\nCompression: none\nNarHash: sha256:{PINNED_NIX32}\n"
        "NarSize: 1\nReferences: \n"
    )
    conf = t / "forged-nix.conf"
    conf.write_text(f"store = file://{cache}\n")
    return {"NIX_USER_CONF_FILES": str(conf), "NIX_REMOTE": f"file://{cache}"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def record(
    name: str,
    certificate: str,
    kind: str = "ir_instance_equivalence",
    input_ll: str = "add_zero.ll",
    passes: str = "instcombine",
) -> Path:
    """A fresh bundle for an input in tests/binding with this certificate, as `record` writes it."""
    out = WORK / name
    shutil.rmtree(out, ignore_errors=True)
    cert = WORK / f"{name}.lean"
    cert.write_text(certificate)
    r = subprocess.run(
        [
            *TOOL,
            "record",
            "--input",
            str(HERE / input_ll),
            "--passes",
            passes,
            "--mtriple",
            "x86_64-unknown-linux-gnu",
            "--function",
            "f",
            "--certificate",
            str(cert),
            "--theorem",
            "Fx.cert",
            "--namespace",
            "Fx",
            "--kind",
            kind,
            "--out",
            str(out),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    if r.returncode != 0:
        sys.exit(f"record {name} failed: {r.stdout}{r.stderr}")
    return out / "manifest.json"


def verify(manifest: Path, *extra: str, env: dict[str, str] | None = None) -> dict:
    r = subprocess.run(
        [*TOOL, "verify", str(manifest), *extra],
        capture_output=True,
        text=True,
        check=False,
        env={**os.environ, **(env or {})},
    )
    try:
        verdict = json.loads(r.stdout)
    except ValueError:
        sys.exit(f"verify gave no JSON for {manifest}: {r.stdout[-2000:]}{r.stderr[-2000:]}")
    if verdict.get("exit_code") != r.returncode:
        sys.exit(f"exit code {r.returncode} isn't the verdict's {verdict.get('exit_code')}")
    return verdict


def edit_manifest(manifest: Path, change: Callable[[dict], None]) -> Path:
    m = json.loads(manifest.read_text())
    change(m)
    manifest.write_text(json.dumps(m, indent=2, sort_keys=True))
    return manifest


def replace_artifact(manifest: Path, role: str, text: str, rehash: bool) -> Path:
    """Overwrites an artifact. With `rehash`, the manifest is updated to match, so only a replay can tell."""
    m = json.loads(manifest.read_text())
    path = manifest.parent / m["artifacts"][role]["path"]
    path.write_text(text)
    if rehash:
        m["artifacts"][role]["sha256"] = sha(path.read_bytes())
        manifest.write_text(json.dumps(m, indent=2, sort_keys=True))
    return manifest


def good(name: str) -> Path:
    """A copy of the good bundle, recorded once."""
    src = WORK / "good"
    if not (src / "manifest.json").exists():
        record("good", GOOD)
    out = WORK / name
    shutil.rmtree(out, ignore_errors=True)
    shutil.copytree(src, out)
    return out / "manifest.json"


def wrong_type(statement: str, proof: str, prelude: str = "") -> Callable[[str], Path]:
    return lambda name: record(
        name, f"{HEADER}{GOOD_LEMMA}\n{prelude}theorem Fx.cert : {statement} :=\n  {proof}\n"
    )


# Each case: a name, how to make its bundle, extra verify arguments, and the (status, reason) it has to give.
CASES: list[tuple[str, Callable[[str], Path], list[str], tuple[str, str]]] = [
    ("bound", good, [], ("bound", "replayed")),
    # Wrong theorem types. Each compiles, so only the type check can stop it.
    (
        "swapped",
        wrong_type(
            CLAIM.replace("Fx.Src.f = Fx.Tgt.f", "Fx.Tgt.f = Fx.Src.f"), "⟨Fx.good.1.symm, Fx.good.2⟩"
        ),
        [],
        ("refused", "claim_type_mismatch"),
    ),
    # Equality alone, the claim this tool asked for before the freeze attack.
    ("equality_only", wrong_type("Fx.Src.f = Fx.Tgt.f", "Fx.good.1"), [], ("refused", "claim_type_mismatch")),
    (
        "stops_on_target",
        wrong_type(
            CLAIM.replace("Fx.Src.f x ≠", "Fx.Tgt.f x ≠"),
            "by refine ⟨Fx.good.1, ?_⟩; rw [← Fx.good.1]; exact Fx.good.2",
        ),
        [],
        ("refused", "claim_type_mismatch"),
    ),
    ("trivial", wrong_type("Fx.Src.f = Fx.Src.f", "rfl"), [], ("refused", "claim_type_mismatch")),
    (
        "no_poison",
        wrong_type(
            "∀ x : BitVec 8, Fx.Src.f (some x) = Fx.Tgt.f (some x)", "fun x => congrFun Fx.good.1 (some x)"
        ),
        [],
        ("refused", "claim_type_mismatch"),
    ),
    (
        "own_definition",
        wrong_type(
            "same Fx.Src.f Fx.Tgt.f",
            "trivial",
            prelude="def same (a b : Val 8 → Outcome (Val 8)) : Prop := True\n\n",
        ),
        [],
        ("refused", "foreign_constant"),
    ),
    # `freeze` in the model: each run's frozen poison is a value it chooses, so these refine.
    (
        "freeze_kept",
        lambda n: record(n, FREEZE, kind="ir_instance_refinement", input_ll="freeze.ll"),
        [],
        ("bound", "replayed"),
    ),
    (
        "freeze_of_freeze",
        lambda n: record(n, FREEZE_FREEZE, kind="ir_instance_refinement", input_ll="freeze_freeze.ll"),
        [],
        ("bound", "replayed"),
    ),
    (
        "freeze_noundef_dropped",
        lambda n: record(n, FREEZE_NOUNDEF, kind="ir_instance_refinement", input_ll="freeze_noundef.ll"),
        [],
        ("bound", "replayed"),
    ),
    (
        "freeze_poison_replaced",
        lambda n: record(n, FREEZE_POISON, kind="ir_instance_refinement", input_ll="freeze_poison.ll"),
        [],
        ("bound", "replayed"),
    ),
    (
        "not_a_theorem",
        lambda n: edit_manifest(
            record(n, GOOD + "\ndef Fx.notThm : Nat := 1\n"), lambda m: m["claim"].update(theorem="Fx.notThm")
        ),
        [],
        ("refused", "not_a_theorem"),
    ),
    ("kernel_skipped", lambda n: record(n, SKIPPED), [], ("refused", "kernel_replay_failed")),
    ("rewrites_generated", lambda n: record(n, REWRITES), [], ("refused", "artifacts_modified")),
    ("adds_module", lambda n: record(n, ADDS_MODULE), [], ("refused", "artifacts_modified")),
    (
        "imports_lake",
        lambda n: record(n, GOOD.replace("import Fx.Tgt\n", "import Fx.Tgt\nimport Lake\n")),
        [],
        ("refused", "certificate_imports_disallowed"),
    ),
    (
        "does_not_compile",
        lambda n: record(n, GOOD + "\ntheorem broken : 1 = 2 := rfl\n"),
        [],
        ("refused", "certificate_compile_failed"),
    ),
    (
        "other_theorem",
        lambda n: edit_manifest(good(n), lambda m: m["claim"].update(theorem="Fx.other")),
        [],
        ("refused", "theorem_not_found"),
    ),
    ("sorry", wrong_type(CLAIM, "sorry"), [], ("refused", "axiom_policy_failed")),
    # What the model can't judge.
    (
        "memory",
        lambda n: record(n, GOOD, input_ll="memory.ll"),
        [],
        ("unsupported", "memory_unsupported"),
    ),
    (
        "emitter_refuses",
        lambda n: record(n, GOOD, input_ll="float.ll"),
        [],
        ("unsupported", "function_unsupported"),
    ),
    (
        "maybe_undef",
        lambda n: record(n, GOOD, input_ll="maybe_undef.ll"),
        [],
        ("unsupported", "undef_argument"),
    ),
    (
        "named_noundef",
        lambda n: record(n, GOOD, input_ll="named_noundef.ll"),
        [],
        ("unsupported", "undef_argument"),
    ),
    # Promises to progress and to return are checked by the model, not refused: a loop deleted under one is
    # bound, and one on an intrinsic's declaration doesn't stand in the way of a function that makes none.
    (
        "promise_checked",
        lambda n: record(
            n, LOOP_DELETED, kind="ir_instance_refinement", input_ll="loop_deleted.ll", passes="loop-deletion"
        ),
        [],
        ("bound", "replayed"),
    ),
    ("intrinsic_declared", lambda n: record(n, GOOD, input_ll="intrinsic.ll"), [], ("bound", "replayed")),
    # Limits make a verdict unknown, never bound or refused.
    ("time_limit", lambda n: record(n, SLOW), ["--timeout", "20"], ("unknown", "time_limit")),
    ("memory_limit", lambda n: record(n, GREEDY), ["--memory", "1500"], ("unknown", "resource_limit")),
    # The refinement claim: bound for a certificate stating IRLean.Refines, and refused for one stating
    # equivalence instead, since the checker compares the whole type.
    (
        "refinement_bound",
        lambda n: record(n, REFINES, kind="ir_instance_refinement"),
        [],
        ("bound", "replayed"),
    ),
    (
        "refinement_from_equivalence",
        lambda n: record(n, GOOD, kind="ir_instance_refinement"),
        [],
        ("refused", "claim_type_mismatch"),
    ),
    # Claims no tool here can check, whatever the evidence.
    (
        "pass_implementation",
        lambda n: edit_manifest(good(n), lambda m: m["claim"].update(kind="pass_implementation")),
        [],
        ("unsupported", "claim_kind_unverifiable"),
    ),
    (
        "rewrite_all_inputs",
        lambda n: edit_manifest(good(n), lambda m: m["claim"].update(kind="rewrite_all_inputs")),
        [],
        ("unsupported", "claim_kind_unverifiable"),
    ),
    # Changed artifacts.
    (
        "tgt_ir_edited",
        lambda n: replace_artifact(good(n), "tgt_ir", "define i8 @f(i8 %x) {\n  ret i8 0\n}\n", False),
        [],
        ("refused", "artifact_hash_mismatch"),
    ),
    (
        "tgt_ir_swapped",
        lambda n: replace_artifact(good(n), "tgt_ir", (WORK / "good" / "src.ll").read_text(), True),
        [],
        ("refused", "transform_replay_mismatch"),
    ),
    (
        "tgt_lean_edited",
        lambda n: replace_artifact(
            good(n),
            "tgt_lean",
            (WORK / "good" / "Tgt.lean").read_text().replace("ret x", "ret (some 0#8)"),
            True,
        ),
        [],
        ("refused", "translation_replay_mismatch"),
    ),
    (
        "certificate_edited",
        lambda n: replace_artifact(good(n), "certificate", GOOD + "\n-- edited\n", False),
        [],
        ("refused", "artifact_hash_mismatch"),
    ),
    (
        "extra_field",
        lambda n: edit_manifest(good(n), lambda m: m["claim"].update(note="trust me")),
        [],
        ("refused", "manifest_invalid"),
    ),
    (
        "path_outside",
        lambda n: edit_manifest(good(n), lambda m: m["artifacts"]["input"].update(path="../good/input.ll")),
        [],
        ("refused", "manifest_invalid"),
    ),
    # Changed configuration.
    (
        "other_passes",
        lambda n: edit_manifest(good(n), lambda m: m["transform"].update(passes="verify")),
        [],
        ("refused", "transform_replay_mismatch"),
    ),
    (
        "other_mtriple",
        lambda n: edit_manifest(
            good(n), lambda m: m["transform"].update(mtriple="aarch64-unknown-linux-gnu")
        ),
        [],
        ("refused", "config_mismatch"),
    ),
    (
        "other_datalayout",
        lambda n: edit_manifest(good(n), lambda m: m["target"].update(datalayout="E-p:32:32")),
        [],
        ("refused", "config_mismatch"),
    ),
    (
        "other_llvm",
        lambda n: edit_manifest(good(n), lambda m: m["llvm"].update(commit="0" * 40)),
        [],
        ("refused", "llvm_pin_mismatch"),
    ),
    (
        "stale_emitter",
        lambda n: edit_manifest(good(n), lambda m: m["toolchain"].update(ir_lean_sha256="0" * 64)),
        [],
        ("refused", "toolchain_mismatch"),
    ),
    (
        "stale_checker",
        lambda n: edit_manifest(good(n), lambda m: m["toolchain"].update(binding_check_sha256="0" * 64)),
        [],
        ("refused", "toolchain_mismatch"),
    ),
    # tools/irlean decides the verdict with tools/binding.py, so a bundle recorded with another one is stale.
    (
        "stale_library",
        lambda n: edit_manifest(good(n), lambda m: m["toolchain"].update(irlean_py_sha256="0" * 64)),
        [],
        ("refused", "toolchain_mismatch"),
    ),
]


def cache_cases(failures: list[str]) -> int:
    """A cache entry counts only for exactly the evidence and toolchain it was written for."""
    cache = WORK / "cache"
    shutil.rmtree(cache, ignore_errors=True)
    ran = 0

    def expect(name: str, verdict: dict, status: str, reason: str | None, cached: str) -> None:
        nonlocal ran
        ran += 1
        got = (verdict.get("status"), verdict.get("reason"), verdict.get("cache"))
        if got[0] != status or (reason is not None and got[1] != reason) or got[2] != cached:
            failures.append(
                f"{name}: expected {status} {reason} cache {cached}, got {got}: {verdict.get('detail')}"
            )
        else:
            print(f"ok    {name}: {got[0]} {got[1]} cache {got[2]}")

    manifest = good("cache_good")
    expect("cache_first", verify(manifest, "--cache", str(cache)), "bound", "replayed", "miss")
    expect("cache_second", verify(manifest, "--cache", str(cache)), "bound", "replayed", "hit")
    # The certificate changes and the manifest is updated to match: a new key, so the bound entry isn't
    # reused.
    bad = replace_artifact(
        good("cache_changed"), "certificate", f"{HEADER}theorem Fx.cert : Fx.Src.f = Fx.Src.f := rfl\n", True
    )
    expect(
        "cache_changed_certificate",
        verify(bad, "--cache", str(cache)),
        "refused",
        "claim_type_mismatch",
        "miss",
    )
    # An entry at the bad bundle's key that was written for other evidence, or by another toolchain, is stale.
    key = verify(bad)["key"]
    entry = json.loads((cache / f"{verify(manifest)['key']}.json").read_text())
    (cache / f"{key}.json").write_text(json.dumps(entry))
    expect(
        "cache_other_manifest",
        verify(bad, "--cache", str(cache)),
        "refused",
        "claim_type_mismatch",
        "stale_ignored",
    )
    m = json.loads(bad.read_text())
    entry.update(
        key=key,
        manifest_sha256=sha(
            json.dumps(m, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
        ),
    )
    entry["toolchain"] = {**entry["toolchain"], "ir_lean_sha256": "0" * 64}
    (cache / f"{key}.json").write_text(json.dumps(entry))
    expect(
        "cache_other_toolchain",
        verify(bad, "--cache", str(cache)),
        "refused",
        "claim_type_mismatch",
        "stale_ignored",
    )
    # Checks before the cache still run on a hit: a changed file is refused even with a bound entry for its
    # key.
    edited = replace_artifact(good("cache_edited"), "certificate", GOOD + "\n-- edited\n", False)
    expect(
        "cache_edited_file",
        verify(edited, "--cache", str(cache)),
        "refused",
        "artifact_hash_mismatch",
        "miss",
    )
    return ran


def hash_cases(failures: list[str]) -> int:
    """tree_hash, on small trees and no Lean: a library hashes the same wherever it is, and a link out of
    what's hashed is an error, since a certificate's code could change what it leads to and nothing would see
    it."""
    # tools/ isn't a package, and tests/binding/ is named like the module, so it's loaded by path.
    spec = importlib.util.spec_from_file_location("binding_tool", ROOT / "tools" / "binding.py")
    assert spec is not None and spec.loader is not None
    binding = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(binding)

    t = WORK / "trees"
    for place in ("a", "b"):
        (t / place / "IRLean").mkdir(parents=True)
        (t / place / "IRLean" / "Basic.olean").write_bytes(b"module")
        (t / place / "IRLean" / "Same.olean").symlink_to("Basic.olean")
    ran = 1
    if binding.tree_hash(t / "a", t / "a" / "IRLean") != binding.tree_hash(t / "b", t / "b" / "IRLean"):
        failures.append("relocated_library: the same library hashes differently in another place")
    else:
        print("ok    relocated_library: the same hash")
    (t / "other").mkdir()
    (t / "other" / "Basic.olean").write_bytes(b"module")
    (t / "c").mkdir()
    (t / "c" / "IRLean").symlink_to(t / "other")
    (t / "d" / "IRLean" / "Sub").mkdir(parents=True)
    (t / "d" / "IRLean" / "Sub" / "Basic.olean").write_bytes(b"module")
    (t / "d" / "IRLean" / "Dir").symlink_to("Sub")
    (t / "e" / "IRLean").mkdir(parents=True)
    (t / "e" / "IRLean" / "Basic.olean").write_bytes(b"module")
    (t / "e" / "hop").symlink_to(t / "e" / "IRLean" / "Basic.olean")
    (t / "e" / "IRLean" / "Hop.olean").symlink_to("../hop")
    (t / "a" / "IRLean" / "Out.olean").symlink_to(t / "other" / "Basic.olean")
    # Sol's: the link names a tracked file once `hop/..` is folded away, and hop leads somewhere else.
    (t / "f" / "IRLean").mkdir(parents=True)
    (t / "f" / "IRLean" / "Basic.olean").write_bytes(b"module")
    (t / "f" / "outside" / "Deep").mkdir(parents=True)
    (t / "f" / "outside" / "IRLean").mkdir()
    (t / "f" / "outside" / "IRLean" / "Basic.olean").write_bytes(b"other")
    (t / "f" / "hop").symlink_to(t / "f" / "outside" / "Deep")
    (t / "f" / "IRLean" / "Hop.olean").symlink_to("../hop/../IRLean/Basic.olean")
    # Each leads where nothing is hashed or stamped: out, a root that's a link, a link to a directory, which
    # would make `..` in another link mean something else, and a link out and back in.
    for name, place in [
        ("link_out", "a"),
        ("root_link", "c"),
        ("directory_link", "d"),
        ("hop_out", "e"),
        ("dotdot_through_link", "f"),
    ]:
        ran += 1
        try:
            binding.tree_hash(t / place, t / place / "IRLean")
            failures.append(f"{name}: hashed")
        except binding.Verdict as v:
            if (v.status, v.reason) != ("error", "toolchain_untrusted_link"):
                failures.append(f"{name}: expected error toolchain_untrusted_link, got {v.status} {v.reason}")
            else:
                print(f"ok    {name}: {v.status} {v.reason}")
    # Sol's sixth-round attack: a tracked checker that's a link to a writable file. stamp() sees only the
    # link, so a rewrite of what it leads to goes unseen, and the link has to be refused before any hashing.
    ran += 2
    (t / "g" / "tools").mkdir(parents=True)
    (t / "g" / "checker.lean").write_text("the checker")
    link = t / "g" / "tools" / "binding_check.lean"
    link.symlink_to("../checker.lean")
    seen = binding.stamp(link)
    (t / "g" / "checker.lean").write_text("a checker that says ok")
    if binding.stamp(link) != seen:
        print("note  standalone_link: stamp() saw the rewrite here, which the attack doesn't rely on")
    try:
        binding.plain_files(link)
        failures.append("standalone_link: a tracked checker that's a link was accepted")
    except binding.Verdict as v:
        if (v.status, v.reason) != ("error", "toolchain_untrusted_link"):
            failures.append(
                f"standalone_link: expected error toolchain_untrusted_link, got {v.status} {v.reason}"
            )
        else:
            print(f"ok    standalone_link: {v.status} {v.reason}")
    try:
        binding.plain_files(t / "g" / "checker.lean", *binding.STANDALONE)
        print("ok    standalone_plain: a plain file and this checkout's tracked files are accepted")
    except binding.Verdict as v:
        failures.append(f"standalone_plain: refused {v.status} {v.reason}: {v.detail}")
    return ran + tree_changes(binding, t / "changes", failures) + recorded_hashes(binding, t, failures)


def tree_changes(binding: Any, t: Path, failures: list[str]) -> int:
    """Every change to a tree changes its hash, including the two that hashed the same when a tree was hashed
    as one stream of paths and bytes: a file holding what two files would, and a directory where an empty
    file was."""

    def tree(name: str, entries: dict[str, str | None]) -> str:
        """A tree of files by path and content, or a directory for None, and its hash."""
        root = t / name / "IRLean"
        root.mkdir(parents=True)
        for path, content in entries.items():
            if content is None:
                (root / path).mkdir(parents=True)
            else:
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(content.encode())
        return binding.tree_hash(t / name, root)

    base = tree("base", {"a": "1", "b": "2", "d": None})
    changed = {
        "content": tree("content", {"a": "1", "b": "3", "d": None}),
        "added": tree("added", {"a": "1", "b": "2", "c": "", "d": None}),
        "removed": tree("removed", {"a": "1", "d": None}),
        "renamed": tree("renamed", {"a": "1", "c": "2", "d": None}),
        "moved": tree("moved", {"a": "1", "d/b": "2"}),
        "one_file_for_two": tree("one_file_for_two", {"a": "1\0IRLean/b\0" + "2", "d": None}),
        "file_for_directory": tree("file_for_directory", {"a": "1", "b": "2", "d": ""}),
    }
    linked = t / "linked" / "IRLean"
    linked.mkdir(parents=True)
    for path, content in (("a", "1"), ("b", "2"), ("c", "2")):
        (linked / path).write_text(content)
    (linked / "d").symlink_to("b")
    other = t / "other_link" / "IRLean"
    shutil.copytree(linked, other, symlinks=True)
    (other / "d").unlink()
    (other / "d").symlink_to("c")
    changed["link_target"] = binding.tree_hash(t / "other_link", other)
    if binding.tree_hash(t / "linked", linked) == changed["link_target"]:
        failures.append("tree_link_target: a link to another file hashes the same")
    same = [name for name, h in changed.items() if h == base]
    if same or len(set(changed.values())) != len(changed):
        failures.append(f"tree_changes: these hash as the unchanged tree or as each other: {same or changed}")
    else:
        print(f"ok    tree_changes: {len(changed)} changes each change the hash: {', '.join(changed)}")
    return 1


def recorded_hashes(binding: Any, t: Path, failures: list[str]) -> int:
    """Nix's recorded NAR hash is read right, used only for a store path root owns, and is the hash of what's
    there, which `nix hash path` works out again."""
    ran = 1
    # `nix-store --query --hash` and `nix hash path` for the pinned llvm-project.
    nix32 = PINNED_NIX32
    pinned = "sha256-+e5YvYEbCvvEQbLVIQP5hwPp4tEk6EB270bSEMKv0t4="
    bad = []
    for text in (nix32[1:], nix32[:-1] + "e", "z" + nix32[1:]):
        try:
            binding.nix32_decode(text, 32)
            bad.append(text)
        except ValueError:
            pass
    decoded = "sha256-" + base64.b64encode(binding.nix32_decode(nix32, 32)).decode()
    if decoded != pinned or bad:
        failures.append(f"nix32: decoded {decoded}, and accepted {bad}")
    else:
        print("ok    nix32: the pin's hash reads back, and a short, misspelled or overlong one is an error")
    run = binding.Runner(120, 1000)
    # A store this user owns, as a single-user install makes: its record could have been rewritten.
    ran += 1
    owned = t / "store"
    (owned / "x-source").mkdir(parents=True)
    store = binding.NIX_STORE
    binding.NIX_STORE = owned
    try:
        got = binding.recorded_nar_hash(run, owned / "x-source")
    finally:
        binding.NIX_STORE = store
    if got is not None:
        failures.append(f"user_owned_store: used the record {got} of a path this user owns")
    else:
        print("ok    user_owned_store: a path this user owns is hashed, not looked up")
    ran += 1
    source = Path(os.environ["LLVM_PROJECT_SRC"])
    recorded = binding.recorded_nar_hash(run, source)
    nested = binding.recorded_nar_hash(run, source / "llvm")
    hashed = subprocess.run(
        ["nix", "hash", "path", str(source)], capture_output=True, text=True, check=True
    ).stdout.strip()
    if nested is not None or recorded not in (None, hashed):
        failures.append(
            f"recorded_hash: {recorded} recorded, {hashed} hashed, {nested} for a directory in it"
        )
    else:
        how = "not used, as the store isn't root's" if recorded is None else "the hash of what's there"
        print(f"ok    recorded_hash: {how}, and a directory inside a store path isn't looked up")
    # A store the user's configuration names, a binary cache whose record says zlib's source is llvm-project.
    ran += 1
    zlib = Path(os.environ["ZLIB_SRC"])
    forged = forged_store(t, zlib)
    query = ["nix-store", "--query", "--hash", str(zlib)]
    fooled = subprocess.run(query, capture_output=True, text=True, env={**os.environ, **forged}, check=False)
    misled = binding.Runner(120, 1000)
    misled.env.update(forged)
    got = binding.recorded_nar_hash(misled, zlib)
    hashed = subprocess.run(
        ["nix", "hash", "path", str(zlib)], capture_output=True, text=True, check=True
    ).stdout.strip()
    if got not in (None, hashed):
        failures.append(
            f"forged_store: read {got} for {zlib}, from the user's store, which hashes to {hashed}"
        )
    else:
        alone = fooled.stdout.strip() == f"sha256:{nix32}"
        how = "fools nix-store alone" if alone else "doesn't fool nix-store here"
        print(f"ok    forged_store: a binary cache the user's configuration names, which {how}, isn't read")
    return ran


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true", help="keep build/binding/tests")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--shard", default="1/1", help="I/N: run the cases in shard I of N")
    args = ap.parse_args()
    shard, shards = (int(x) for x in args.shard.split("/"))
    if not 1 <= shard <= shards:
        sys.exit(f"--shard {args.shard}: I has to be from 1 to N")

    def runs(name: str) -> bool:
        """Whether this run has the case `name`: it's asked for, and in this shard."""
        mine = crc32(name.encode()) % shards == shard - 1
        return (not args.only or name in args.only) and mine

    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    failures: list[str] = []
    ran = 0
    for name, make, extra, (status, reason) in CASES:
        if not runs(name):
            continue
        ran += 1
        verdict = verify(make(name), *extra)
        got = (verdict.get("status"), verdict.get("reason"))
        if got != (status, reason):
            failures.append(f"{name}: expected {status} {reason}, got {got}: {verdict.get('detail')}")
        elif status != "bound" and verdict.get("exit_code") == 0:
            failures.append(f"{name}: {status} with exit code 0")
        else:
            print(f"ok    {name}: {got[0]} {got[1]}")
        if "open_obligation" not in verdict or not verdict.get("does_not_establish"):
            failures.append(f"{name}: the verdict doesn't say what it leaves open")
    if runs("hashes"):
        ran += hash_cases(failures)
    if runs("time_limit"):
        # The certificate that ran out of time mustn't still be running.
        ran += 1
        left = subprocess.run(
            ["pgrep", "-f", "binding/tests/.*Cert.lean|runs/.*/Fx/Cert.lean"],
            capture_output=True,
            text=True,
            check=False,
        ).stdout
        if left:
            failures.append(f"time_limit: left running: {left}")
        else:
            print("ok    time_limit_stopped: nothing left running")
    if runs("adds_companion"):
        # A file added to IRLean's library is caught, whatever its name. It's this checkout's own build, and
        # the file is removed after.
        ran += 1
        added = ROOT / ".lake" / "build" / "lib" / "lean" / "IRLean" / "Basic.ir"
        if added.exists():
            failures.append(f"adds_companion: {added} is already there")
        else:
            try:
                verdict = verify(record("adds_companion", ADDS_COMPANION))
            finally:
                added.unlink(missing_ok=True)
            got = (verdict.get("status"), verdict.get("reason"))
            if got != ("refused", "artifacts_modified"):
                failures.append(f"adds_companion: expected refused artifacts_modified, got {got}")
            else:
                print(f"ok    adds_companion: {got[0]} {got[1]}")
    if runs("leaves_process"):
        # Code that ran while the certificate compiled doesn't outlive it.
        ran += 1
        verdict = verify(record("leaves_process", LEAVES_PROCESS))
        left = subprocess.run(
            ["pgrep", "-f", "sleep 313.7"], capture_output=True, text=True, check=False
        ).stdout
        if verdict.get("status") != "bound" or left:
            failures.append(
                f"leaves_process: {verdict.get('status')} {verdict.get('reason')}, left: {left!r}"
            )
        else:
            print("ok    leaves_process: bound, nothing left running")
    if runs("path_leanchecker"):
        # A leanchecker earlier on PATH that passes everything isn't the one that runs.
        ran += 1
        fake = WORK / "fake-bin"
        fake.mkdir(exist_ok=True)
        (fake / "leanchecker").write_text("#!/bin/sh\nexit 0\n")
        (fake / "leanchecker").chmod(0o755)
        verdict = verify(
            record("path_leanchecker", SKIPPED), env={"PATH": f"{fake}:{os.environ.get('PATH', '')}"}
        )
        got = (verdict.get("status"), verdict.get("reason"))
        if got != ("refused", "kernel_replay_failed"):
            failures.append(f"path_leanchecker: expected refused kernel_replay_failed, got {got}")
        else:
            print(f"ok    path_leanchecker: {got[0]} {got[1]}")
    if runs("uncovered"):
        # A bound claim about f says what else the run changed, which it doesn't cover.
        ran += 1
        verdict = verify(record("uncovered", GOOD, input_ll="two.ll"))
        got = (verdict.get("status"), verdict.get("uncovered_changes"))
        if got != ("bound", {"functions": ["g"], "module_level": False}):
            failures.append(f"uncovered: expected bound with g uncovered, got {got}: {verdict.get('detail')}")
        else:
            print(f"ok    uncovered: {got[0]}, uncovered {got[1]}")
    if runs("other_source"):
        # The same version of opt, with LLVM_PROJECT_SRC some other tree: not the pinned source.
        ran += 1
        verdict = verify(good("other_source"), env={"LLVM_PROJECT_SRC": str(HERE)})
        got = (verdict.get("status"), verdict.get("reason"))
        if got != ("refused", "llvm_pin_mismatch"):
            failures.append(f"other_source: expected refused llvm_pin_mismatch, got {got}")
        else:
            print(f"ok    other_source: {got[0]} {got[1]}")
    if runs("other_store_source"):
        # Another store path, which tools/binding.py looks up rather than hashes when root owns the store.
        ran += 1
        verdict = verify(good("other_store_source"), env={"LLVM_PROJECT_SRC": os.environ["ZLIB_SRC"]})
        got = (verdict.get("status"), verdict.get("reason"))
        if got != ("refused", "llvm_pin_mismatch"):
            failures.append(f"other_store_source: expected refused llvm_pin_mismatch, got {got}")
        else:
            print(f"ok    other_store_source: {got[0]} {got[1]}")
    if runs("forged_store_source"):
        # The same, with the user's Nix configuration naming a binary cache that says it's the pinned source.
        ran += 1
        zlib = os.environ["ZLIB_SRC"]
        forged = forged_store(WORK / "forged", Path(zlib))
        verdict = verify(good("forged_store_source"), env={"LLVM_PROJECT_SRC": zlib, **forged})
        got = (verdict.get("status"), verdict.get("reason"))
        if got != ("refused", "llvm_pin_mismatch"):
            failures.append(f"forged_store_source: expected refused llvm_pin_mismatch, got {got}")
        else:
            print(f"ok    forged_store_source: {got[0]} {got[1]}")
    if runs("cache"):
        ran += cache_cases(failures)
    if not args.keep:
        shutil.rmtree(WORK, ignore_errors=True)
    for f in failures:
        print(f"FAIL  {f}")
    print(f"{ran - len(failures)}/{ran} binding cases behave")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
