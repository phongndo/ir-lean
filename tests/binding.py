#!/usr/bin/env python3
"""Checks that tools/binding.py binds a certificate to what it's about, and refuses evidence that doesn't
match.

One real rewrite, `instcombine` folding `add i8 %x, 0` in tests/binding/add_zero.ll, with a certificate that
the functions ir-lean generates before and after are equal. Its bundle has to come back `bound`. Then each
case breaks one thing, as someone handing over wrong evidence would, and the verdict has to be the status and
reason given, never `bound`: a theorem of another type, a changed file, a changed configuration, a manifest
from another toolchain, a cache entry that isn't for this evidence, and claims nothing here can check.

It runs one process at a time, each capped by tools/binding.py, in build/binding/tests, and needs
`nix develop`, build/ir-lean and `lake build`.

usage: tests/binding.py [--keep] [--only NAME ...]
"""

import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

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

# The attack the adversarial lane found with tools/verify.py, on a real instcombine run: the two are equal in
# the model, since both stop at a frozen poison, and Fx.stops shows the source does. Equality alone is all a
# certificate can prove here, and it isn't the claim.
FREEZE_EQUAL = (
    HEADER
    + """theorem Fx.cert : Fx.Src.f = Fx.Tgt.f := by
  funext x
  cases x with
  | none => rfl
  | some x =>
    simp only [Fx.Src.f, Fx.Tgt.f, noundef]
    rw [run.eq_1 Fx.Src.f.step, run.eq_1 Fx.Tgt.f.step]
    by_cases h : 8#8 ≤ x
    · simp [Fx.Src.f.step, Fx.Tgt.f.step, llvm, h]
    · have : 1#8 <<< x.toNat >>> x.toNat = 1#8 := by
        have hx : x.toNat < 8 := by bv_omega
        generalize x.toNat = n at hx ⊢
        match n, hx with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
      simp [Fx.Src.f.step, Fx.Tgt.f.step, llvm, h, this]

theorem Fx.stops : Fx.Src.f (some 8#8) = some (.error (.model .freezePoison)) := by
  simp only [Fx.Src.f, noundef]
  rw [run.eq_1 Fx.Src.f.step]
  simp [Fx.Src.f.step, llvm]
"""
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


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def record(
    name: str, certificate: str, kind: str = "ir_instance_equivalence", input_ll: str = "add_zero.ll"
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
            "instcombine",
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
    (
        "freeze_equality",
        lambda n: record(n, FREEZE_EQUAL, input_ll="freeze.ll"),
        [],
        ("refused", "claim_type_mismatch"),
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
    (
        "trusted_promise",
        lambda n: record(n, GOOD, input_ll="willreturn.ll"),
        [],
        ("unsupported", "trusted_promise"),
    ),
    # Limits make a verdict unknown, never bound or refused.
    ("time_limit", lambda n: record(n, SLOW), ["--timeout", "20"], ("unknown", "time_limit")),
    ("memory_limit", lambda n: record(n, GREEDY), ["--memory", "1500"], ("unknown", "resource_limit")),
    (
        "refinement_unavailable",
        lambda n: record(n, GOOD, kind="ir_instance_refinement"),
        [],
        ("unsupported", "claim_kind_unavailable"),
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
    return ran


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true", help="keep build/binding/tests")
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    failures: list[str] = []
    ran = 0
    for name, make, extra, (status, reason) in CASES:
        if args.only and name not in args.only:
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
    if not args.only or "hashes" in args.only:
        ran += hash_cases(failures)
    if not args.only or "time_limit" in args.only:
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
    if not args.only or "adds_companion" in args.only:
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
    if not args.only or "leaves_process" in args.only:
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
    if not args.only or "path_leanchecker" in args.only:
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
    if not args.only or "uncovered" in args.only:
        # A bound claim about f says what else the run changed, which it doesn't cover.
        ran += 1
        verdict = verify(record("uncovered", GOOD, input_ll="two.ll"))
        got = (verdict.get("status"), verdict.get("uncovered_changes"))
        if got != ("bound", {"functions": ["g"], "module_level": False}):
            failures.append(f"uncovered: expected bound with g uncovered, got {got}: {verdict.get('detail')}")
        else:
            print(f"ok    uncovered: {got[0]}, uncovered {got[1]}")
    if not args.only or "other_source" in args.only:
        # The same version of opt, with LLVM_PROJECT_SRC some other tree: not the pinned source.
        ran += 1
        verdict = verify(good("other_source"), env={"LLVM_PROJECT_SRC": str(HERE)})
        got = (verdict.get("status"), verdict.get("reason"))
        if got != ("refused", "llvm_pin_mismatch"):
            failures.append(f"other_source: expected refused llvm_pin_mismatch, got {got}")
        else:
            print(f"ok    other_source: {got[0]} {got[1]}")
    if not args.only or "cache" in args.only:
        ran += cache_cases(failures)
    if not args.keep:
        shutil.rmtree(WORK, ignore_errors=True)
    for f in failures:
        print(f"FAIL  {f}")
    print(f"{ran - len(failures)}/{ran} binding cases behave")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
