# Binding proofs to LLVM

How a certificate about an optimization is tied to what it's about: the input IR, the output IR, the pass and options
that made it, the LLVM it came from, the Lean ir-lean generated, and the theorem's exact type. What ties each link
today, what doesn't, and the contract [`tools/binding.py`](../tools/binding.py) checks. For what any theorem here means,
see [trust](trust.md).

Facts here were checked on top of commit `18421be` on 2026-11-08, on x86-64 Linux in the dev shell, with LLVM 23.1.3
and Lean 4.35.0.

**A `bound` verdict is translation validation of one run.** It says one function, in one input module, after one run
of `opt` with one pass spec and triple, is equal in IRLean's semantics before and after, and that the model never stops
on it, so the model knows what LLVM does on every input. It says nothing about the pass
on any other input, about the pass's C++, about native code, or about a pipeline. Hashes establish identity, not
correctness: two files with the same SHA-256 are the same bytes, whatever those mean.

## The pins this was checked against

| What | Pinned to | Where the pin lives | What checks it |
| --- | --- | --- | --- |
| llvm-project | `llvmorg-23.1.3`, commit `0d261d1ca552c95a8f007e061c787ac7132fbcbc`, NAR hash `sha256-+e5YvYEbCvvEQbLVIQP5hwPp4tEk6EB270bSEMKv0t4=` | [`tests/llvm/targets.toml`](../tests/llvm/targets.toml) `[project]` | `tools/binding.py` reads it there, and refuses a manifest naming anything else. `nix hash path $LLVM_PROJECT_SRC` gives that NAR hash in the dev shell |
| `opt` | `LLVM version 23.1.3`, `/nix/store/8lg1k2kl3dazk3s0ppqvnqp17y1032cb-llvm-23.1.3/bin/opt` | `llvmPackages_latest` in [`nix/shell.nix`](../nix/shell.nix), through `flake.lock` | Its SHA-256 is in each manifest, and its version has to match the tag |
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | [`lean-toolchain`](../lean-toolchain), through `elan` | The `lean` and `leanchecker` binaries' SHA-256 are in each manifest |
| ir-lean, `IRLean` | Built from this commit | The working tree | The binary's and the `.olean` files' SHA-256 are in each manifest |

`tools/binding.py` keeps no pin of its own. When the pinned LLVM moves, it moves in `tests/llvm/targets.toml`, and every
recorded manifest stops verifying until it's recorded again.

## What ties each link today

The chain from LLVM's source to a counted result, and what each tool in the repo does about each link.
`tests/passes.py` is the unpublished scorer on `research/prove-llvm-optimizations`, read but not run here.

| Link | `tests/llvm.py` | `tools/verify.py` | `tests/passes.py` (unpublished) | `tools/binding.py` |
| --- | --- | --- | --- | --- |
| llvm-project commit | `targets.toml` pins it, and a one-off compared the 60 proved files with GitHub's | Not recorded | Not recorded. `score.json` has `opt --version` once | Manifest names the commit, which has to be the repo's pin. `LLVM_PROJECT_SRC` has to have the pinned NAR hash |
| `opt` binary | Not used | Not used | Whatever is on PATH. Not in the cache key | SHA-256 and version recorded and checked |
| Pass, options, triple | Not applicable | Not applicable | `-passes=` and `-mtriple` from the `RUN` line. Other options are dropped. Not recorded per instance | Pass spec and `-mtriple` recorded. No other options are representable |
| Data layout and triple of the IR | Fixed by `PROOF_CFLAGS` | Not recorded | Not recorded | Read from both IR files, and have to match the manifest |
| Input IR | Compiled from pinned source with recorded flags, hashed | Hashed | In the cache key, as text. Not kept | Hashed, and `opt` rerun on it |
| Output IR | Not applicable | Not applicable | In the cache key. Not kept | Hashed, and has to be what `opt -passes=SPEC` gives, byte for byte |
| Generated Lean | Regenerated each run | Regenerated, hashed | Regenerated. Not kept | Hashed, and has to be what ir-lean writes, byte for byte |
| Theorem's type | Has to mention the function, from the generated module | Has to mention it. A pinned statement can match up to reducible defeq | Written by the scorer as `Refines Src.f Tgt.f`. The unpublished `checkRefines` checks the head, the two functions, and that the type and instance use only Lean's and IRLean's constants | Built by the checker from the claim's kind, and has to be the same `Expr` |
| Axioms and kernel | `check_axioms.lean`, `leanchecker` | Same | Same | Same, unchanged |
| Files the proof's code could change | Not checked | IR, generated module and library rehashed | Not checked | Generated modules, the certificate's `.olean`, the library and every tool rehashed after the certificate compiles, and again at the end |
| The counted result | Manifest with hashes and statements | `result.json` with hashes | A status in `build/passes/cache/KEY.json`. The certificate is deleted | A bundle that can be replayed from scratch, and a verdict |

### What the audit found

None of these changes a theorem proved so far. Each is a reason a counted result could be about something other than
what it's counted as.

| Finding | Where | Effect | Status |
| --- | --- | --- | --- |
| Equality of two generated functions certified a wrong rewrite: duplicating a `freeze`. On a poison input both stop the model at the frozen poison, so they're equal there, though LLVM's target can return anything where its source returns 0. `tools/binding.py` asked for exactly that equality | The adversarial lane's `tests/verification_negative/cases/freeze_duplicated_equality_pin`, against `tools/verify.py`. The same claim shape was this tool's `ir_instance_equivalence` | A certificate could bind any rewrite where both sides stop the model, which a model stop never says anything about | Fixed. The claim now also says the source never stops the model, and `freeze_equality` in `tests/binding.py` reproduces the attack on a real `instcombine` run: the certificate proves equality and that the source stops, and is refused |
| A generated module names its input file, and nothing else: not the IR's hash, ir-lean's version, the triple or the data layout | `src/Emitter.cpp`'s header | A generated module on its own isn't bound to any IR. Only regenerating it binds it | `tools/binding.py` regenerates and compares bytes. The emitter is unchanged |
| `checkRefines` checks that the instance argument uses only Lean's and `IRLean`'s constants, not that it's the instance Lean would find. A theorem stating `@IRLean.Refines _ ⟨fun _ _ => True⟩ Src.f Tgt.f` would pass it, proved by `trivial` | `tests/check_axioms.lean` on the unpublished branch | None through `tests/passes.py`, which writes the statement itself and lets Lean find the instance. A certificate from anywhere else could prove nothing | Analysis only: the unpublished branch wasn't built or run. `tools/binding_check.lean` compares the whole type, instance included, with the one it builds |
| A cached `certified` can't be checked again: the certificate, the generated modules and the IR are deleted, and the cache entry is a status | `tests/passes.py` | The score trusts `build/passes/cache`. Nothing records which pass spec, triple and test file a certified instance came from | Open. A bundle per certified instance would make each one replayable. That's the scorer owner's call |
| The cache key covers the IR pair, ir-lean, every `.olean` under `.lake/build/lib/lean`, `check_axioms.lean` and the scorer's code, but not `opt`, `lean` or `leanchecker` | `tests/passes.py` | A changed `leanchecker` with unchanged libraries would reuse old results. `opt` doesn't change what a certificate is about, only which pair a test gives | Open, for the scorer owner |
| Options on the `RUN` line other than `-passes=` and `-mtriple` are dropped | `tests/passes.py` | A certificate is about a configuration the regression test may not run. `docs/passes.md` on that branch says so | Open. `tools/binding.py` can't represent other options, so it refuses rather than drops them |
| Instances are the functions whose text changed, and their callers. A pass that changes only globals, declarations or module flags makes no instance | `tests/passes.py` | Such a pass is neither counted nor penalised. Pure functions can't read globals, so no certified instance is wrong because of it | Open, for the scorer owner |
| `tools/verify.py` accepts a pinned statement up to reducible definitional equality | `tools/verify_check.lean` | A statement can unfold to the pinned one through a reducible definition from Lean, `IRLean` or the generated module. Not from the proof, which it already refuses | Kept as is. `tools/binding_check.lean` is stricter: the same `Expr` |

## The contract

A **bundle** is a directory with a manifest and the six files it names. `record` writes one. `verify` checks one, and
believes nothing in it.

```console
$ nix develop
$ tools/binding.py record --input tests/binding/add_zero.ll --passes instcombine \
    --mtriple x86_64-unknown-linux-gnu --function f --certificate tests/binding/AddZero.lean \
    --theorem Fx.cert --namespace Fx --out build/binding/add_zero
$ tools/binding.py verify build/binding/add_zero/manifest.json
```

### The manifest, `ir-lean.binding.manifest/1`

Every object has exactly these keys. Any other key, or a missing one, is `manifest_invalid`, so a field nothing checks
can't ride along.

| Field | Means | Checked by |
| --- | --- | --- |
| `claim.kind` | One of the kinds below | The checker builds the expected type from it |
| `claim.namespace` | The Lean namespace, such as `Fx`. The generated modules are `Fx.Src` and `Fx.Tgt`, and the certificate `Fx.Cert` | Regenerating them |
| `claim.function`, `claim.lean_function` | The LLVM name, and the name ir-lean gives it | `ir-lean --report` on both IR files |
| `claim.theorem` | The theorem's full name, which has to be declared in `Fx.Cert` | `tools/binding_check.lean` |
| `llvm.repository`, `.tag`, `.commit`, `.nix_hash` | The llvm-project the `opt` binary is from | Equal to `tests/llvm/targets.toml`'s pin. `opt --version` has to say the tag's version, and `LLVM_PROJECT_SRC` has to have that NAR hash |
| `transform.passes`, `.mtriple` | The `opt -passes=` spec, and `-mtriple` or `null` | Rerunning `opt` |
| `target.triple`, `.datalayout` | What both IR files say | Reading them |
| `artifacts.ROLE.path`, `.sha256` | `input`, `src_ir`, `tgt_ir`, `src_lean`, `tgt_lean`, `certificate`: a plain file directly in the bundle, by name, and its hash | Hashing it |
| `toolchain` | The version and SHA-256 of `lean`, `leanchecker` and `opt`, and the SHA-256 of every file in the Lean toolchain, `build/ir-lean`, every file of `IRLean`'s library, `tests/check_axioms.lean`, `tools/binding_check.lean` and `tools/binding.py` | Recomputing each, with paths from the toolchain's or the library's own directory, so a moved checkout hashes the same. A link has to be a bare file name naming a sibling that's hashed itself, or an absolute path into the Nix store, and never a directory: nothing in a link's target is normalized, so nothing it passes through goes unchecked. The pinned toolchain's 14 links are all of these kinds. `build/ir-lean`, `tests/check_axioms.lean`, `tools/binding_check.lean` and `tools/binding.py` have to be files, not links, since only a link itself would be compared afterward. `lean` and `leanchecker` are the ones in the toolchain `lean --print-prefix` names, and `opt` the one on PATH, and each runs by that absolute path, so what runs is what was hashed |

The source IR is `opt -S -passes=verify` of the input, and the target is `opt -S -passes=SPEC` of it. Both read it from
stdin, so neither names a path.

### Claim kinds

| Kind | The claim, as Lean | Checkable now |
| --- | --- | --- |
| `ir_instance_equivalence` | `Fx.Src.f = Fx.Tgt.f ∧ ∀ (x : IRLean.Val 8) (s : IRLean.ModelStop), Fx.Src.f x ≠ some (.error (.model s))`, with a binder for each argument: on every input, poison included, both have the same outcome in IRLean's semantics, and the source never stops the model | Yes, for a function without memory, whose arguments are all `noundef` in the source, and whose target IR makes no promise IRLean trusts |
| `ir_instance_refinement` | `IRLean.Refines Fx.Src.f Fx.Tgt.f`, with the instance Lean finds where only `IRLean` and the generated modules are imported | Only with an `IRLean` that has `IRLean.Refines`, which this commit doesn't. Until then it's `unsupported`, `claim_kind_unavailable` |
| `rewrite_all_inputs` | The pass's rewrite is right for every input module (L3) | No. Always `unsupported` |
| `pass_implementation` | The pass's compiled C++ makes only proved rewrites (L4) | No. Always `unsupported` |
| `pipeline_composition` | A pipeline at a level and target preserves meaning | No. Always `unsupported` |

Equality alone isn't evidence. A model stop is where IRLean doesn't know what LLVM does, so two functions that stop
there are equal in the model and can differ in LLVM. With the source never stopping, neither does the target, and
every outcome the source has, the target has too: a value, poison, undefined behavior, or a run that never ends. That
implies refinement as the adversarial lane's contract states it, where a model stop in the source allows nothing.

It also holds only where the model has no less undefined behavior than LLVM in the source, and no more in the target.
So three kinds of function are `unsupported`, before any proof is read:

- one that uses memory or pointers, where the model has more undefined behavior than LLVM
  ([trust](trust.md#known-gaps-in-the-model)), so a source undefined in the model can be defined in LLVM;
- any target IR with `mustprogress` or `willreturn`, which IRLean trusts instead of checking: a target that spins
  under one is undefined in LLVM, and runs forever in the model, just as a source without one does;
- one with an argument that isn't `noundef` in the source. IRLean's values are a value or poison, never `undef`, and
  the emitter refuses `undef` in the IR, but a caller can still pass one. An `undef` argument can be a different value
  at each use, so `and i8 %x, 0` and `xor i8 %x, %x` are equal in the model and differ in LLVM. `noundef` makes passing
  `undef` or poison undefined, which the model checks.

A certificate that can't prove this claim, for a rewrite that's right but only refines, comes back `refused` or
`certificate_compile_failed`. That says the evidence doesn't bind, never that the rewrite is wrong: nothing here
finds counterexamples, and no verdict counts against a pass as refuted.

Equivalence is stronger than refinement, so it fails on rewrites that only refine, such as one that removes undefined
behavior or a model stop. It's here because it needs nothing this commit doesn't have.

### The checks, in order

Each one that runs is listed in the verdict's `checks`. The first that fails decides the verdict.

1. **`manifest`**: the schema, exactly.
2. Claim kinds nothing can check stop here as `unsupported`.
3. **`artifacts`**: each file is a plain file in the bundle with the recorded hash.
4. **`toolchain`**: every hash and version is recomputed and has to match.
5. **`llvm_pin`**: the pin, `opt`'s version, and `LLVM_PROJECT_SRC`'s NAR hash.
6. **`target`**: both IR files' triple and data layout, and `-mtriple`.
7. **`cache`**, if `--cache` is given: see [below](#the-cache).
8. **`transform_replay`**: `opt` gives both IR files byte for byte.
9. **`translation_replay`**: ir-lean gives both Lean modules byte for byte, and the same name for the function. It
   has to translate the function, without memory, on both sides, and its arguments have to be `noundef`. Before this, a target IR with `mustprogress` or
   `willreturn` is `unsupported`, and the verdict's `uncovered_changes` lists the other functions the run changed and
   whether anything outside a function changed, none of which the claim covers.
10. **`compile_generated`**, **`compile_certificate`**: Lean compiles them in a fresh directory, from source, with only
    `IRLean` on the path besides them. No `.olean` comes from the bundle. The certificate's code runs here, so every
    file and link where Lean finds modules is listed with its hash before and after, and only the certificate's
    `.olean` may be new. A module the certificate adds, named like one it imports, is refused, and so is any change
    to the toolchain, `IRLean` or these tools. Those were hashed in step 4, and a second hash would take seconds, so
    what `lstat` says of each entry, its inode, size and change time, is compared instead. A process without root
    can't set a change time back.
11. **`claim_type`**: [`tools/binding_check.lean`](../tools/binding_check.lean) builds the claim where only Lean,
    `IRLean` and the two generated modules are imported, and reads the certificate as data. Its theorem has to be
    declared in it, import nothing else, use only constants that are the same declarations, and have exactly that type,
    as the same `Expr`. Definitional equality isn't enough: an instance or definition of the certificate's own could
    make a weaker claim unfold to the right one. Every module it imports has to be read from where it should be:
   Lean's from the toolchain, `IRLean`'s from its library, and the rest from the run's directory.
12. **`axioms`**: [`tests/check_axioms.lean`](../tests/check_axioms.lean), unchanged, with the theorem required to name
    both functions.
13. **`kernel_replay`**: `leanchecker` on the two generated modules and the certificate.
14. **`unchanged`**: every file and link in the run's Lean directory hashes the same at the end as just after the
    certificate compiled, and the toolchain, `IRLean` and these tools are as `lstat` saw them before it compiled, so
    every check read the same files.

### The verdict, `ir-lean.binding.verdict/1`

| Status | Exit | Means |
| --- | --- | --- |
| `bound` | 0 | Every check passed |
| `refused` | 1 | The evidence isn't what it claims to be |
| `unsupported` | 3 | The claim kind can't be checked, or the emitter refuses the function |
| `unknown` | 4 | A time or memory limit stopped a step. More may help |
| `error` | 5 | A tool failed in a way that says nothing about the evidence, or a bug here |

Only `bound` is a success. Every verdict, whatever its status, carries `does_not_establish`, `trusted` and
`open_obligation`. A `bound` one also carries `establishes` and `statement`, the claim as Lean printed it.

| Reason | Status | Means |
| --- | --- | --- |
| `replayed` | `bound` | Every check passed |
| `manifest_invalid` | `refused` | A missing or extra key, a bad value, or a path that isn't a file name |
| `artifact_hash_mismatch` | `refused` | A file isn't there, isn't plain, or has another hash |
| `toolchain_mismatch` | `refused` | A tool or checker on this machine isn't the one recorded |
| `llvm_pin_mismatch` | `refused` | Another llvm-project, an `opt` of another version, or another source tree |
| `config_mismatch` | `refused` | The IR's triple or data layout, or `-mtriple`, isn't what the manifest says |
| `transform_replay_mismatch` | `refused` | `opt` doesn't give the recorded IR |
| `translation_replay_mismatch` | `refused` | ir-lean doesn't give the recorded Lean |
| `function_not_found` | `refused` | The IR has no such function |
| `certificate_compile_failed` | `refused` | Lean rejects the certificate |
| `artifacts_modified` | `refused` | A checked file or tool changed while the certificate's code could run |
| `theorem_not_found`, `not_a_theorem` | `refused` | No such theorem in the certificate's module |
| `certificate_imports_disallowed` | `refused` | The certificate imports something besides Lean, `IRLean` and the generated modules |
| `foreign_constant` | `refused` | The theorem's type uses a constant the certificate defines |
| `module_shadowed` | `refused` | A module the certificate imports is read from somewhere it shouldn't be |
| `claim_type_mismatch` | `refused` | The theorem's type isn't the claim. `expected` and `got` print both, with every implicit argument |
| `function_not_generated`, `signature_mismatch` | `refused` | The two functions aren't both generated, or have different types |
| `axiom_policy_failed` | `refused` | `tests/check_axioms.lean` rejects the certificate's modules |
| `kernel_replay_failed` | `refused` | `leanchecker` rejects a declaration |
| `claim_kind_unverifiable` | `unsupported` | The kind is L3, L4 or a pipeline |
| `claim_kind_unavailable` | `unsupported` | `IRLean` has no `IRLean.Refines` |
| `function_unsupported` | `unsupported` | ir-lean leaves the function out |
| `memory_unsupported` | `unsupported` | The function uses memory or pointers |
| `undef_argument` | `unsupported` | An argument isn't `noundef` in the source, so a caller can pass `undef` |
| `trusted_promise` | `unsupported` | The target IR has `mustprogress` or `willreturn` |
| `time_limit`, `resource_limit` | `unknown` | A step ran out of time, or Lean or a cgroup ran out of memory, heartbeats or stack |
| `toolchain_untrusted_link` | `error` | A link in the toolchain or `IRLean`'s library isn't a bare file name naming a sibling that's hashed itself, or an absolute path into the Nix store that stays there. A root that's itself a link, a link to a directory, and `build/ir-lean`, `tests/check_axioms.lean`, `tools/binding_check.lean` or `tools/binding.py` being a link, are refused too |
| `toolchain_missing`, `tool_failed`, `generated_module_failed`, `checker_error`, `invalid_request`, `internal_error` | `error` | Something here failed |

### The cache

`--cache DIR` keeps a `bound` verdict at `DIR/KEY.json`, where `KEY` is the SHA-256 of the manifest and the live
toolchain. An entry is used only if its key, the manifest's hash and the toolchain in it all match, and steps 1 to 6 run
first either way, so a changed file or tool is refused before the cache is read. Anything else is `stale_ignored`, and
everything is replayed.

The cache is local, trusted storage, and an optimization. An entry someone writes with the right key, manifest hash and
toolchain is believed. A verdict for anyone else has to come from `verify` without `--cache`.

### Limits

Each process runs alone, with a time limit (300 s by default), Lean's `-M` memory limit (3000 MB by default), and, where
`systemd-run --user --scope` works, a cgroup capped at 512 MB more, with no swap. The verdict's `memory_capped` says
which. A process stopped by any of these makes the verdict `unknown`, never `bound` or `refused`. A process that runs out
of time is killed with everything it started: its process group, and its scope. So is anything a process leaves
running when it exits, such as a process a certificate's code started while it compiled. A step is done when its
main process exits, not when its output closes.

## What a `bound` verdict rests on

Everything in [trust](trust.md), and these:

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| IRLean's semantics are LLVM's for this code, and the emitter is faithful | [Trust](trust.md) and `tests/opcheck.py`. An emitter bug the same on both sides cancels out of an equality, so it can hide one | A wrong operation those checks miss |
| Without memory, the model's undefined behavior is no more than LLVM's, and its other gaps are model stops, which the claim rules out | The known cases of more are about memory ([trust](trust.md#known-gaps-in-the-model)), and memory is unsupported. `undef` is refused by the emitter in the IR, and arguments have to be `noundef` | More undefined behavior in integer code than LLVM has, which would let a source's undefined behavior hide a wrong target |
| `opt` does the same on a rerun | It's deterministic on one input, and the replay checks it did | Nothing here: a nondeterministic pass is refused, not wrongly bound |
| The `opt` binary is built from the pinned source | `LLVM_PROJECT_SRC` has the pinned NAR hash, and the same `llvmPackages` gives both. The derivation came from the binary cache, so it isn't on this machine to inspect | A Nix or binary-cache compromise |
| `-passes=` and `-mtriple` are all the configuration | They are all `opt` was given | A pass reading another option's default, or the environment |
| Lean's kernel, elaborator and `leanchecker` | [Trust](trust.md) | A Lean bug |
| SHA-256 | Standard | A collision |
| The certificate's code, which runs while it compiles, doesn't reach past what's rechecked | The run's directory is hashed again afterward and at the end, the toolchain, IRLean and every tool are compared by `lstat`, and what it left running is killed. It isn't sandboxed: `bwrap` isn't in the dev shell, and may not work on CI runners | A change to a file nothing checks that a check reads, such as the Python interpreter, a process running as root or one that sets the clock back, or, without systemd, a process that left its process group |

## Independent replay

Who can check a bundle, and how independent that is from whoever made it.

| Level | What's independent | Status |
| --- | --- | --- |
| R0: fresh directory, same machine | Every artifact rebuilt from the bundle's sources, no `.olean` reused, no cache | Done: `tools/binding.py verify` |
| R1: another machine | The machine, its store and its builds. The bundle, the repo at the same commit and `flake.lock` give the same toolchain hashes, or the verdict is `toolchain_mismatch` | Designed. Nothing runs it yet, and the binary hashes may differ across machines even from one `flake.lock`, which would need the manifest to pin store paths instead |
| R2: another kernel | Lean's kernel and `leanchecker`: export the certificate's modules and replay them in a separate checker, such as `lean4lean` or `nanoda` | Not started |
| R3: other semantics | IRLean: run Alive2's `alive-tv`, already pinned in the shell for `tests/opcheck.py`, on the same IR pair, and treat a disagreement as a bug to find in one of them | Not started. Alive2 agreeing is evidence, not a proof, and a timeout there is unknown |
| R4: another translation | The emitter: a second way from IR to the claim, such as Lean reading the IR itself ([design](design.md#ir-and-lean-both-ways)) | Not started |

## What isn't bound yet

The gap between a `bound` verdict and the [goal](roadmap.md) is the rest of the work. Each of these counts as
unfinished.

**Implementation correspondence.** No theorem here relates LLVM's C++ for any pass to the rewrites it makes. A `bound`
verdict says one run of a binary gave output equal to its input, in the model. To tie a proof to the implementation,
one of these is needed for each pass:

- Validate every run: run the checker on every function `opt` changes, in every build that's trusted. That proves each
  output, not the pass, and costs a proof per change.
- Prove the rewrites, then the code (L3 and L4): state each rewrite a pass can make as a theorem for all inputs, and
  prove the pass's C++ makes only those. The C++ could be reached through its own IR, as `tests/llvm.py` reaches
  compiler-rt, but that needs C++ objects, `std::` containers and LLVM's own data structures in the model, none of which
  it has.

**Composition.** A pipeline is a sequence of runs, and equality chains: if each step's target IR is the next step's
source, the first source equals the last target. The contract this needs first, before any code:

- a manifest listing steps, where each step's `tgt_ir` hash is the next step's `input` hash, and the steps are what
  `opt -print-pipeline-passes` says the level runs, for that triple;
- for refinement, a transitivity theorem for `IRLean.Refines`, which is the semantics owner's to state, since it depends
  on how poison, undefined behavior and model stops are treated;
- functions the pipeline adds, removes, inlines or changes the signature of, which a per-function claim can't express.

**Unsupported today.**

- `ir_instance_refinement`, until `IRLean.Refines` is on the main branch. The checker builds it with `mkAppM`, and that
  path hasn't been run.
- Functions that use memory or pointers, arguments that aren't `noundef`, and target IR with `mustprogress` or
  `willreturn`.
- Rewrites whose source can stop the model, such as on a frozen poison. A refinement claim could say a model stop in
  the source allows nothing, and so can't be bound either; it needs `ir_instance_refinement`, or a stand-in such as the
  adversarial lane's, under separate ownership.
- Any `opt` option but `-passes=` and `-mtriple`.
- More than one function per manifest, and functions a pass adds or removes.
- Changes outside a function: globals, declarations, metadata and module flags, and other functions. The verdict's
  `uncovered_changes` lists them, and a bound claim says nothing about them.
- Everything ir-lean refuses. See [trust](trust.md#known-gaps-in-the-model).
- Codegen: `llc` and machine passes have no IR on one side.

## Tests

[`tests/binding.py`](../tests/binding.py) runs in the dev shell after `lake build` and building `build/ir-lean`. It
records one real rewrite, `instcombine` folding `add i8 %x, 0` from
[`tests/binding/add_zero.ll`](../tests/binding/add_zero.ll), with the certificate
[`tests/binding/AddZero.lean`](../tests/binding/AddZero.lean), and has to get `bound`. Then each case breaks one thing
and has to get the status and reason given:

| Kind | Cases | Verdict |
| --- | --- | --- |
| Wrong theorem type | The functions swapped, equality alone, the stop condition on the target, `Src.f = Src.f`, a claim leaving out poison | `refused`, `claim_type_mismatch` |
| | The freeze attack: equality on a real `instcombine` run where both sides stop the model, with a proof that the source stops | `refused`, `claim_type_mismatch` |
| | A definition, named as the theorem | `refused`, `not_a_theorem` |
| | A predicate the certificate defines | `refused`, `foreign_constant` |
| | `sorry` | `refused`, `axiom_policy_failed` |
| | A false theorem added past the kernel with `debug.skipKernelTC` | `refused`, `kernel_replay_failed` |
| | A theorem name the certificate doesn't declare | `refused`, `theorem_not_found` |
| | A certificate that doesn't compile | `refused`, `certificate_compile_failed` |
| | A certificate importing `Lake` | `refused`, `certificate_imports_disallowed` |
| | A certificate whose code rewrites the generated target, adds a module named `IRLean` where Lean looks first, or adds a companion `.ir` file to `IRLean`'s library, while it compiles | `refused`, `artifacts_modified` |
| | A certificate whose code leaves a process running | `bound`, and the process is gone |
| | A `leanchecker` earlier on PATH that passes anything, with a certificate the kernel never saw | `refused`, `kernel_replay_failed` |
| | `ir_instance_refinement`, on this `IRLean` | `unsupported`, `claim_kind_unavailable` |
| | `pass_implementation`, `rewrite_all_inputs` | `unsupported`, `claim_kind_unverifiable` |
| What the model can't judge | A function reading memory | `unsupported`, `memory_unsupported` |
| | A function ir-lean refuses, on floating point | `unsupported`, `function_unsupported` |
| | An argument without `noundef`, and one named `%noundef` without it | `unsupported`, `undef_argument` |
| | A target marked `willreturn` | `unsupported`, `trusted_promise` |
| Limits | A certificate that sleeps past `--timeout 20`, and nothing of it left running | `unknown`, `time_limit` |
| | A certificate that allocates past `--memory 1500` | `unknown`, `resource_limit` |
| Uncovered changes | A run that also changes another function | `bound` about `f`, with `g` in `uncovered_changes` |
| Changed artifact | Target IR or certificate edited | `refused`, `artifact_hash_mismatch` |
| | Target IR swapped, with its hash updated | `refused`, `transform_replay_mismatch` |
| | Generated Lean edited, with its hash updated | `refused`, `translation_replay_mismatch` |
| | An extra field, a path outside the bundle | `refused`, `manifest_invalid` |
| Changed configuration | Another pass spec | `refused`, `transform_replay_mismatch` |
| | Another `-mtriple`, another data layout | `refused`, `config_mismatch` |
| | Another llvm-project commit, another source tree | `refused`, `llvm_pin_mismatch` |
| | Another ir-lean or checker | `refused`, `toolchain_mismatch` |
| Stale cache | A second run of the good bundle | `bound`, cache `hit` |
| | A certificate changed with its hash updated | Replayed and `refused`, cache `miss` |
| | An entry for another manifest, or another toolchain, at the key | Replayed and `refused`, cache `stale_ignored` |
| | A changed file, with a `bound` entry in the cache | `refused` before the cache is read |

58 cases took 298 s, one process at a time. Eight of them check the hash on small trees, without Lean: a library
hashes the same in another place, and a link out of it, a library that's a link, a link to a directory, a link out and
back in, a `..` through a link to somewhere else, and a checker that's a link to a writable file are errors, while
plain files, and this checkout's own, are accepted. `memory_limit` also comes back `unknown` without a systemd scope, from
Lean's `-M` alone, which was checked by hand. It isn't in CI, or in [testing](testing.md), yet.

No test reaches `function_not_found`, `function_not_generated`, `signature_mismatch`, `module_shadowed`, which the
directory listing stops first, or the `error` reasons.
