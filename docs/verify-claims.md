# Verifying claims about LLVM's passes

[`tools/verify_claims.py`](../tools/verify_claims.py) is [BIND-03](llvm-verification-tasks.md#bind-03-an-independent-verifier):
the independent verifier that decides when a claim in
[`tests/llvm_scope/coverage.json`](../tests/llvm_scope/coverage.json) counts. A claim's status and hashes are the
claimant's word. This replays its evidence, decides whether that evidence covers the pass in every context, and only
then does `tests/llvm_scope.py` count the claim toward `verified_done`. It's the verifier [binding a proof to LLVM's
C++](binding-approach.md#what-a-code-binding-claims-evidence-is) says G3 and G4 count with. For what any theorem means,
see [trust](trust.md).

Facts here were checked on top of `dbfd710` on 2026-11-09, on x86-64 Linux in the dev shell, with LLVM 23.1.3 at
`llvmorg-23.1.3` and Lean 4.35.0.

**Today it verifies no claim, because none can be complete yet.** `coverage.json` has no claims. Of the dimensions
a pass needs, all-input waits on the verifier reading [INV-04](llvm-verification-tasks.md#inv-04-rewrite-level-inventory)'s
lists of rewrites, which exist for chunk 1's four passes since #79 and which it doesn't read yet, code-binding on
[BIND-02](llvm-verification-tasks.md#bind-02-implementation-closure)'s complete closure of each pass, and composition
on [PASS-05](llvm-verification-tasks.md#pass-05-composition-through-pipelines)'s contract. The verifier refuses each
until it can decide it, naming what's missing. What it can do now is replay the evidence those claims
will be made of, theorems about functions compiled from the pinned source, and refuse evidence that isn't what it
says.

## Independent of the scorer

It shares no code with the scorer: not [`tools/verify.py`](verify.md), [`tools/binding.py`](llvm-proof-binding.md),
`tools/irlean` or the Lean checkers they run, `tools/verify_check.lean`, `tools/binding_check.lean` and
`tests/check_axioms.lean`. It's written against Python's standard library, and its Lean questions are in its own
[`tools/verify_claims_check.lean`](../tools/verify_claims_check.lean). It runs its own processes, hashes its own files
and reads the pin from `tests/llvm/targets.toml` and the inventory from `tests/llvm_scope/inventory.json` itself. So a
bug in the scorer's checks isn't a bug here too, unless both make the same mistake.

That makes it the one place Python grants a verdict without asking [`irlean.verdict`](trust.md#where-python-decides-a-verdict),
on purpose. Its verdicts are `replayed`, `verified`, `refused`, `partial`, `unknown` and `error`, none of which the
scorer uses, and [`tests/verify_claims_test.py`](../tests/verify_claims_test.py) checks how it reaches each.

## Evidence

A claim's evidence entry names a file in the repo and its SHA-256, as `coverage.json` always has. For the verifier,
that file is evidence in the form `ir-lean.claim-evidence/1`. Every object has exactly its keys: any other key, or a
missing one, is `evidence_invalid`.

| Field | Means |
| --- | --- |
| `llvm` | The llvm-project tag, commit and NAR hash. They have to be the pin in `tests/llvm/targets.toml` |
| `lean_version` | What `lean --version` printed when it was recorded |
| `units[]` | Each compiled source: `source`, in `llvm-project` or the `repo`, with `language` `c`, `c++` or `ir`; the build's `flags`, `include` directories in llvm-project, `local_include` directories in the repo and whether to add `llvm-config --includedir`; functions to `extract` with `llvm-extract`, if any; the Lean `namespace` and `ir-lean`'s `translate` options; and what replaying gives: `anchors`, every file of llvm-project clang read, `repo_files`, every file of the repo it read, and the SHA-256 of the IR and of the generated Lean |
| `lean` | `root`, a directory in the repo, `files`, its Lean modules with their SHA-256s, and `model`, the modules whose definitions a statement may use. A theorem's own module can be one, as each of `tests/llvm`'s is: then the definitions it states with are part of what the reader reads, and the verdict lists each constant a statement takes from the model, with its module |
| `theorems[]` | Each theorem's `module` and `name`, listed once, the symbols of the generated functions it's `about`, each defined in exactly one unit, and its `statement`, as the verifier prints it, with `statement_sha256`, a hash of its `Expr` |
| `cuts` | Calls out of the code a theorem rules out by stopping the model, as the [prototype](binding-approach.md#where-it-stops) does. Any cut makes the evidence `partial` |
| `contexts` | `"all"`, or the contexts it covers |

`tools/verify_claims.py evidence FILE --record OUT` fills in the hashes and statements by replaying, and writes the
evidence only if every other check passes. A statement copied from a recording always matches.

## The checks, in order

For evidence, the first that fails decides:

1. **Shape.** Exactly the schema's keys, and a unit's `flags` only ones that say how to compile: `-O`, `-D`, `-U`,
   `-std=`, `-f`, `-W` and `-m` flags, and none that loads code into clang or names a file, such as `-fplugin` or
   `-mllvm`.
2. **Cuts.** Any is `partial`, and nothing more is replayed.
3. **Pin.** The evidence's llvm-project is the pin, and `nix hash path $LLVM_PROJECT_SRC` gives its NAR hash.
4. **Anchors.** Before anything the evidence names runs, the toolchain, `IRLean`'s library, `ir-lean` and the
   verifier's own files are stamped with what `lstat` says of each entry, and compared at the end. clang compiles
   each unit from its own tree, with the source named relative to it, so the IR names no
   machine's path, and with `-MD`. The files of llvm-project it read are the unit's anchors, and they have to be
   exactly the recorded ones, each with its recorded SHA-256. A changed header is stale, and so is one left out.
5. **IR.** The IR, after `llvm-extract` if the unit names functions, is the recorded bytes.
6. **Translation.** `ir-lean` gives the recorded Lean, byte for byte, and its `--report` says which function is which
   Lean constant. A symbol a theorem is about has to be defined in exactly one unit, so which function it covers is
   plain.
7. **Lean.** Lean compiles the generated modules, then the evidence's own modules, copied from the repo with their
   recorded hashes, in the order their imports need. Their code runs while they compile, so first the run's directory
   is hashed.
8. **Statements.** `tools/verify_claims_check.lean` reads each theorem's module and its imports as data, with
   `importModules (loadExts := false)`, one module to a process, so none of their code runs there. Each theorem has to
   be declared in its module, as a theorem. Every module has to be read from where it should be: Lean's from the
   toolchain, `IRLean`'s from its library, the rest from the run's directory. Every constant its statement uses has to
   come from Lean, `IRLean`, a generated module or a module the evidence lists as the model, so nothing the reader
   wasn't pointed to can choose what the statement means. It has to name each generated function it's about, declared in that function's generated
   module. And its statement's `Expr`, written out so that two different `Expr`s never share the text, has to hash to
   the recorded `statement_sha256`, and print as the recorded `statement`.
9. **Axioms.** Every axiom a theorem rests on is `propext`, `Classical.choice` or `Quot.sound`, or one `bv_decide`
   adds: `verifyBVExpr formula certificate = true`, with both made of constructors and literals, rerun with the
   toolchain's own checker. `sorryAx` is reported as `sorry`.
10. **Kernel.** `leanchecker` replays every generated module and every module of the evidence's, one to a process.
11. **Unchanged.** The run's directory holds what it did, apart from each evidence module's new `.olean`, and nothing
    stamped has changed.

Every Lean process runs with `-M` and a thread stack of 64 MB, `-s 65536`, as `tests/llvm.py` gives it: Lean commits
about 1 GiB of stack for each thread, and `bv_decide` forks Lean to start its solver, which fails with `ENOMEM` on a
machine with less memory than that, such as a CI runner. Each runs by the toolchain's absolute path rather than
`elan`'s shim, and every process has a time limit, after which it's killed with everything in its session. A limit,
including running out of memory, is `unknown`, never `refused` or `replayed`.

For a claim, `tools/verify_claims.py claim` refuses before replaying anything a claim that isn't `complete`, covers
some contexts, lists gaps, or is about translation validation, which [never counts](llvm-verification-tasks.md#translation-validation-isnt-proof-for-all-inputs).
Then, by dimension:

| Dimension | Needs before any evidence can cover it | Then |
| --- | --- | --- |
| `code-binding` | The claim's anchors are the inventory's, and BIND-02's closure for the pass, `tests/llvm_scope/closure/PASS.json`, is complete | Every evidence file replays, with contexts `"all"`. The evidence reads every file of the closure at its hash, compiles every source the closure's functions come from, and has a theorem about every function in it, as compiled from that function's own file |
| `all-input`, `analysis-soundness` | INV-04's list of the pass's rewrites, or PASS-01's facts | Refused: the verifier doesn't read those lists yet. INV-04's exist for chunk 1's passes since #79, and PASS-01's don't |
| `composition` | PASS-05's contract for pipelines | Refused, for the same reason |

`tests/llvm_scope.py` asks it, through `VERIFIERS`, about each complete claim. It decides from the claim and the repo
itself, not from what `tests/llvm_scope.py` read.

## What it trusts

Lean's kernel, as `leanchecker` runs it, and the toolchain's `bv_decide` checker; IRLean's semantics and `ir-lean`'s
translation; the pinned clang, compiling the pinned source as the shipped LLVM was compiled; and whoever reads each
statement, and the model definitions it names, against what the claim says. Every verdict lists these. The evidence's
code isn't sandboxed while it compiles: a change to a file nothing stamps that a check reads, such as the Python
interpreter, or a process that leaves its session, isn't detected.

## What it was shown to do

[`tests/verify_claims_test.py`](../tests/verify_claims_test.py), in CI as `verify_claims_static` and `verify_claims`:

| Claims | Verdict |
| --- | --- |
| All 87 functions of LLVM's code `tests/llvm.py` proves, 63 units with their theorems, as one piece of evidence | `replayed` |
| The five controls `tools/verify.py` certifies in `tests/verification_negative`, each also proved by `tools/verify.py` in the same run | `replayed` |
| A complete code-binding claim for a pass, in a test inventory, whose closure is `__ashldi3` alone | `verified` |
| The same, with a function in the closure no theorem is about | `refused`, `closure_uncovered` |
| The same, with evidence for some contexts, or evidence changed since the claim | `refused`, `contexts_uncovered` or `stale_evidence` |
| A proof that sleeps past a 20 s limit | `unknown` |

The corpus took 139 s to replay with 2 Lean jobs, and the whole live tier 322 s with a peak of 4.9 GB, on 2026-11-09
on a 32-core machine. CI runs it in a job of its own.

And each forged claim, a good one with one thing broken:

| Forged | Verdict |
| --- | --- |
| A weaker hypothesis, another statement's hash, a statement printed differently | `refused`, `statement_mismatch` |
| A statement using a definition from a module the evidence doesn't list as the model, or about a function the proof names like the generated one | `refused`, `foreign_constant` |
| The source's hash changed, a header left out of the anchors, another llvm-project | `refused`, `stale_anchors` |
| A theorem resting on an axiom of its own | `refused`, `disallowed_axiom` |
| `sorry` | `refused`, `sorry` |
| A false theorem added with `debug.skipKernelTC` | `refused`, `kernel_replay_failed` |
| Other flags, an edited translation, an extra field | `refused`, `ir_replay_mismatch`, `translation_replay_mismatch`, `evidence_invalid` |
| A theorem listed twice, a flag loading a plugin into clang, and the function a closure needs also defined by hand-written IR, which could stand in for it | `refused`, `evidence_invalid` |
| A proof whose code rewrites a generated module, or adds a module where Lean looks, while it compiles | `refused`, `artifacts_modified` |
| A call cut out | `partial` |

And claims refused before any replay: partial and admitted claims, some contexts, gaps, translation validation, an
unknown pass, all-input and composition, stale anchors, anchors left out, and code-binding for a pass with no closure.

**A finding about the scorer.** `tools/verify.py` answers `timeout`, `heartbeat_limit` while reading the claim, on
`tests/llvm`'s proofs, such as `ashldi3_correct` with the IR the verifier compiled. So it proves none of them, though
`tests/llvm.py` does. The verifier's own checker hit the same limit printing large statements, and runs without
Lean's heartbeat limit, under its process's time limit.

## Limits

- Units are compiled and translated whole, or with `llvm-extract`. Linking a closure's files into one module is
  BIND-02's, and comes when a closure needs it.
- A code-binding claim's statement is pinned by its hash, not built from BIND-04's abstraction, which doesn't exist
  yet. The reader reads it, and the model definitions it names.
- The time and memory to replay grow with the evidence: the corpus above costs about what `tests/llvm.py` does without
  its mutants.
- A model module's definitions, and a theorem module's when it's listed as one, are read by a person. Nothing checks
  that a model is the C++ it stands for: that's what binding it, theorem 2, is for.
