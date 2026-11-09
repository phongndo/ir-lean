# Testing

How to run the checks, and what each one shows. For what the results add up to, see [status](status.md).

## Tests

The dev shell works on Linux and on Apple silicon Macs. The proofs compile for x86-64 Linux on every host, so
they check the same IR everywhere. On Macs, `lint` and `lsp` fail on C++ only: `clang-tidy` and `clangd` report
errors there that don't appear on Linux, so use `-LE 'lint|slow'` to skip them.

Run `lake build`, then `ctest --test-dir build`. Add `-LE slow` to skip `zlib_slow`. With that, on 32 cores, a first
run takes about a minute. A run with nothing changed takes about 4 s, apart from `llvm` and `superopt`, which check
everything every time, in about a minute.

`llama` needs llama.cpp's source, which only `nix develop .#llama` has, so it skips in the default shell. Run it with
`nix develop .#llama -c ctest --test-dir build -L llama`, which takes under 3 minutes with 6 Lean jobs.

| Test | What it checks |
| --- | --- |
| `opcheck` | Each integer operation against LLVM's constant folder, and against Alive2 for exact poison and UB behavior. `freeze` runs under two choices, and a result that depends on them is one any value refines. Fails without `alive-tv`, or if it can't check a variant. `--no-alive` is the opt-out. Prints Alive2's LLVM version and this code's |
| `gepcheck` | `getelementptr`'s flags against Alive2, on many layouts, since native code can't see poison pointers |
| `differential` | Emitted Lean against natively compiled code, on real C, and on [`choices.ll`](../tests/real/choices.ll)'s functions with a `freeze`, whose result under one choice is compared where it's what native code did, and otherwise skipped, since another choice could give that |
| `vectors_pointers` | The same for vectors, function pointers, pointers in globals and the heap, GEPs LLVM defines, and promises kept, failing if any input is skipped |
| `undefined` | Code LLVM calls undefined stops the model, since comparing with native code can't show that |
| `memory_errors` | Memory errors through the emitter each stop the model for their own reason: out of bounds, after a free, through a dangling pointer or the wrong provenance, null, misaligned, an overlapping copy, a write to a constant, and frees of what `malloc` didn't return |
| `model_stops` | Where LLVM doesn't say it's undefined, the model stops without an answer |
| `model_stops_are_not_undefined` | `--expect-ub` says those aren't undefined |
| `emitter` | What the emitter refuses and accepts on purpose, IR that fails LLVM's verifier, a value named like a name emitted code binds, checks only seen by running, what the model says of a run that never finishes under each [promise to progress](trust.md#promises-to-progress), proved of what it emits, that each `freeze` a run executes reads its own place in the run's `IRLean.Choice`, run under chosen ones, the default namespace, and that `opcheck` can't pass quietly without Alive2 |
| `fuzz` | The same comparison on random functions, optimized at random levels |
| `proofs` | The proofs against freshly generated Lean, that each theorem names its generated function, that breaking the C stops the proof with an error that isn't running out of time or memory, that a proof can only rest on the standard axioms and `bv_decide`'s, with no `implemented_by` or `extern`, and that `leanchecker` replays it |
| `llvm` | [LLVM's own code](llvm.md): functions from `llvm-project` at the pinned tag, compiled as upstream does, against their proofs, checked as `proofs` checks them, with an injected bug for each that has to stop its proof with an error of its own. Prints the score. `--manifest` writes what each theorem says and rests on, and what stopped each bug's proof |
| `llvm_scope` | The checks on [claims about LLVM's passes and the task list](llvm-verification-tasks.md), without LLVM: no claim counts as done without an independent verifier, finite translation validation never counts for all inputs, a stale hash or evidence outside the repo is refused, and the list's scope line matches the inventory. Python only |
| `llvm_scope_check` | The inventory of every name the pinned LLVM registers a pass or codegen implementation under, derived again from its source, `opt` and `llc`, and compared byte for byte, so the denominator can't move quietly. `llc` starts from `x86_64-unknown-linux-gnu` before `-march` sets each target, so macOS gives the same inventory as Linux. About 5 s, and no Lean |
| `corpus` | [The corpus](corpus.md)'s capture reads `opt`'s pipelines and traces right, and a corpus refuses a toolchain other than its own. `tools/measure.py` gives MiB on macOS and Linux, stops the whole process tree at a cap or timeout, and keeps its heavy-job lock exclusive, in the platform's cache directory. With the pinned `opt` on `PATH`, one seed is captured and each of its steps replays alone byte for byte. About 2 s, and no Lean |
| `superopt` | What a search finds for real functions, against Alive2 and a Lean theorem that names both and says they do the same, and that a wrong rewrite fails both, with an error in Lean and a counterexample from Alive2. An Alive2 timeout is never a pass. `--bench` also measures it against `clang -O3`, which CI doesn't, since timings vary |
| `x86` | x86's integer dot-product intrinsics and vector bitcasts against the processor, at every width, skipped without AVX-512 VNNI |
| `x86check` | The same intrinsics but VPDPBUSD, which nothing but the processor knows, and bitcasts between integers and vectors, on any processor: against Alive2, both ways, and LLVM's constant folder, poison included, with a wrong result for each that Alive2 has to refuse. About 2 s |
| `llama` | [llama.cpp's q4_K kernels](llama.md): that `llc` reproduces clang's code, the rewrite, that every change is in a slice and every other line is where it was, a Lean theorem for each slice, a native comparison of each if the processor can run it, and four wrong versions each refuted, by Lean proving a rewritten slice differs from clang's on an input, by every theorem stopping with an error of its own, or by the native comparison. A theorem that only runs out of time or memory is unknown, and refutes nothing. It needs llama.cpp's source, so it runs in `nix develop .#llama`, and skips elsewhere. CI runs it in two jobs: `llama` does everything but refute three of the four changes, which `llama_mutants` does, with `--mutants signs,seven,scale --no-theorems`. `tests/llama_bench.py` measures it on real inference, which CI doesn't |
| `llama_mutants` | The three wrong rewrites of `llama`, without its theorems, as CI runs them in a job of their own |
| `llama_bitspread` | The exact q5_0 integer slice against its replacement, including poison inputs and the defined byte value for every bit; regenerates Lean, audits axioms, and rejects a wrong-bit replacement without downloading a model |
| `llama_rewrite` | The q5_0 matcher against the committed IR fixture: it rewrites exactly the three sites into the committed helper, keeps every other line and outside users, and refuses a wrong shuffle lane, complement mask, flag, input width, layout, metadata or name, and a site count or function set other than the expected one |
| `llama_capture` | Complete raw-logit captures are accepted; changed bits, tokens, positions, prompts, truncation, and inconsistent metadata are rejected |
| `llama_evidence` | Committed timing rows agree with raw logs and generated output hashes; paired estimates and the pooled bootstrap reproduce without a model download |
| `names` | Every word Lean reserves is avoided in generated names |
| `undef_freeze` | [An experimental `undef` and `freeze` semantics](undef-freeze.md), not the model's: it builds with warnings as errors, LangRef's examples get LangRef's verdicts, four shortcuts each certify a wrong rewrite it rejects, both modules rest on the standard axioms and `leanchecker` replays them, two false proofs and a `sorry` are refused, five edits to a copy of it each stop the theorem they target, and Alive2 gives the same verdict on 31 rewrites. One process at a time, each Lean process capped at 2 GB, about 17 s of CPU |
| `freeze` | [`freeze` in the model](refinement.md#runs-that-make-choices), F3: ten rewrites, from `tests/freeze` and the `freeze` cases of `undef_freeze` without `undef`, translated, with a theorem for each proving its verdict about what ir-lean emits, on the standard axioms and replayed by `leanchecker`, a false proof that a duplicated `freeze` refines fails, and Alive2, with `undef` inputs off, gives each the theorem's verdict |
| `verify` | [`tools/verify.py`](verify.md) gives each status and reason when it should, refuses proofs that cheat, and no required check can be missing from a proved result |
| `prooftest` | [Tier-1 proof tests](proof-tests.md): in Python, the generators, shrinking, the store, and that nothing undecided, stopped or unconfirmed is a pass. Then `tools/prooftest/prooftest.py` on `tests/prooftest/Cases.ll`: a wrong spec shrinks to the least failing input, which the kernel refutes and the next run tries first, a buggy loop is refuted through `runFuel`, under a promise to progress and without one, a spec stated with `∃` is decided by running the call once, poison inputs, a call the kernel can't follow is confirmed by `tools/verify.py` instead, and a run that never ends, with a promise or without, memory, floating point, a statement about another function and a memory limit each come back unknown, a vacuous hypothesis vacuous, never a pass. At most four cases at a time |
| `prooftest_t1` | Milestone T1, with `tools/prooftest/bench.py --check-t1`: tier 1 on the 16 bugs `tests/proofs.sh` injects and on `tests/verification_negative`. Each one it can run is refuted, each one it can't comes back unknown, a true claim is never refuted, and the median time to a counterexample is under 100 ms. Two cases at a time |
| `verify_negative_static` | [What counts as a certificate](llvm-negative-verification.md): a stored proved result is certified, and broken, stale or mismatched ones aren't, nor answers from checkers that hang, crash or print nonsense. The runner reads a checker's peak memory, and what's free, in MB on macOS and Linux. Python only |
| `verify_negative` | Wrong LLVM rewrites, and right ones outside the model, are never certified through `tools/verify.py`, and five right ones are. Runs alone, one Lean process at a time, about 2 minutes |
| `replay_challenge_static` | [Challenging replay certificates](replay-challenge.md): manifests `tools/binding.py` has to refuse before it reads a tool, and its runner calling a crash, a timeout or running out of memory unknown, and leaving nothing running. A finding it shows is accepted as known, and the contract's answer too. Python only, about 4 s |
| `replay_challenge_alive` | The same: Alive2 agrees with LangRef, worked out by hand, on 17 poison and flag rewrites and every case in `tests/verification_negative`, with and without `undef` arguments, two disagreements have the reason given checked, and one is a known limit of Alive2's, checked too: it doesn't model `mustprogress`. A certified case Alive2 finds wrong fails. One capped `alive-tv` at a time, about 5 s |
| `replay_challenge` | The same: IRLean's model fails each poison and flag rewrite on exactly the inputs worked out by hand, which hold Alive2's counterexample, and `tools/binding.py` on real `opt` runs gives the reasons `binding` doesn't reach, with Alive2 agreeing with each bound bundle. Runs alone, one Lean process at a time, about 75 s |
| `binding` | [Binding a certificate to LLVM](llvm-proof-binding.md): one real `instcombine` rewrite is bound, and so is a real `loop-deletion` run that only `mustprogress` makes right, and four `instcombine` runs on `freeze` as refinements, and a certificate is refused, unsupported, unknown or an error, with the reason it should give, when its theorem's type, a file, the pass, the triple, the data layout, llvm-project, a tool or the cache doesn't match, when the model can't judge the function, and when a limit stops it. Never `bound` otherwise. Its cases are in two halves by a hash of each one's name, so a new case lands in one, and `binding` and `binding_2` each run one alone, one Lean process at a time |
| `binding_2` | The other half of `binding`'s cases |
| `passes_static` | [The scorer](passes.md)'s rules, without Lean: options on a `RUN` line other than where `opt` reads and writes are kept, not dropped, a cache entry saying `bound` or `certified`, or for another key or toolchain, is ignored, a bound instance is cached only as a candidate to verify again, and a verdict from `tools/binding.py` with another schema, manifest, claim kind or exit code is an error, never bound. Python only |
| `passes` | The scorer on three small tests in `tests/passes/`, not on llvm-project: seven wrong rewrites fail to prove and a right one is bound, two functions are bound and `tools/binding.py` binds their bundles again with no cache, memory and `undef` arguments are unsupported, a `RUN` line with another option is an unsupported run, a second run verifies cached instances again, a changed certificate is refused, a forged cache entry is ignored, a wall clock shorter than a proof takes, or a memory limit, makes an instance unknown. Runs alone, with `--jobs 2` and memory for three Lean processes, so the self-check tries three mutants at a time, and the three that run until Lean's heartbeat limit take as long as one |
| `contracts` | [Semantic contracts](llvm-semantic-contracts.md): LangRef's integer poison rules, as Lean predicates the model meets at every width. They build with warnings as errors, LangRef's poison examples hold, seven semantics LangRef rules out each fail their contract, both modules rest on the standard axioms and `leanchecker` replays them, a false proof and a `sorry` are refused, and five edits to a copy of `IRLean/Int.lean` each stop the theorem they target with an error that isn't a resource limit. One Lean process at a time, each capped at 2 GB, about 12 s |
| `refine` | [Refinement](refinement.md): `IRLean.Refines` builds with warnings as errors and rests on the standard axioms, right rewrites refine, `freeze` ones among them, and eleven known-wrong ones provably don't, deleting a loop refines under `mustprogress` and not without it, memory has no claim, the claim `tools/binding_check.lean` builds is the statement a certificate elaborates, a false proof fails, and four edits to a copy of the model each stop the case guarding them. One Lean process at a time, each capped at 2 GB, about 25 s |
| `cpp_correspondence` | [LLVM's C++](llvm-cpp-correspondence.md): a model of the pinned `simplifyAddInst`, proved right at every width, its quotes of the C++ at the pinned hashes and lines, with every code line quoted, and its answers against `opt -passes=instsimplify` on generated `add`s, with a changed quote, a missing one and two broken models each caught. One Lean process at a time, each capped at 2 GB, about 12 s |
| `generic_rewrites` | [Rewrites at every width](generic-rewrites.md): `IRLean.Generic` builds with warnings as errors, its uses at real widths hold, a counterexample shows each hypothesis and flag is needed and each refinement isn't an equality, every module rests on the standard axioms and `leanchecker` replays it, two false rewrites and a `sorry` are refused, and five edits to a copy of `IRLean/Int.lean` each stop the theorem they target with an error that isn't a resource limit. One Lean process at a time, each capped at 2 GB, about 20 s |
| `store` | [The lemma store](lemma-store.md): `tools/store/store.py check` passes, so every stored lemma rests on the standard axioms with its module replayed by `leanchecker`, is stated for every width, has a counterexample for each hypothesis, and meets the other admission checks, and the index's status for each is right. Lookup finds lemmas under five restatements and at two real widths, `store.py add` refuses a `sorry`, an extra axiom, a `bv_decide` proof, a fixed width, a hypothesis with no counterexample, a counterexample proved by `sorry`, a duplicate after normalization and a false statement, and a lemma already in `IRLean` whose hypothesis nothing needs, and accepts a good lemma, `grind +suggestions` proves two goals from the store that plain `grind` doesn't, and a proof from the store and one without it both check, with the axioms each should have. Reads what `lake build` built. Two Lean processes at a time, each capped at 4 GB |
| `needs_tests` | [`.github/needs-tests.py`](#skipping-the-tests), which lets a pull request skip CI's test jobs: 15 changes in a scratch git repo each get the answer given, the three documents tests here are known to read each have a reader it finds, and the scripts it leaves out as the lint job's are what the tests labeled `lint` run. About a second, and only git |
| `zlib` | All of zlib translates, and real calls into it match native code, failing if any input is skipped |
| `zlib_slow` | The same for the calls that slide `deflate`'s window, the slowest of them |
| `lint` | Every formatter and linter below, for every language |
| `lsp` | Every language server below starts, opens real files, and reports no errors in them |

The dev shell sets `CTEST_PARALLEL_LEVEL`, how many tests run at once, and `LEAN_JOBS`, how many Lean processes
each runs at once, from the machine's cores and memory. Compiled modules stay in `build/lean-cache`, so a run only
recompiles what changed. `proofs` keeps its compiled modules and the checks that passed in `build/proof-cache`, and
the other tests keep what Lean printed and what Alive2, `clang-tidy` and the language servers passed in
`build/result-cache`. These are named after everything they read, so a test only repeats what could come out
differently, and only a pass is kept. CI doesn't keep those two directories, so it works everything out on every
run. To do the same locally, delete them.

`tests/bench.py` times what you wait for after each kind of change, from a cold build to an edit to the model, with
real edits it undoes afterwards.

`tests/proof_bench.py build/ir-lean` times checking each proof on its own, against the Lean the tests generate, and
the peak memory each one takes. `--llvm CrtUdivmoddi4` adds a target's proof, and `--proof Crc32=FILE` checks another
version of a proof on the same obligations, so two versions can be compared. [Status](status.md#what-checking-costs)
has what it measured.

## CI

`.github/workflows/ci.yml` runs on every pull request and push to `main`. Each job sets up on a runner of its own,
with 4 cores and 16 GB, and the jobs run at once:

| Job | Runs |
| --- | --- |
| Formatters, linters and language servers | The tests labeled `lint`: `lint` and `lsp` |
| Tests and proofs (`passes`) | `passes` |
| Tests and proofs (`binding`) | `binding`, half of `tests/binding.py`'s cases |
| Tests and proofs (`binding_2`) | `binding_2`, the other half |
| Tests and proofs (`llvm`) | `llvm` |
| Tests and proofs (`semantics`) | `replay_challenge`, `contracts`, `refine`, `undef_freeze`, `freeze`, `generic_rewrites`, `cpp_correspondence`, `store`, `prooftest` and `prooftest_t1` |
| Tests and proofs (`llama`) | `llama`, in `nix develop .#llama`, the only shell with llama.cpp's source: the 34 theorems, the native comparison, and the change to the mask |
| Tests and proofs (`llama_mutants`) | `llama_mutants`, in `nix develop .#llama`: the three wrong rewrites |
| Tests and proofs (`proofs`) | `proofs`, and then `verify_negative`, which runs alone |
| Tests and proofs (`rest`) | Every other test, apart from `zlib_slow` |
| Slow zlib tests | `zlib_slow`, on pushes to `main` |

Each test job but `rest` is named after a ctest label set in `CMakeLists.txt`, and runs the tests with it, through
`.github/test-shard.sh`. `rest` runs every test without one of those labels, `lint` or `slow`, so a new test runs
there with nothing more to do. To give a long test a job of its own, label it, and add the label to the matrix in
`ci.yml`. Before it runs anything, `rest` checks that CI runs each test exactly once, and fails if a test would run
in two jobs.

[Run 42572895262](https://github.com/phongndo/ir-lean/actions/runs/42572895262), on 2026-11-09, was #65's last pull request run, with #61, #63 and #64 already on
`main` and merged in. It took 8.0 minutes:

| Job | Setting up | ctest | The job |
| --- | --- | --- | --- |
| Which jobs the change needs | | | 5 s |
| Formatters, linters and language servers | 93 s | 94 s | 3.4 min |
| Tests and proofs (`passes`) | 87 s | 300 s | 6.5 min |
| Tests and proofs (`binding`) | 86 s | 126 s | 3.6 min |
| Tests and proofs (`binding_2`) | 89 s | 273 s | 6.1 min |
| Tests and proofs (`llvm`) | 102 s | 291 s | 6.6 min |
| Tests and proofs (`semantics`) | 98 s | 319 s | 7.0 min |
| Tests and proofs (`llama`) | 91 s | 277 s | 6.2 min |
| Tests and proofs (`llama_mutants`) | 96 s | 350 s | 7.5 min |
| Tests and proofs (`proofs`) | 77 s | 287 s | 6.1 min |
| Tests and proofs (`rest`) | 90 s | 357 s | 7.5 min |

Three pull request runs earlier that day, each with some of the other changes and none of #65's, took 11.7, 12.8 and
16.6 minutes: A, [42566328921](https://github.com/phongndo/ir-lean/actions/runs/42566328921), #61's, B,
[42566758308](https://github.com/phongndo/ir-lean/actions/runs/42566758308), #63's first, and C,
[42567711827](https://github.com/phongndo/ir-lean/actions/runs/42567711827), #64's with #61 merged in. They ended with
`binding`, `llama` and `passes`. Two of #65's own runs in between, with the jobs split and `passes` not yet changed,
took 11.0 and 11.2 minutes, [42568552495](https://github.com/phongndo/ir-lean/actions/runs/42568552495) and
[42570803347](https://github.com/phongndo/ir-lean/actions/runs/42570803347), ending with `passes`. And #53's own three
runs took 12.8 to 15.8 minutes. These are samples, and times vary with the runner: `passes` alone took 473 to 839 s of
ctest in A to C. C1 asks for the median of 20 consecutive pull requests, so one run doesn't reach it.

What set each job's time before, in runs A to C unless it says otherwise, and what changed it:

| Job | Before | What changed |
| --- | --- | --- |
| Setting up | 101 to 132 s in [42557512002](https://github.com/phongndo/ir-lean/actions/runs/42557512002), [42557742359](https://github.com/phongndo/ir-lean/actions/runs/42557742359) and [42557663688](https://github.com/phongndo/ir-lean/actions/runs/42557663688), after #53, with alive2 built from source in every job | alive2 from a cache of its own, in #61. 77 to 102 s in run 42572895262 |
| `binding` | 451 to 621 s of ctest, 59 cases one at a time, each hashing the toolchain and llvm-project | Less hashing, in #63, and two jobs, in #65 |
| `passes` | 473 to 839 s, the scorer's self-check trying seven mutants one at a time, three of them to Lean's heartbeat limit | Those three at once, in #65 |
| `llama` | 420 to 635 s, 190 of its 231 s locally refuting four mutants | Three of them in a job of their own, in #65 |
| `rest` | 419 to 495 s, with `proofs` at 357 s in A next to three others | `proofs` in a job of its own, in #65 |
| `semantics` | 314 to 396 s, two tests that run alone after five others, and 402 s in 42570803347 once #60 added `store` | `verify_negative` in the `proofs` job, in #65 |

### Proposals, not done

These change how merging and `main` work, so they're the maintainer's to decide. As of 2026-11-09:

- **Branch protection, or a merge queue.** `main` has no protection rules: a pull request can merge with a red check,
  and one green against an older `main` can merge without a run against the newer one. A rule requiring the test jobs
  and lint stops the first. Since a skipped job counts as passed, a pull request that skips the tests still merges. A
  rule requiring branches to be up to date stops the second: a pull request that's fallen behind has to merge `main`
  in and pass again before it merges, one more run of about 8 minutes, and with four or five lanes merging the same
  day, most fall behind. A merge queue checks the same thing without the manual update: it runs CI on each queued pull
  request merged onto `main` and the ones ahead of it, can build several at once, and merges each when it's green. But
  GitHub offers merge queues only to repositories an organization owns, and this one is a user's, so it would first
  have to move to an organization. It would also need `merge_group` among `ci.yml`'s triggers, and the slow zlib job,
  which runs on every event but `pull_request`, would then run on each queued merge too, unless its condition changes:
  2.9 minutes in [42570671573](https://github.com/phongndo/ir-lean/actions/runs/42570671573), shorter than the test jobs. Either rule catches two pull requests that
  pass alone and break together, as #63 and #65 would have on 2026-11-09: #63 added a local variable `zlib` to
  `tests/binding.py`'s `main()`, where #65 called `zlib.crc32`. It was caught by hand, merging them.
- **Moving tiers to nightly runs.** C1 doesn't need it now: the longest job in run 42572895262 took 7.5 minutes. If
  the median passes 10 minutes again, the candidates are the longest single tests, such as `llama_mutants`, `passes` or
  `binding_2`, each moved with its reason written down, as [Phase 8](roadmap.md#phase-8-speed) asks, and still run on
  `main` and nightly. The cost: a regression in a moved test shows on `main` after the merge, not on the pull request,
  when the lane that caused it may have moved on.
- **Testing every commit on `main`.** `ci.yml`'s `concurrency` groups runs by branch, and cancels a running pull
  request run when its branch gets a new push. On `main` it lets the running one finish, but GitHub keeps one pending
  run per group, and a newer push replaces it. Of the 25 commits on `main` from `2bf52f0` to `a216ce1`, 2 never had a
  run finish: `de2825e` and `a26abb3`, each cancelled by a later push within minutes. And a run waits for the one
  before it: [42570671573](https://github.com/phongndo/ir-lean/actions/runs/42570671573), for `a216ce1`, started its jobs at 06:17:09, a second after `a77fda7`'s run
  ended, and finished 26 minutes after its push, though its longest job took 11.1. A group of its own for each push to
  `main`, such as `${{ github.workflow }}-${{ github.ref }}-${{ github.event_name == 'push' && github.sha || '' }}`, runs every
  commit at once. The cost is runners: each run on `main` now has 12 jobs, the slow zlib one included, which compete
  with pull requests' runs for the account's concurrent jobs. In three overlapping pull request runs on 2026-11-09,
  about 25 jobs at once, none waited more than 3 s for a runner. A merge queue would make this unneeded, since every
  commit to `main` would then be one CI ran on.

### Setting up

`.github/actions/setup` installs Nix, restores the caches, sets up the dev shell, and builds `build/ir-lean` and the
Lean library. Three downloads in it have failed a run:

| When | What failed | What happens now |
| --- | --- | --- |
| 2026-11-09, [run 42555906703](https://github.com/phongndo/ir-lean/actions/runs/42555906703/attempts/1) | The Nix installer's download of `nix-2.35.4-x86_64-linux.tar.xz` from releases.nixos.org: nothing for a minute, then a TLS "unexpected eof" | Every `curl` in the job reads `$RUNNER_TEMP/.curlrc`, which tries a download six times, and gives up on a try after 30 s without a connection or below 1 kB/s for 30 s. The installer runs `curl` once for the tarball and has no option for retries, so this is the one place to add them. It checks the tarball's SHA-256, so a bad download still fails |
| 2026-11-08, runs [42473433450](https://github.com/phongndo/ir-lean/actions/runs/42473433450) and [42473641335](https://github.com/phongndo/ir-lean/actions/runs/42473641335) | alive2's source from GitHub, HTTP 504 on all four tries, while Nix set up the dev shell | alive2 comes from a cache of its own, so its source isn't downloaded, and the dev shell, and the job's own if it has one, such as `.#llama` with llama.cpp's source from GitHub, are each set up up to three times, 30 s and then 60 s apart |
| Reported, with no run found among the latest 200 | HTTP 416 from cache.nixos.org while Nix set up the dev shell | The same three tries. What Nix finished stays in the store, so a second try only does the rest |

Retrying the whole install step instead would have to reason about what a failed install left behind, and the
installer fails on the download before it changes anything, so retrying the download itself is the smaller change.

alive2 is built from source, since cache.nixos.org doesn't have it on this LLVM, which took about 73 s of every job's
setup. After the first job builds it, `nix-store --export` writes it to `~/.cache/ir-lean-alive2`, 1.2 MB, with the paths it
depends on. The lint job saves that under a key naming `flake.lock`, `flake.nix` and `nix/`, so a change to anything
Nix builds it from builds it again. Other jobs fetch what it depends on from cache.nixos.org, as for the rest of the
shell, and `nix-store --import` it. That's unsigned: the cache is trusted as the toolchain and the library the jobs
restore are, and a pull request's run only ever saves a cache its own runs can read. If the import fails, Nix builds it.

### Skipping the tests

A job, "Which jobs the change needs", runs first and decides with `.github/needs-tests.py`. A pull request skips the
test jobs only when every file it changes is Markdown it adds or edits, and no file in the repo that isn't Markdown
names that file, ignoring case. Tests read a document by naming it:

| Document | Read by |
| --- | --- |
| `docs/llvm-verification-tasks.md` | `tests/llvm_scope.py`, which parses the task list |
| `docs/llvm-cpp-correspondence.md` | `tests/cpp_correspondence.py`, which checks its anchors |
| `docs/verify.md` | `tests/verify.py`, which checks it names every status and reason |
| Any document `tests/llvm_scope/coverage.json` gives as evidence | `tests/llvm_scope.py`, which checks the evidence's hash |
| Every Markdown file | `tests/lint.sh` and `tests/lsp.py`, the lint job's, which runs on every pull request |

A name in a comment counts too, so as of 2026-11-08 only `docs/llama-q5.md`, `docs/prior-art.md`, `docs/roadmap.md` and
new documents can skip the tests. Removing or renaming a file always runs them, since a test can check that a file it
was told about exists. The rule only sees names: a test that read every document by a pattern would have to be added to
it. Lint runs either way, and pushes to `main` and manual runs run everything. A skipped job counts as passed for a
required check, so the tests are skipped only when that job says so: if it fails, they run. `needs_tests` tests the
rule, and fails if the documents above stop having readers it finds.

## Formatters, linters and language servers

| Language | Formatter | Linter | Language server |
| --- | --- | --- | --- |
| C++ | `clang-format` | `clang-tidy` | `clangd` |
| C test inputs | `clang-format` | `clang -Wall -Wextra` | `clangd` |
| Lean | None exists | Lean's own linters, with `lake build --wfail`, and warnings as errors in `tests/llvm.py` | `lake serve` |
| Python | `ruff format` | `ruff check`, `ty check` | `ty server`, `ruff server` |
| Shell | `shfmt` | `shellcheck` | `bash-language-server` |
| Nix | `nixfmt` | `statix`, `deadnix` | `nixd` |
| CMake | `gersemi` | `cmakelint` | `neocmakelsp` |
| TOML | `taplo fmt` | `taplo lint` | `taplo lsp` |
| YAML | `yamlfmt` | `actionlint` | `yaml-language-server` |
| Markdown | `rumdl fmt` | `rumdl check` | `rumdl server` |
| LLVM IR test inputs | None exists | `opt -passes=verify` | None exists |

`tests/lint.sh` runs them all, and `tests/lint.sh --fix` has the formatters rewrite what they can.
`editorconfig-checker` also checks whitespace in every file, which is the only check on how Lean files are
laid out. CI runs all of this, the tests and the proofs on every pull request and push to `main`, and
`zlib_slow` on pushes to `main`. To run `zlib_slow` on a branch before merging it, use
`gh workflow run CI --ref BRANCH`.

Python scripts need nothing beyond the standard library, and run through `uv`, which also pins `ruff` and
`ty` in `uv.lock`.

`clangd` needs `build/compile_commands.json`, which `cmake` writes. To open the proofs in an editor, first
run this, so the language server can find the generated modules they import:

```console
tests/proofs.sh build/ir-lean --generate build/generated
```
