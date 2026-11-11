# Bug classes

The kinds of bug this repo has had more than once, where each showed up, what guards against it now, and what will.
[The process](process.md) reads from this: a design names the classes it touches, a reviewer reads this beside the
change, a finding is sorted into its class before it's fixed, and a class seen twice gets one guard before more
feature work. Facts here were checked on 2026-11-10, at `f140938`.

A class is closed when one guard covers every case of it and a test fails if anything gets around the guard. None is
closed yet.

## 1. A limit or a failure counted as a pass

A run that stopped at a time or memory limit, crashed, stopped the model, or failed to compile is read as a success,
or quietly dropped from what a pass is counted over. The rule since [#105](https://github.com/phongndo/ir-lean/pull/105)
is that only clean evidence gives a positive verdict, and each tool applied it on its own.

- **Seen in:**
  - [#51](https://github.com/phongndo/ir-lean/pull/51): a scorer counted cached results whose certificates were gone.
  - [#57](https://github.com/phongndo/ir-lean/pull/57): a crashed native check counted as catching a wrong rewrite,
    and a slice that failed to compile counted as a refutation.
  - [#91](https://github.com/phongndo/ir-lean/pull/91): running out of memory.
  - #105: unclean evidence.
  - [#111](https://github.com/phongndo/ir-lean/pull/111): a failed proof forging a counterexample.
  - [#115](https://github.com/phongndo/ir-lean/pull/115): `tests/cut.sh` reading limits from Lean's messages.
  - [#117](https://github.com/phongndo/ir-lean/pull/117) S9: crashed timing runs counted as faster.
  - [#118](https://github.com/phongndo/ir-lean/pull/118) S1: model stops dropped as inputs that didn't meet the
    hypotheses.
- **Still open:** a hand-written proof-test property drops model stops the same way. Only the equivalence form is
  guarded.
- **Guard now:** `irlean.proc` treats a limit as never a success, and `irlean.verdict.decide` is used by some tools.
  Eight places decide a verdict, each with its own statuses and reasons.
- **Guard planned:** stage A, one place that decides every positive verdict, default-deny. Its design,
  `docs/verdicts.md`, is under review.
  A test runs every combination of evidence that isn't clean through every tool's mapping, and a lint fails if
  anything outside `tools/irlean` sets a positive status.

## 2. A check, then a use of something else

Something is checked, and then a later step reads a file again by its path, and gets something else: the files
audited aren't the files replayed, or the IR certified isn't the IR translated.

- **Seen in:**
  - [#109](https://github.com/phongndo/ir-lean/pull/109), rounds 2 to 5:
    - the axiom audit and the kernel's replay read different modules;
    - the generated checker could be replaced before Lean read it;
    - an editor could change the IR during translation, then undo;
    - an inherited `LEAN_SYSROOT` pointed the replay at another toolchain.
  - #117 S5: a session run again under a copied plan.
- **Guard now:** certify works in a private directory, with each file bound by its hash and `lstat` as it's written,
  since #109. That's the pattern. [The gates' promise](rules.md#what-the-gates-promise) says what's in scope.
- **Guard planned:** stage C, one content-addressed work area in `tools/irlean`. A step reads its inputs by hash, and
  writes each output once.

## 3. Reading another tool's text

A tool's printed output, or a free-form string, is read with patterns, and a form the pattern misses gets through.

- **Seen in:**
  - #109 S6: new value names collided with existing ones, twice. `tools/rules/ir.py` reads and rewrites IR with
    regular expressions.
  - #115, rounds 2 to 4: `tests/cut.sh` told a limit from an error by grepping Lean's messages.
  - [#116](https://github.com/phongndo/ir-lean/pull/116) S7: the rule pinning files of ours read command strings,
    and `env -C {repo}`, then `{repo}/`, got around it.
  - #117 S2, three rounds: data next to the code was compared from `objdump`'s text.
- **Guard now:** none shared.
- **Guard planned:** stage B. IR and machine code go through LLVM's C++ API, in subcommands of `build/ir-lean`,
  which already links it. A file of ours is named by a structured field, not found in a string.

## 4. Two sources of truth, or a reader that skips the check

The same fact is defined in two places that can disagree, or one entry point validates a file and another reads it
without validating.

- **Seen in:**
  - #116 S8 and S9: the lock's record was checked by one command and not by others.
  - #117 S6: the board took a comparison's word for which workload a session measured.
  - #117 S11, S12 and `decompress`: the corpus's manifest and the harness's `harness.toml` each defined workloads and
    their checks.
- **Guard now:** `kernels.validate`, which every command that measures or records demand calls, since #116.
- **Guard planned:** stage D. Each data file has one loader that validates it, and the manifest is the only place a
  workload is defined.

## 5. A check that doesn't run the code it checks

A correctness check passes whatever the code under test does, because it builds or runs something else.

- **Seen in:**
  - [#106](https://github.com/phongndo/ir-lean/pull/106): before it merged, the cancel test passed even when irl
    killed the call with SIGKILL.
  - #116 S1: the perplexity check never ran the GEMV kernels.
  - #116 S5: Argon2id's timed run used the checking build.
  - #117 S1: xxHash's `make check` rebuilt with its own flags.
  - #117 S12: xxHash's dispatch test compiled its own copy of the rewritten unit.
- **Guard now:** each of those was shown fixed by a planted bug that the check catches: a GEMV that adds 1.0, a
  flipped bit in `XXHL128_default_avx512`, a changed lane of CRC-32's folding constant.
- **Guard planned:** a rule. A check counts only once a planted bug in the code it checks is shown to fail it, and
  that test stays.

## 6. A total that hides a failing part

A figure made of parts, or a count made of kinds, is judged as a whole, and one bad part hides inside it.

- **Seen in:**
  - #117 S11: xxHash's four rates averaged, so one hash 10% slower hid behind another 50% faster.
  - #118 S1: model stops counted among the inputs discarded.
  - #116 S2: perplexity's output, rounded and clipped before it was compared.
- **Guard now:** each case fixed on its own: each hash judged by itself, and model stops counted apart.
- **Guard planned:** a rule. Each part is judged on its own, and every input or run left out is counted by why.

## 7. An answer that changes from run to run

The same question gets a different verdict on another run or machine, so a pass can't be reproduced.

- **Seen in:**
  - [#92](https://github.com/phongndo/ir-lean/pull/92): LLVM's verifier probing `jumptable` at a call.
  - [#113](https://github.com/phongndo/ir-lean/pull/113): Alive2's 10 s query limit on a loaded CI runner made a
    proof unknown.
- **Guard now:** each case fixed on its own. A timeout gives `unknown`, never a pass, by class 1, so this costs
  reruns, not wrong answers.
- **Guard planned:** CI runs the verdict tests twice, and fails if any verdict differs.
