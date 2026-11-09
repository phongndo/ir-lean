# Negative verification

Wrong optimizations, unknown answers and stale results must never count as proof. `tests/verify_negative.py` checks
that, on a small corpus of LLVM rewrites in
[`tests/verification_negative/`](../tests/verification_negative/). Most of the rewrites are wrong, or right only
outside what the model covers. A few are right and have to be certified, so the rest can't pass just because
everything fails. For what any theorem here means, see [trust](trust.md). For the checker it runs, see
[verify](verify.md).

**This proves no optimization.** Each certified case is one rewrite, on one pair of 8-bit functions written by hand.
It says nothing about the LLVM pass that would make that rewrite, about other inputs to the pass, or about native
code. The corpus tests the checking, not LLVM.

Facts here were checked at commit `18421be` on 2026-11-08, on x86-64 Linux in the dev shell: Lean 4.35.0 (`eb6cafb`),
Lake 5.0.0, clang, `opt` and LLVM 23.1.3, Python 3.14.8, nixpkgs `1d06008`.

## Running it

From the repo, after `lake build` and building `build/ir-lean`, in `nix develop`:

```console
tests/verify_negative.py                  # both tiers, then the blocked list
tests/verify_negative.py --tier static    # Python only: no Lean, no build
tests/verify_negative.py --only freeze_duplicated stub_hang
tests/verify_negative.py --list
```

Each run writes `report.json`, and for each live case the request, what `tools/verify.py` printed and the envelope
the gate read, under `build/verify-negative/`, which keeps the last 5 runs. `--out DIR` puts them elsewhere.

| Exit | Means |
| --- | --- |
| 0 | Every case came out as expected |
| 1 | A case didn't: a wrong rewrite certified, a control not certified, or a case refused for another reason than the one it's about |
| 2 | A usage or manifest error |
| 3 | A case couldn't run, such as without the toolchain or enough free memory. That's never a pass |

A refused case has to be refused for its own reason. A broken toolchain refuses everything, so a negative case
that's refused for another reason fails, and the controls fail too.

## The claim

A case is `src`, before an optimization, and `tgt`, after it, as LLVM IR. Its claim is that `tgt` refines `src`
on every input, poison included. That's this statement, which the runner writes into the request from the case's
`claim`, so a manifest can't drift to a weaker one:

- undefined behavior in `src` allows anything;
- a `src` that never finishes needs a `tgt` that never finishes;
- a poison result from `src` allows any result;
- a value allows only itself;
- anything else allows nothing, a model stop in `src` above all, since the model doesn't know what LLVM does there.

Equality, `tgt x = src x`, isn't refinement, and isn't safe as a claim. It lets a model stop in `tgt` match the same
stop in `src`. [`freeze_duplicated_equality_pin`](../tests/verification_negative/cases/freeze_duplicated_equality_pin/)
is a wrong rewrite that Lean proves equal, since both sides stop at a frozen poison. The gate refuses it.

The statement only names Lean, `IRLean` and the generated module, so it can be pinned. A `match` would make an
auxiliary definition in the proof module, and `tools/verify.py` never lets a pinned statement name one of those.
It's decidable, so a witness can be decided by running it. It lists the reasons for undefined behavior rather than
the model stops, so a reason added to `IRLean.UB` later makes it stricter, never weaker. `noProgress` and `noReturn`,
which SEM-07 added on 2026-11-08 for a broken promise to progress or to return, aren't listed, so a `src` that breaks
one allows nothing here, which is stricter than `IRLean.Refines`. It's a stand-in for an
`IRLean.Refines` that isn't on `main` yet: see [blocked](#blocked-integration-cases).

## The live cases

Each runs `tools/verify.py` on its own copy of the case's files, one at a time.

| Case | Rewrite | LLVM says | `tools/verify.py` says | Certified |
| --- | --- | --- | --- | --- |
| `control_mul2_to_shl1` | `mul X, 2` to `shl X, 1` | Right | proved | Yes |
| `control_drop_nsw` | `add nsw X, 1` to `add X, 1` | Right | proved | Yes |
| `control_freeze_noundef_removed` | `freeze X` to `X`, for `noundef` X | Right | proved | Yes |
| `control_precondition_sufficient` | `(X << 1) >> 1` to `X`, for X < 128 | Right | proved, and the probe meets X < 128 | Yes |
| `wrong_mul2_to_shl2` | `mul X, 2` to `shl X, 2` | Wrong at 1 | counterexample | No |
| `poison_add_nsw_introduced` | `add X, 1` to `add nsw X, 1` | Wrong at 127 | counterexample | No |
| `freeze_removed` | `freeze X` to `X` | Wrong at poison | counterexample, the model's | No |
| `freeze_duplicated` | One freeze used twice to two freezes | Wrong at poison | counterexample, the model's | No |
| `freeze_duplicated_equality_pin` | The same, claimed as equality | Wrong at poison | proved | No: `pin_mismatch` |
| `freeze_added_unmodeled` | `X` to `freeze X` | Right | counterexample, the model's | No |
| `undef_in_target` | `sub X, X` to `undef` | Wrong | unsupported | No |
| `float_fadd_zero_removed` | `fadd X, 0.0` to `X` | Wrong at -0.0 | unsupported | No |
| `precondition_insufficient` | `(X << 1) >> 1` to `X`, for X < 200 | Wrong at 150 | counterexample | No |
| `precondition_vacuous` | The same, for X < 0 | Says nothing | proved | No: `hypotheses_unwitnessed` |
| `proof_for_other_target` | A proof about one `tgt`, given for another | Wrong | `statement_not_about_target` | No |
| `malformed_proof` | The control, with its proof cut off | Right | `proof_failed` | No |
| `unpinned_statement` | The control, with no statement pinned | Right | proved | No: `unpinned` |
| `resource_heartbeats` | The control, with `maxHeartbeats 1` | Right | timeout | No |
| `resource_memory` | The control, with 300 MB | Right | timeout | No |
| `resource_wall_time` | The control, after a 2-minute sleep, with 20 s | Right | timeout | No |
| `wrong_loop_deleted` | A loop that never ends, deleted | Wrong at 0 | timeout: deciding it runs `src` forever | No |
| `wrong_promise_added` | `mustprogress` added to a function whose loop never ends at 0, with the proof that trusting it allowed | Wrong at 0 | `proof_failed`: `tgt` breaks the promise at 0 | No |
| `stale_input` | The control, certified, then its IR edited | Right | proved | No: `stale_input` |
| `stale_proof` | The control, certified, then its proof edited | Right | proved | No: `stale_proof` |

"LLVM says" is what LangRef's rules give, worked out by hand for each case and written in its `case.json`. Nothing
here checks it, and Alive2 wasn't run on these. A counterexample marked "the model's" involves a model stop: it's
a counterexample to the claim in the model, and not necessarily one in LLVM. `freeze_added_unmodeled` is a right
rewrite that the model refutes, since its `tgt` stops at a frozen poison. It stays uncertified, rather than
certified by a semantics for `freeze` the model doesn't have.

A precondition can be unsatisfiable, and then the theorem is true and says nothing. So for a claim with
hypotheses, the runner also asks `tools/verify.py` to refute `∀ x, hypotheses → tgt x ≠ tgt x` at the case's
`precondition_witness`. Only a counterexample, from a checker that exited as one does, without a signal or the
watchdog, shows an input meets the precondition, and only then is the claim certified.

## The static cases

These need only Python. They take the stored result of `control_mul2_to_shl1`,
[`fixtures/control_result.json`](../tests/verification_negative/fixtures/control_result.json), which the gate has to
certify, and break it one way at a time: half the JSON, another schema, each other status, a status that doesn't
match its reason or exit code, an exit code of `false`, which Python calls equal to 0, a required check that failed,
was skipped, is missing or appears twice, a counterexample, another function, no pin, a weaker pin, a claim that
leaves out `src`, an undeclared hypothesis, every input hash, and every version. They also run the runner on
checkers that hang, crash, get killed, print nonsense, print nothing, or print a proved result and exit 1.

The precondition probe gets the same treatment, from the stored result and probe of
`control_precondition_sufficient`, in
[`fixtures/precondition_envelope.json`](../tests/verification_negative/fixtures/precondition_envelope.json): certified
as it is, and not with the probe missing, exiting or crashing, timed out, without a failing witness, with another
status or exit code, for another statement, or for other IR. A last case fails if any reason the gate can give
isn't one some case expects.

`tests/verify_negative.py --write-fixture` reruns the two controls and stores their results, with the run's paths
taken out. A static control fails with `stale_input` or `stale_proof` if its case's files change and its fixture
doesn't.

## The gate

`gate` in `tests/verify_negative.py` decides what counts. It reads an envelope: what `tools/verify.py` printed, how
its process ended, the hashes of the checker's own files when it ran, and the precondition probe. A result is
certified only if the gate finds no reason to refuse it, and any field it can't read is a reason.

| Reason | Means |
| --- | --- |
| `harness_timeout` | The runner's watchdog killed the checker |
| `harness_killed` | The checker was killed, as the OOM killer does |
| `harness_crash` | The checker died with another signal |
| `result_unreadable` | The checker printed no JSON object |
| `result_malformed` | The result is JSON, without the fields or types a result has |
| `schema_mismatch` | The result's schema isn't `ir-lean.verify/1` |
| `not_proved` | The status isn't `proved` with reason `kernel_checked` |
| `exit_mismatch` | The exit code doesn't match the status, or the process's exit doesn't match it |
| `contract_violation` | `tools/verify.py`'s own `assert_contract` rejects the result |
| `check_missing` | A check `tools/verify.py` defines is missing from the result |
| `check_duplicate` | A check appears twice |
| `check_not_passed` | A required check didn't pass, or an optional one failed |
| `witness_failed` | A witness made the claim false, or there's a counterexample |
| `no_proof` | The request had no proof or no theorem |
| `wrong_target` | The result is about another function, or its claim doesn't name the target |
| `unpinned` | The request didn't pin a statement, so nothing ties the theorem to the claim |
| `pin_mismatch` | The pinned statement isn't the case's claim, or the theorem doesn't match it |
| `claim_missing_function` | The claim doesn't name both `src` and `tgt` |
| `hypotheses_undeclared` | The theorem's hypotheses aren't the preconditions the case declares |
| `hypotheses_unwitnessed` | No input was shown to meet the preconditions, so the theorem may say nothing |
| `artifact_roles_mismatch` | The result hashed other inputs than the case has |
| `stale_input` | The IR it checked isn't the case's IR now |
| `stale_proof` | The proof it checked isn't the case's proof now |
| `stale_support` | A support module it checked isn't the case's now |
| `stale_library` | The `IRLean` library it used isn't the one built now |
| `stale_tool` | The `ir-lean` binary it used isn't the one there now |
| `stale_emitter` | The emitter's commit isn't the one checked out now |
| `dirty_emitter` | The emitter had uncommitted changes, so no commit says what it was |
| `stale_lean` | The Lean it used isn't the one on `PATH` now |
| `stale_checker` | `tools/verify.py`, `tools/verify_check.lean`, `tests/check_axioms.lean` or `tools/irlean`'s Python changed since |

## Blocked integration cases

[`blocked.json`](../tests/verification_negative/blocked.json) lists the negative cases that need a contract another
lane owns. The runner prints each as `BLOCK`. A blocked case is never run and never certified, and it doesn't fail
the run, so it has to be read. Nothing from the peer prototypes is copied here.

| Case | Blocked on | Has to show |
| --- | --- | --- |
| `refines_certificates` | T1 | The live cases, restated as `IRLean.Refines`, give the same verdicts |
| `certificate_for_another_pass` | T2 | A certificate for one pass, or other parameters, doesn't count for another |
| `source_not_the_pass_input` | T2 | A true theorem whose `src` isn't the IR the pass was given doesn't count |
| `stale_llvm_revision` | T2 | A certificate from another LLVM revision doesn't count |
| `pipeline_with_a_gap` | T1, T2 | A pipeline with one step uncertified, unsupported or timed out isn't certified |
| `memory_refinement` | T1 | A wrong memory rewrite, such as a deleted store a later load reads, isn't certified |
| `vector_lane_poison` | T1 | A rewrite that makes one lane poison where `src` had a value isn't certified |
| `inventory_denominator` | The inventory | A pass with no certificates counts as unfinished, and dropping it from the inventory fails |
| `codegen_passes` | A machine IR model | Wrong backend rewrites aren't certified |

T1 is read here as the semantics and refinement contract, and T2 as the contract binding a certificate to a pass, an
`opt` run and an LLVM revision, from the lanes' branch names. Check that against `docs/llvm-verification-tasks.md`
when it lands.

## What this trusts

- **`tools/verify.py`** and what it trusts: [verify](verify.md#what-proved-rests-on), with
  `tools/verify_check.lean`, `tests/check_axioms.lean`, the kernel and `leanchecker`. The gate reads what it printed
  and can't tell a faithful result from a forged one. It catches results that are stale, for something else, or that
  contradict themselves, not a dishonest checker.
- **The emitter and the model**, as [trust](trust.md) says. Each certificate is about `IRLean`'s meaning of the IR.
- **The claim template** in `tests/verify_negative.py`, `REFINES`, which a person has to read. Each control proves it,
  and `freeze_duplicated` refutes it where equality is fooled, but that's tests, not a proof that it's refinement.
- **The gate itself**, about 140 lines of Python, which the static cases test and nothing proves.
- **Each case's `llvm_verdict`**, worked out by hand.
- **Lean's compiler**, for counterexamples, as for every witness in [verify](verify.md#counterexamples). Certificates
  don't rest on it.

## Assumptions

- A case's functions take and return one integer, and touch no memory. The claim template is only refinement there.
- The binder in a claim isn't named `r` or `_`, which the template binds.
- `tools/verify.py` runs on the toolchain of the dev shell, with `IRLean` built from the same commit.
- A result's `versions.ir_lean` names a commit only when the emitter, `IRLean` and `tools/` have no local changes.
  The gate refuses a stored result without one. A result the runner made in the same run is checked against the
  tree as it is, so the live tier works while those files are being edited.

## What isn't covered

- Memory, pointers, vectors, floating point, `undef` and calls between functions: no claim, or blocked above.
- Model stops: a `src` that stops in the model allows nothing, so a right rewrite like `freeze_added_unmodeled` can't
  be certified.
- Counterexamples are only as good as the model: one that runs through a model stop isn't LLVM's.
- Only `tools/verify.py`'s answers are tested. `tests/proofs.sh`, `tests/llvm.py`, `tests/superopt.py` and any pass
  scorer have their own checks, which this doesn't exercise.

## Proof-to-code gaps

- The IR is written by hand. Nothing ties `src` and `tgt` to an `opt` run, a pass, or a revision of LLVM, and a
  certificate says nothing about the C++ that would make the rewrite. Those are `certificate_for_another_pass`,
  `source_not_the_pass_input` and `stale_llvm_revision` above.
- The result doesn't record the hash of `tools/verify.py` or its Lean checks. The runner records them in its own
  envelope, so a stored envelope can be checked for them, but a bare result can't.
- The result doesn't record `opt`'s version, which decided `ir_valid`, or `leanchecker`'s separately from Lean's.

## Found while building this

- **Equality isn't refinement.** `tgt x = src x` proves `freeze_duplicated`, a wrong rewrite, because both sides stop
  at a frozen poison. Any claim of equality between two functions that can stop in the model has this problem.
- **`tools/verify.py` proves a vacuous precondition**, as [verify](verify.md#reading-a-result) says it will. Nothing
  in a result says whether a hypothesis can hold. The probe above is one way to check.
- **`assert_contract` in `tools/verify.py` raises `KeyError`**, not `AssertionError`, on a result missing a required
  check, since it reads `checks[c]`. `build_result` always has every check, so `tools/verify.py` itself can't hit
  this, but anything checking a stored result with it crashes instead of refusing. The gate counts any exception as a
  `contract_violation`.
- **`mentions_target` only needs the target.** A theorem about `tgt` alone passes it. The gate also needs every
  function the claim is about.
- **A pinned statement can't use `match`**, since its auxiliary definition is in the proof module.
- **Reading a claim takes about 2.4 GB.** With `limits.memory_mb` at 2000, every proof here comes back
  `memory_limit`, even the controls.

## Running it in CI

`ctest` runs it as two tests: `verify_negative_static`, with every other test, and `verify_negative`, the live
tier, with `RUN_SERIAL`, so `CTEST_PARALLEL_LEVEL` never runs it beside other Lean tests. CI's `test` job runs both,
through `ctest -LE 'lint|slow'`. `tests/lint.sh` checks the cases' IR with `opt -passes=verify`.

### Limits

| Limit | Default | Where |
| --- | --- | --- |
| Time per check | At most 120 s. Cases set 20 to 120 | `--case-timeout`, the case's `limits.timeout_seconds` |
| Watchdog | The time limit plus 60 s, then the checker's process group is killed | `run_checker` |
| Lean's memory per check | At most 4000 MB, through `lean -M` | `--case-memory-mb`, the case's `limits.memory_mb` |
| Peak memory per case | 5512 MB, five quarters of Lean's plus 512. Over it, the case fails | `run_live` |
| Free memory before each live case | 6000 MB, and 4000 MB under `ctest`, or the case doesn't run, and the run exits 3 | `--min-available-mb` |
| At once | One `tools/verify.py`, which runs one Lean process at a time | |
| The whole live test | 900 s | `ctest`'s `TIMEOUT` |
| Measured on Linux | The live tier in about 85 s, at most 2.4 GB at once. The static tier in about 3 s | |

A case can lower its limits and never raise them past the runner's. Exit 3, not run, fails the test, and the job:
nothing here is `continue-on-error`. Don't cache `build/verify-negative/` between runs. The gate would refuse a
stale result anyway.

### Later

- When T1's `Refines` lands, the claim template becomes `IRLean.Refines Opt.src Opt.tgt`, and `refines_certificates`
  moves from blocked to live, with a check that the template and `Refines` agree on every case here.
- When T2's certificate format lands, a pass scorer counts a certificate only through `gate`, or a version of it moved
  next to `tools/verify.py`. A certificate then has to carry what the gate reads: the pinned claim, the functions it
  names, the hash of every input, the toolchain's versions, and the checker's own hashes. The T2 cases move to live.
- Each blocked case that moves becomes a directory under `cases/`, and leaves `blocked.json`.
- CI could upload `build/verify-negative/*/report.json` and the envelopes when the test fails, which say why each
  case came out as it did. That's a change to `.github/workflows/ci.yml`, which this doesn't make.

## Changing it

- **A case** is a directory under `tests/verification_negative/cases/` with `case.json`, `Opt.ll` and, for a proof,
  `Proof.lean`, whose theorem states the claim the runner writes. `--list` checks every manifest.
- **A new reason** goes in `DENIALS`, this doc's table, and a case that expects it, or `denials_covered` fails.
- **A new kind of result** from `tools/verify.py` is refused until the gate knows it: any status but `proved` is.
