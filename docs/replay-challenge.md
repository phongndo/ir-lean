# Challenging replay certificates

An adversarial check of the certificates [#45](llvm-proof-binding.md) binds and [#44](llvm-negative-verification.md)
counts, from outside the tools that make them. [`tests/replay_challenge.py`](../tests/replay_challenge.py) feeds
[`tools/binding.py`](../tools/binding.py) evidence it should refuse. It also asks Alive2 about every rewrite those
tools are tested on, and checks IRLean's own verdict on new poison and flag rewrites against both Alive2 and a hand
derivation from LangRef. For what any theorem here means, see [trust](trust.md).

**This proves no optimization.** It tests the checking. A `bound` bundle here is translation validation of one
`opt` run on one function, in IRLean's model, as [binding](llvm-proof-binding.md) says. Alive2 agreeing is
evidence from a second semantics, not a proof. Evaluating a pair on every input in Lean's interpreter is a
cross-check of the model, which trusts Lean's compiler, not its kernel.

Facts here were checked on top of commit `4cd91e5` on 2026-11-08, on x86-64 Linux in the dev shell: LLVM and `opt`
23.1.3, Alive2 at `a68009c9e81575bdcc249d3cc534514a76112221` built on that LLVM, as
[`nix/shell.nix`](../nix/shell.nix) pins it, and Lean 4.35.0.

## Running it

From the repo, in `nix develop`:

```console
tests/replay_challenge.py --tier static   # Python only, about 4 s
tests/replay_challenge.py --tier alive    # alive-tv only, about 5 s
tests/replay_challenge.py --tier live     # after lake build and building build/ir-lean
tests/replay_challenge.py --only live/binding/spoofed_limit alive/pair
```

| Exit | Means |
| --- | --- |
| 0 | Every case came out as the contract says, or as a known finding below says |
| 1 | A case didn't. A bound bundle that Alive2 finds wrong, or a certified #44 case that Alive2 finds wrong, always fails |
| 2 | Usage |
| 3 | A case couldn't run: a tool is missing, a limit stopped it, Alive2 didn't decide, or less than 4000 MB was free. Never a pass |

Each run writes `build/replay-challenge/report-TIER.json`, and removes only its own tier's work, since `ctest`
runs the static and Alive2 tiers at once. `--keep` keeps the bundles and generated Lean.

A case with a known finding passes on the contract's answer, or on the finding's status and reason together with
its evidence in the verdict, such as the error a crash raised or the step a certificate failed at. The same status
and reason for another cause fails.

## What's checked

### Static: the contract, in Python

| Case | Feeds `tools/binding.py` | Has to be |
| --- | --- | --- |
| `fixtures` | Nothing: `pairs.json` against `pairs.ll`, and against itself | Every pair defined, a right pair failing on nothing, an equal pair right |
| `manifest/template` | A manifest with every key of the right shape, naming files that aren't there | `refused`, `artifact_hash_mismatch`, so each case below that changes one field is refused for that field |
| `manifest/not_utf8`, `top_level_array` | Bytes that aren't UTF-8, a JSON array | `refused`, `manifest_invalid` |
| `manifest/mtriple_not_a_string` | `transform.mtriple` of `false` | `refused`, `manifest_invalid` |
| `manifest/option_in_passes` | `instcombine -disable-output` as the pass spec | `refused`, `manifest_invalid`: no option rides in on `-passes=` |
| `manifest/function_with_type` | `f(i8)` as the function | `refused`, `manifest_invalid` |
| `manifest/kind_a_list`, `kind_an_object`, `nested_too_deep`, `path_parent` | A claim kind that isn't a string, 100,000 nested arrays, `..` as a path | `refused`, `manifest_invalid`. Known: F2 |
| `manifest/key_twice` | `"kind"` twice, `pass_implementation` and then `ir_instance_equivalence` | `refused`, `manifest_invalid`. Known: F4 |
| `runner/failure` | A process that prints an error and exits 1 | An answer, exit 1, which the caller judges |
| `runner/signal` | A process that dies of `SIGSEGV` | `unknown`, `resource_limit` |
| `runner/timeout` | A process past its time, with a child | `unknown`, `time_limit`, and the child gone |
| `runner/leftover` | A process that exits and leaves a child | Exit 0, and the child gone |
| `runner/memory` | A process past its cgroup's memory | `unknown`, `resource_limit`. Without a systemd scope, only that the runner doesn't claim one |
| `promises` | `mustprogress` in loop metadata and an attribute group, `willreturn` on a function | Found, so a target with one is `unsupported` |

Every verdict is also checked for what any verdict has to be: its schema, an exit code that's its status's, and
`does_not_establish`, `trusted` and `open_obligation`. A verdict that isn't `bound` establishes nothing, and a `bound`
one ran every check in [order](llvm-proof-binding.md#the-checks-in-order), each passed, and states its claim.

### Alive2: every pair, both ways

Alive2 is asked about each rewrite twice: with `--disable-undef-input`, as IRLean assumes, and without, as LLVM
allows. Each function is put alone in a file, named `f`, and the two files are compared, with `--smt-to=10000`, in
a process capped at 2048 MB and 120 s. It's `correct` only if Alive2's summary counts exactly one correct
transformation and nothing else, `incorrect` only if it counts exactly one incorrect one, and otherwise unknown.

[`pairs.ll`](../tests/replay_challenge/pairs.ll) has 17 poison and flag rewrites, and
[`pairs.json`](../tests/replay_challenge/pairs.json) says, worked out by hand from LangRef, whether each is right, on
exactly which inputs it's wrong, and whether the two are equal in the model.

| Pair | Rewrite | Wrong at | Equal |
| --- | --- | --- | --- |
| `mul_nsw_shl_nsw` | `mul nsw x, 2` to `shl nsw x, 1` | Nothing | Yes |
| `mul_nsw_shl_nuw` | `mul nsw x, 2` to `shl nuw x, 1` | 192 to 255 | No |
| `add_drop_nuw` | `add nuw x, 1` to `add x, 1` | Nothing | No |
| `add_add_nuw` | `add x, 1` to `add nuw x, 1` | 255 | No |
| `or_disjoint_add` | `or disjoint x, 1` to `add x, 1` | Nothing | No |
| `add_or_disjoint` | `add x, 1` to `or disjoint x, 1` | Every odd x | No |
| `zext_nneg_sext` | `zext nneg` to `sext` | Nothing | No |
| `sext_zext_nneg` | `sext` to `zext nneg` | 128 to 255 | No |
| `udiv_exact_lshr_exact` | `udiv exact x, 4` to `lshr exact x, 2` | Nothing | Yes |
| `udiv_lshr_exact` | `udiv x, 4` to `lshr exact x, 2` | Every x not a multiple of 4 | No |
| `icmp_samesign_slt` | `icmp samesign ult x, 5` to `icmp slt x, 5` | Nothing | No |
| `icmp_add_samesign` | `icmp ult x, 5` to `icmp samesign ult x, 5` | 128 to 255 | No |
| `shl_overshift_zero` | `shl 1, x` to `x < 8 ? shl 1, x : 0` | Nothing | No |
| `ctlz_drop_zero_poison` | `ctlz(x, true)` to `ctlz(x, false)` | Nothing | No |
| `ctlz_add_zero_poison` | `ctlz(x, false)` to `ctlz(x, true)` | 0 | No |
| `abs_add_int_min_poison` | `abs(x, false)` to `abs(x, true)` | 128 | No |
| `and_zero_xor_self` | `and x, 0` to `xor x, x` | Nothing, unless x can be `undef` | Yes |

All 34 Alive2 answers are the hand derivation's, and each counterexample Alive2 gives is an input the derivation
says the pair fails on. `and_zero_xor_self` is right without `undef` and wrong with it, which Alive2 shows with an
`undef` x. That's why `tools/binding.py` refuses an argument that isn't `noundef`.

The 23 cases in [`tests/verification_negative`](../tests/verification_negative/cases/) are asked the same way. A
precondition is stated as `llvm.assume` at the start of `src`. Alive2 agrees with each case's `llvm_verdict` in
42 of its 46 answers. The other four are two cases, each asked both ways, that
[`corpus.json`](../tests/replay_challenge/corpus.json) explains, each with a check that the explanation holds:

| Case | Alive2 says | Why | Checked by |
| --- | --- | --- | --- |
| `wrong_loop_deleted` | Correct, and the rewrite is wrong | Alive2 unrolls a loop a bounded number of times and drops longer runs, so it never sees `src` run forever. Its "correct" isn't evidence for code with a loop | Unrolled twice, Alive2 still says correct, and its `src` ends in `#sink` |
| `precondition_vacuous` | Correct | `x < 0` never holds, so `src` is undefined on every input. Vacuous, as the case says | No value of `x` meets the hypotheses, tried on all 256 |

A case `tests/verify_negative.py` certifies that Alive2 finds wrong fails, whatever `corpus.json` says.

### Live: IRLean on the pairs

ir-lean translates `pairs.ll`, and Lean evaluates each pair on all 257 inputs, poison included, in its
interpreter. A pair fails at an input where the target isn't allowed by the source, as `tests/verify_negative.py`'s
claim says: undefined behavior allows anything, a poison result any returned result, a value only itself, a run
that never ends only another, and a model stop nothing. So a poison result doesn't allow undefined behavior, a run
that never ends, or a model stop. Each pair's failing set has to be exactly the one `pairs.json` gives, equality
has to be what it says, the source can't stop the model, Alive2 has to give the verdict `pairs.json` does, and its
counterexample has to be in the set. If Alive2 doesn't decide, the case doesn't run. One Lean process, capped at
2000 MB, compiles the module and another evaluates it.

So three independent answers agree on every input of every pair: the hand derivation, IRLean's model, and Alive2,
where Alive2 gives one counterexample and the other two give the whole set. 6 of the 9 right pairs are
refinements that aren't equal, which an `ir_instance_equivalence` certificate can't bind and an
`ir_instance_refinement` one could, once `IRLean.Refines` is on `main`.

### Live: `tools/binding.py` on real `opt` runs

Each bundle is made with `tools/binding.py record` on a real `opt` run with `-mtriple=x86_64-unknown-linux-gnu`,
changed only as the case says, and checked with `tools/binding.py verify --timeout 300 --memory 3000`, without a
cache. `tests/binding.py` reaches neither `function_not_found` nor `signature_mismatch`, and the other cases reach a
reason it does by another way: a string attribute, a pipeline, an `axiom` rather than `sorry`, a moved bundle, and a
certificate's own words.

`module_shadowed` looks out of reach from a manifest. Lean takes a module's root from the first directory on its
path named like it, so a namespace named like a root, such as `IRLean`, makes the run's `IRLean/` hide the real one,
and the generated module doesn't compile: `error`, `generated_module_failed`, before any certificate is read. A
module the certificate adds is caught by the listing first, as [binding](llvm-proof-binding.md#tests) says.

| Case | Input, pass | Evidence | Has to be |
| --- | --- | --- | --- |
| `bound` | [`mul_nsw.ll`](../tests/replay_challenge/mul_nsw.ll), `instcombine` | [`MulNsw.lean`](../tests/replay_challenge/MulNsw.lean): `mul nsw x, 2` and `shl nsw x, 1` are equal and never stop | `bound`, and Alive2 agrees |
| `add_zero_bound` | `tests/binding/add_zero.ll`, `instcombine` | `tests/binding/AddZero.lean`, read as it is | `bound`, and Alive2 agrees |
| `relocated` | The `bound` bundle, copied elsewhere | The same | `bound`: nothing depends on where a bundle is |
| `function_missing` | The `bound` bundle | `claim.function` names `h`, which isn't there | `refused`, `function_not_found` |
| `signature_changed` | [`dead_argument.ll`](../tests/replay_challenge/dead_argument.ll), `deadargelim` | `f` loses an argument | `refused`, `signature_mismatch` |
| `namespace_irlean` | `mul_nsw.ll`, `instcombine` | Namespace `IRLean`, so the generated modules are `IRLean.Src` and `IRLean.Tgt` | `refused`, `manifest_invalid`. Known: F2 |
| `string_noundef` | [`string_noundef.ll`](../tests/replay_challenge/string_noundef.ll), `instcombine` | An argument with the string attribute `"noundef"`, which isn't `noundef` | `unsupported`, `undef_argument` |
| `o2_promises` | `mul_nsw.ll`, `default<O2>` | `function-attrs` adds `mustprogress` and `willreturn` | `unsupported`, `trusted_promise`, and Alive2 finds the run right |
| `custom_axiom` | `mul_nsw.ll`, `instcombine` | The claim as an `axiom` | `refused`, `axiom_policy_failed` |
| `spoofed_limit` | `mul_nsw.ll`, `instcombine` | `MulNsw.lean` and a theorem whose tactic fails with "maximum number of heartbeats" | `refused`, `certificate_compile_failed`. Known: F1 |

`o2_promises` matters for scoring pipelines: any function `function-attrs` can prove returns gets `willreturn`, so a
pure function from an `-O2` pipeline is unsupported until IRLean checks those promises.

## Findings

Each was sent to the owner of `tools/binding.py` with a repro. None lets wrong evidence come back `bound`: each fails
closed. The tests accept the current answer as known, and the contract's when it's fixed.

| Id | What | Repro | Effect |
| --- | --- | --- | --- |
| F1 | A certificate can make its own refusal `unknown`. The runner calls a failed step a resource limit if Lean's output matches a limit's message, and the certificate controls what Lean prints | `live/binding/spoofed_limit`: a tactic `fail "maximum number of heartbeats (200000) has been reached"` | `unknown` says more time or memory may help. A scorer that retries or reports unknowns differently from refusals is misled. Not `bound` |
| F2 | The schema lets through values it should refuse. A claim kind that isn't a string reaches a `dict` lookup and raises `TypeError`, JSON nested 100,000 deep raises `RecursionError`, `..` passes as a file name, and `IRLean`, `Init`, `Lean` or `Std` pass as a namespace, which hides that root from Lean when it compiles the generated module | `static/manifest/kind_a_list`, `kind_an_object`, `nested_too_deep`, `path_parent`, `live/binding/namespace_irlean` | `error`, `internal_error` or `generated_module_failed`, or `refused` for another reason, where the contract says `refused`, `manifest_invalid` |
| F3 | An `internal_error` verdict has only `schema`, `status`, `reason`, `detail` and `exit_code`. The contract says every verdict carries `does_not_establish`, `trusted` and `open_obligation` | The `internal_error` cases of F2 | A reader of that verdict isn't told what it doesn't establish |
| F4 | A key given twice is read as the last one. Another reader may take the first, and RFC 8259 leaves it open, so the manifest can mean different things to different readers | `static/manifest/key_twice` | Low: the verdict repeats the claim kind it checked, and the scorer reads that |

Found on the way, in the tools rather than `tools/binding.py`:

- **`alive-tv --src-fn=NAME` ignores a name it doesn't find.** It then checks every function in the file against
  itself, and calls them all correct: `--src-fn=nope` on `pairs.ll` gave 34 correct transformations. A file with
  `src` and no `tgt` does the same: `proof_for_other_target`'s three functions came back as three correct ones,
  though the claim, `src` to `tgt_bad`, is wrong. A file with only `src` and `tgt` prints no summary at all. Each pair
  is therefore put in two files of its own, with one function `f` each, and counts only if the summary is exactly one
  transformation.
- **Alive2's "correct" doesn't cover a loop.** See `wrong_loop_deleted` above.
- **The binding doc swaps a direction.** [Binding](llvm-proof-binding.md#claim-kinds) says equivalence implies
  refinement only where "the model has no less undefined behavior than LLVM in the source, and no more in the
  target". Soundness needs the reverse: no more in the source, so a source the model calls undefined is undefined
  in LLVM, and no less in the target, so a target LLVM calls undefined is undefined in the model. The three
  `unsupported` kinds that follow it are each the right way round.

## What this trusts and leaves out

- **The hand derivations** in `pairs.json` and `corpus.json`, checked against Alive2 and the model, which could share
  a mistake with them. Alive2 and IRLean are written separately, from LangRef.
- **Alive2**, at the pinned commit, for its answers. A timeout or a failure to prove is unknown, never agreement.
- **Lean's compiler and interpreter**, for the model's answers on the pairs. Nothing here is a kernel-checked proof,
  apart from what `tools/binding.py` checks for a `bound` bundle.
- Only `i8` arguments. 257 inputs is every input of one, and says nothing about other widths.
- Nothing here runs a pass scorer. Lane 2's scorer contract (`ir-lean.passes.run/1` and `ir-lean.passes.instance/1`,
  verdicts through `tools/binding.py`) isn't on `main` yet, and challenges to its cache, verdict reading and
  `unknown` handling come when it is.
- `ir_instance_refinement` isn't challenged: `IRLean.Refines` isn't on `main` yet.
- Memory, pointers, vectors, floating point and `undef` arguments stay unsupported, as [binding](llvm-proof-binding.md)
  says. These tests only check that they're refused.

## Limits

| Limit | Value |
| --- | --- |
| Alive2 | `--smt-to=10000`, 120 s and 2048 MB a process, one at a time |
| Lean, evaluating the pairs | `-j1 -M 2000`, 300 s, a cgroup of 2512 MB |
| `tools/binding.py verify` | `--timeout 300 --memory 3000`, which caps each of its processes at 3512 MB |
| Free memory before the live tier | 4000 MB, `--min-available-mb` |

Without `systemd-run --user --scope`, Alive2 runs under an address-space limit, and Lean under its own `-M`.
`ctest` runs the static and Alive2 tiers with the other tests, and the live tier alone. See [testing](testing.md).
