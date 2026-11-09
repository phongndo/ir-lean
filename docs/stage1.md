# Stage 1: InstCombine's rewrites, certified and compared with Alive2

Stage 1 of [proved superoptimization](roadmap.md#phase-4-certified-translation-validation-and-superoptimization), as
[the gate](prior-art.md#the-gate) narrowed it: InstCombine's own regression tests read through the emitter, each rewrite
certified with `bv_decide` at fixed widths, every verdict compared with Alive2's, and a corpus of known miscompilations
that must never get a certificate. The harness is [`bench/instcombine/stage1.py`](../bench/instcombine/stage1.py). For
what any theorem means, read [trust](trust.md) first.

**This proves no optimization.** A certificate here is translation validation of one `opt` run on one function, as
[binding](llvm-proof-binding.md) says. It says nothing about InstCombine on any other input, or about its C++.

## The results

Run on 2026-11-09 on x86-64 Linux in the dev shell, with LLVM 23.1.3, Alive2 at its pinned commit, and Lean 4.35.0,
on `main` at `dbfd710` merged into this branch. The harness was this branch at `51afc87` for every stage, and the
summaries were written at `362c0f6`, which changes no stage.
[`results/summary.json`](../bench/instcombine/results/summary.json) has every count and the toolchain's hashes.

**In short:**

- No known-wrong rewrite is certified, and none Alive2 finds wrong without `undef` is proved. Of the 104 pairs from
  known miscompilations that Alive2 confirms wrong, the model refutes every one it can run, 18, and can't state a
  claim about 84.
- On a uniform sample of 4,000 of the 31,158 changed pairs, 1,104 are certified or proved, and Alive2 agrees with
  1,101 of them. It has no verdict on the other 3. No pair is proved where Alive2 finds a counterexample, and the
  model finds no counterexample where Alive2 proves one.
- Certificates are rare: 3 in the sample. `tools/binding.py` needs every argument `noundef`, and 91 of the 12,002
  candidates have that.
- The emitter refuses 59% of the changed functions, half of them for floating point. [Below](#why-the-emitter-refuses-a-function).

### Every test

`opt -passes=instcombine` ran on all 1,845 tests, and rejected one. It changed 31,240 of their 38,704 functions:

| Pairs | Count |
| --- | ---: |
| Candidates: both sides translated, no memory | 12,002 |
| The emitter refuses a side | 18,361 |
| Translated, using memory | 795 |
| Unchanged once cut into a module of its own | 77 |
| `llvm-extract` failed | 5 |

Of the 12,002 candidates, 2,696 have vector arguments, and 91 have every argument `noundef`.

### Chunk 1's gates, for InstCombine

[Chunks](chunks.md#how-each-is-measured) defines G0 and G1 over these pairs, and S1's metric is G1 for InstCombine.
They're measured on this branch's head, `44cfcc2`, with `main` at `b9446de` merged in, after the run above: `pairs` on
every test, then `prove --eligible-only` and `certify`, which give every certificate there can be, since only a pair
whose arguments are all `noundef` can be bound, and `alive --eligible-only`, which compares each of them with Alive2. [`results/summary.json`](../bench/instcombine/results/summary.json)'s
`instcombine_gates` has the counts and the toolchain.

- **G0, 40.2%:** 12,547 of the 31,240 pairs translate on both sides, the 11,753 candidates and the 794 with memory. On
  `dbfd710` it was 41.0%, 12,797, and SEM-08, [#82](https://github.com/phongndo/ir-lean/pull/82), has the emitter
  refuse 250 more since. The 38.4% chunks recorded before counted only the pairs without memory, though its definition
  counts a pair with memory.
- **G1, 0.11%:** 34 of the 31,240 pairs are certified. 75 can be bound: 34 proved and all 34 bound, 28 found no proof,
  10 ran out of heartbeats, the emitter left 2 out of the module `prove` writes, and Lean rejected what it wrote for 1.
- **Alive2 on the 75:** it calls none incorrect, and 67 correct, 33 of the 34 certified among them. It calls 8 sources
  undefined on every input. One is certified, `pt62607` in `div-i1.ll`, and is: its loop's first trip divides by
  `false`, so the certificate is vacuous. The other 7 the automation doesn't prove: 6 loops out of heartbeats, and
  one with no proof.

### A uniform sample

`--upto 4000` takes the first 4,000 of the 31,158 candidates and refused pairs by id, a SHA-256 of the test and
function, so they're a uniform sample of them, the same every run. 1,541 are candidates.

| `ir-lean` | Pairs | Why |
| --- | ---: | --- |
| `certified` | 3 | Bound by `tools/binding.py` |
| `proved` | 1,101 | |
| `refuted` | 0 | |
| `no_verdict` | 187 | The automation found no proof, and no witness refutes it |
| `unknown` | 203 | Heartbeats 154, recursion depth 43, time 6 |
| `unsupported` | 2,466 | The emitter refuses a side 2,356, memory 103, and a model stop on the only counterexample 7 |
| `error` | 40 | Lean rejects what the emitter wrote: the emitter bug [below](#found-along-the-way) |

The agreement matrix, each pair once:

| `ir-lean` \ Alive2 | `correct` | `incorrect` | `src_always_ub` | `timeout` | `incomplete` | `unsupported` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `certified` | 3 | | | | | |
| `proved` | 1,098 | | 2 | 1 | | |
| `refuted` | | | | | | |
| `no_verdict` | 171 | | | 16 | | |
| `unknown` | 187 | | 3 | 13 | | |
| `unsupported` | 1,523 | 32 | 28 | 110 | 495 | 278 |
| `error` | 39 | | 1 | | | |

### Disagreements

Two verdicts disagree where one side proves and the other refutes. In the sample, none do: of the 1,104 pairs `ir-lean`
certifies or proves, Alive2 refutes none, and of the 32 Alive2 refutes, `ir-lean` proves none. The model refuted no
pair, on 380 tried, so it contradicts none of Alive2's 3,021 `correct`.

Where one side has a verdict and the other doesn't:

| Kind | Pairs | Explained as |
| --- | ---: | --- |
| `ir-lean` proves, Alive2 calls the source always undefined | 2 | Both agree the source is undefined everywhere, such as `udiv_by_zero_indirect_is_poison`, which divides by zero on both paths. The proof is vacuous: any target refines such a source. `--fail-src-ub` is why Alive2 doesn't count it |
| `ir-lean` proves, Alive2 times out | 1 | An Alive2 timeout: `mul_select` in `select-fixed-zero.ll` |
| Alive2 has a verdict, the model can't state the claim | 1,555 | Unsupported: the emitter refuses a side for 1,454, and 101 use memory. All 32 of Alive2's `incorrect` are here, 31 refused by the emitter and 1 with memory: floating-point `minnum`, `maximum` and class folds, x86 vector shifts, and a `memcpy` turned into loads |
| Alive2 calls the source always undefined, the model stops | 7 | Neither has a verdict on the rewrite. Each source calls a function with a type its declaration doesn't have, such as `call void @use16` of an `i16 @use16`: Alive2 calls that undefined, and the model stops, `unknownCallee`, which never certifies |
| Alive2 says `correct`, `ir-lean` found no proof | 358 | The automation's limit, not a disagreement. 171 found no proof, and a limit stopped 187. Witnesses ran on 341 of them, Alive2's counterexample where it had one and edge values, and none refutes. 16 couldn't be tried, a source that chooses or a type `refute` doesn't take, and 1 ran out of time |
| Alive2 says `correct`, Lean rejects what the emitter wrote | 39 | The emitter bug, which fails closed |

So over the 1,104 pairs `ir-lean` has a verdict on, every one either agrees with Alive2, or Alive2 has none: two
vacuous sources and one timeout.

### The known miscompilations

From [`known_wrong.json`](../bench/instcombine/known_wrong.json)'s 232 cases, 186 give a changed pair at the pin, 556
pairs in all. A pair counts as known-wrong when the pinned Alive2 says so:

| Alive2 | Pairs | `ir-lean` on them |
| --- | ---: | --- |
| Wrong, without `undef` | 104 | Refuted 18, unsupported 84, no verdict 1, error 1. None proved or certified |
| Wrong only with an `undef` argument | 20 | Proved 7, which `proved` allows, since it doesn't cover `undef`. Unsupported 8, no verdict 5. None certified |
| Not confirmed wrong | 432 | Fixed at the pin, or wrong only in ways this Alive2 doesn't see, such as loops past its bound |

Of the 104, 50 are from Alive2's dashboard, 35 are issues' own pairs, and 19 are what the pinned `opt` still does to an
issue's reproducer. The model refutes every one it can run. Three pairs disagree:

- **Issue 91127:** the model refutes, and Alive2 calls the source always undefined. The source is a loop of three trips
  returning 1, and the target returns 0. With `--src-unroll=4 --tgt-unroll=4`, Alive2 finds the same value mismatch.
  Its bound on loops, not the source, is why it said undefined.
- **Issue 161492:** Alive2 refutes, and the model has no verdict. The source returns a `select` of two frozen poisons,
  a value, and the target poison. It chooses, so a refutation needs every way it chooses to fail, which a witness can't
  show, and the automation finds no proof, as it shouldn't.
- **Issue 210605:** Alive2 refutes, and Lean rejects what the emitter wrote for its vector `llvm.ssub.with.overflow`.

Whether Alive2 says a pair is wrong only with `undef` comes from a second run without `--disable-undef-input`, and is
best effort: with `undef` inputs its solver often times out, and a pair whose second run doesn't decide stays not
confirmed.

### Cost per pair

| Stage | Pairs | Median | 90th percentile | Most | Wall time, at once |
| --- | ---: | ---: | ---: | ---: | --- |
| `pairs`, every test | 31,240 | | | | 120 s, 8 tests |
| `prove` | 1,541 | 4.1 s | 55 s | 120 s, the limit | 3,546 s, 6 |
| `certify` | 3 | 7.2 s | | | 15 s |
| Alive2 | 4,000 | 0.02 s | 0.1 s | 60 s, the limit | 366 s, 6 |
| `refute` | 380 | 3.5 s | 4.5 s | 300 s, the limit | 467 s, 6 |

A candidate costs about 15 s of `ir-lean`'s time in all, most of it the pairs that run to a limit: half prove in
4.1 s. Alive2 answers most pairs in hundredths of a second. Each `tools/verify.py` peaks at about 2.4 GB.

## What a verdict means

Each pair is one function from one test: the function before `opt -passes=instcombine`, and after. It gets one verdict
from `ir-lean`, from the gates only, and one from Alive2.

| `ir-lean` verdict | Means | From |
| --- | --- | --- |
| `certified` | A bound certificate: `IRLean.Refines Src.f Tgt.f`, kernel-checked, bound to the input, the `opt` run and the toolchain, and replayed from scratch | [`tools/binding.py`](llvm-proof-binding.md) `verify` said `bound` about this pair's input, function, pass spec and claim kind `ir_instance_refinement`, and [`irlean.verdict`](trust.md#where-python-decides-a-verdict) granted `certified` on its run and record |
| `proved` | The same theorem, kernel-checked, for every input that's a value or poison. Not a certificate: an argument without `noundef` can be `undef`, which this doesn't cover | [`tools/verify.py`](verify.md) said `proved` with the statement pinned, the [negative-verification gate](llvm-negative-verification.md#the-gate) found no reason to refuse it, and `irlean.verdict` granted `proved` |
| `refuted` | The model's counterexample: on some input, and for a target that chooses, some way of choosing, the target does what the source doesn't allow, and neither side stops the model there | `tools/verify.py` decided a witness false by running the model, `irlean.verdict` granted `refuted`, and a second run on that witness found no model stop |
| `no_verdict` | The automation found no proof, and no witness tried refutes it. Never a counterexample | `tools/verify.py` said `proof_failed` |
| `unknown` | A limit stopped it: time, memory, heartbeats or recursion depth. More may help | `tools/verify.py` said `timeout` |
| `unsupported` | The model can't state the claim: the emitter refuses a side, the function uses memory, or a refutation goes through a model stop | The emitter's report, or the refutation's probe |
| `error` | A tool failed, such as Lean rejecting what the emitter generated | `tools/verify.py` said `error` for another reason |

Only `certified` is a certificate. `proved` is how most pairs can be compared with Alive2 at all: Alive2 runs with
`--disable-undef-input`, so its `correct` covers the same inputs.

| Alive2 verdict | Means |
| --- | --- |
| `correct` | `alive-tv` proved the target refines the source, for inputs that are values or poison, at the widths given |
| `incorrect` | It found a counterexample |
| `src_always_ub` | The source is undefined on every input, so any target refines it. With `--fail-src-ub`, that's a failure to prove, not a pass |
| `timeout` | Its solver or the 60 s limit ran out |
| `incomplete` | It approximated something and couldn't decide, or its solver gave up |
| `unsupported` | It can't read a type, instruction or attribute, such as scalable vectors or `x86_fp80` |

A disagreement is a pair whose verdicts differ where at least one side has one. Each is one of:

| Kind | Means |
| --- | --- |
| `investigate` | One side proves and the other refutes, or Alive2 refutes and the model, run on Alive2's counterexample, doesn't. A model bug or an Alive2 bug, explained by hand [below](#disagreements) |
| `alive2_timeout`, `alive2_incomplete`, `alive2_unsupported`, `source_always_ub` | `ir-lean` has a verdict and Alive2 doesn't |
| `unsupported` | Alive2 has a verdict and the model can't state the claim |
| `lean_no_proof` | Alive2 says correct, and `ir-lean`'s automation found no proof, or ran out, with no counterexample |

## How the pairs are made

At `llvmorg-23.1.3`, `llvm/test/Transforms/InstCombine` has 1,845 test files. For each, `stage1.py pairs`:

1. Reads the first `RUN` line that runs `instcombine` alone, for its spec and `-mtriple`. Without one, it uses plain
   `instcombine`. If `opt` refuses to reach a fixpoint, it uses `instcombine<no-verify-fixpoint>`, as such tests' own
   `RUN` lines do. Other options on the `RUN` line are dropped, so a pair is about `opt -passes=SPEC`, not the test's
   exact configuration.
2. Runs `opt -S -passes=verify` and `opt -S -passes=SPEC` on the whole test, and keeps the functions whose text changed,
   attribute groups included.
3. Cuts each changed function into a module of its own with `llvm-extract`, keeping the declarations it uses, and runs
   `opt` on that alone, reading stdin, exactly as `tools/binding.py` replays it. A function the run no longer changes
   alone is skipped. So the pair's target is what `opt` makes of that module, which a certificate can bind.
4. Asks the emitter's `--report` about both sides. A side the emitter refuses, or a function with memory or pointers, is
   `unsupported`.

The rest are candidates. `prove` puts each pair's source and target into one module, as `@src` and `@tgt`, with
`llvm-link`, and writes the theorem `IRLean.Refines Opt.src Opt.tgt` with a proof its own automation finds: each
argument, and each lane of a vector argument, split into poison and a value, both sides run a block at a time,
each branch and each case of the relation split, and each path closed with `bv_decide`. The proof is untrusted, and
imports only Lean, `IRLean` and the generated module. `certify` sends each proved pair that `tools/binding.py` can bind
through `record` and `verify`, with the same automation stated for the bundle's modules. `tools/binding.py` binds a pair
only when every argument is `noundef` in the source. Since SEM-07, [#62](https://github.com/phongndo/ir-lean/pull/62),
the model checks `mustprogress` and `willreturn`, so a target with either can be bound.

**Runs that choose.** Since F3, [#72](https://github.com/phongndo/ir-lean/pull/72), a function with a `freeze` returns
`IRLean.Outcomes`, an outcome for each way it chooses ([refinement](refinement.md#runs-that-make-choices)). Where only one
side chooses, which a rewrite adding or removing a `freeze` gives, the claim lifts the other with `IRLean.Outcomes.det`,
exactly as `tools/binding_check.lean` builds it, and the pinned statement says the same. The proof takes every way the
target chooses, and has the source choose the same, or, choosing alone, choose 0 everywhere, which can fail where
another choice would do.

`refute` runs the model, through `tools/verify.py`, on each pair the automation didn't prove, whose arguments and result
are integers or vectors of them: Alive2's counterexample first, if it has one, then up to 64 edge values for each
argument or lane, poison among them. A target that chooses gets two ways of choosing, 0 and 1 everywhere, as another
binder. A source that chooses isn't refuted, since that needs every way it chooses to fail. For an integer result, the
statement is the decidable form of refinement the [negative-verification gate](llvm-negative-verification.md#the-claim)
uses, over every reason `IRLean.UB` has, read from `IRLean/Basic.lean`. For a vector, it's the same lane by lane, with
`IRLean.Vec.lane`. A witness that makes it false is then run once more, to ask whether either side stops the model there.
A counterexample through a model stop is `unsupported`, never `refuted`, since a model stop says nothing about LLVM.

## The known miscompilations

[`bench/instcombine/known_wrong.json`](../bench/instcombine/known_wrong.json) holds 232 cases, fetched on 2026-11-08 with
`stage1.py known-fetch` and `known-build`:

| Kind | Cases | From |
| --- | --- | --- |
| `issue_pair` | 44 | A source and a target that LLVM got wrong, from the Alive2 sessions linked in llvm-project's issues labeled `miscompilation` and `llvm:instcombine`, 246 in all, or from an issue's own code |
| `issue_reproducer` | 64 | A reproducer and the InstCombine-family pass it ran, from the same issues. The pinned `opt` runs on it |
| `dashboard` | 124 | A test in the pinned llvm-project and the 502 functions Alive2's [dashboard](https://web.ist.utl.pt/nuno.lopes/alive2/) failed in it, in its run of LLVM `8a4244b560f3` on 2026-01-29. The pinned `opt` runs the test's own pass on it |

Issue cases keep their IR, since an issue can be edited. Dashboard cases only name a test and its functions. Each case
becomes pairs as above, and goes through the same stages. A pair counts as known-wrong when the pinned Alive2 says
`incorrect` about it, or says `incorrect` only once `undef` inputs are allowed, which the second Alive2 run, without
`--disable-undef-input`, checks. The rule:

- no known-wrong pair is `certified`;
- no pair Alive2 finds wrong without `undef` is `proved`.

A pair wrong only with an `undef` argument can be `proved`, since `proved` doesn't cover `undef`. That's why `proved`
isn't a certificate. It can't be `certified`: `tools/binding.py` requires `noundef` arguments, and with one, passing
`undef` is undefined.

## Why the emitter refuses a function

Of the 31,240 functions InstCombine changes, the emitter refuses 18,361 on one side or both, and 795 more use memory,
which the model translates but has no refinement for. This is every pair, not the sample, from `report`'s
`emitter_refusals`.

The emitter names one reason per function, the first it meets, so these are exclusive. A reason counts in the first
group that matches it, in this order:

| Group | Functions | Commonest reasons in it |
| --- | ---: | --- |
| Floating point | 9,035 | `float` 4,074, `double` 1,862, `<N x float>` 1,245, `half` 824, `<N x double>` 435, and floating-point attributes such as `denormal_fpenv` and `strictfp` |
| Calls outside the module | 2,936 | `call to external @F` 2,787, mostly the tests' `@use` helpers, and variadic calls |
| Target intrinsics | 1,815 | `llvm.x86.*`, most often `avx512.pternlog`, `pshuf.b` and the AVX-512 shifts, and `llvm.amdgcn.*` |
| Scalable vectors | 977 | `<vscale x N x ...>` types and `vscale_range` |
| Pointers: address spaces, `inttoptr`, external globals | 887 | `ptr addrspace(N)` 440, external globals 394 |
| `undef` | 691 | An `undef` constant, which the emitter refuses |
| Data layouts | 491 | A test's own data layout the model doesn't take, such as big-endian or 32-bit pointers |
| Division or remainder on vectors | 289 | `sdiv`, `udiv`, `srem` or `urem` of a vector |
| Other instructions | 258 | `store` 90 and `load` 27 of shapes the model doesn't take, calls 46, scalar `sdiv` and `udiv` 49, `freeze` 30, `getelementptr` 13 |
| Other intrinsics | 228 | Such as `llvm.ptrmask` |
| Other attributes | 157 | Such as `nocallback`, `null_pointer_is_valid` and `builtin` |
| Vector casts and pointer vectors | 148 | `bitcast` between vector shapes, `<N x ptr>` |
| Attributes on vectors | 112 | `range` or `noundef` on a vector argument or result |
| Metadata | 94 | `!range` and `!nonnull` on loads and calls |
| Atomics | 70 | |
| Constant expressions | 66 | `ptrtoint` of a global in a constant |
| Exceptions | 41 | |
| The emitter crashed | 34 | `ir-lean --report` gave no row: a segmentation fault, [below](#found-along-the-way) |
| Other | 32 | Prefix data, prologue data or a garbage collector 14, array types 8, variadic functions 4 |

Counted instead by what the source contains, a function can count in several: floating point in 9,576 of the 18,361,
vectors in 7,131, calls to a declared function in 5,264, target intrinsics in 4,656, pointers in 3,918, memory
instructions in 2,913, `undef` in 1,222, and scalable vectors in 906. So floating point alone blocks about half of what
the emitter refuses, and vectors run through every group.

This is `dbfd710`'s emitter. [#88](https://github.com/phongndo/ir-lean/pull/88), after these runs, models vector
intrinsics, vector division and remainder, and `noundef` and `range` on vectors, and by its own count on these pairs
has the emitter translate 664 more of them.

## Found along the way

None is a soundness bug: each makes the model or a tool say less, never prove a wrong rewrite.

| Finding | Where | Effect | Next |
| --- | --- | --- | --- |
| The emitter writes the vector form of an intrinsic as its scalar operation, such as `Val.saddWithOverflow` on a `Vec` for a vector `llvm.sadd.with.overflow`, and the same for vector bit counts and `llvm.bitreverse` in InstSimplify's tests. It also applies `noundef` to a struct value as if it were one integer. Lean rejects the module | `src/Emitter.cpp` | Fails closed: `tools/verify.py` says `generated_module_failed`, an `error` here. 40 pairs in the sample and 2 in the corpus | Fixed by [#88](https://github.com/phongndo/ir-lean/pull/88), after these runs, which models both lane by lane and field by field |
| `ir-lean --report` crashes, with a segmentation fault, on a constant `bitcast` of one vector type to another inside an instruction, such as `and <2 x i64> bitcast (<4 x i32> ... to <2 x i64>), ...` from `x86-muldq-inseltpoison.ll` | `src/Emitter.cpp` | Fails closed: the function gets no report and counts as refused. 34 changed functions | Fixed by [#88](https://github.com/phongndo/ir-lean/pull/88), after these runs: the emitter refuses the form instead |
| `tools/binding.py` binds only a source whose arguments are all `noundef`, since an `undef` argument can be a different value at each use and `IRLean`'s values never are. 91 of the 12,002 candidates are | `tools/binding.py`, by design | Certificates are rare. The rest can be `proved` for every value or poison, the same scope as Alive2's `--disable-undef-input`, but aren't certificates | Modeling `undef` arguments, which F3 kept out, is what would let most of InstCombine's tests be certified |
| `tests/verify_negative.py`'s list of `IRLean.UB` missed `noProgress` and `noReturn` after SEM-07 added them, so its decidable claim was stricter than refinement where a source spins | `tests/verify_negative.py` | A spurious counterexample where a source breaks a promise; never a false certificate | Fixed by [#77](https://github.com/phongndo/ir-lean/pull/77), which reads the list from the model. This harness reads it from `IRLean/Basic.lean` too |
| Alive2 calls the source of issue 91127 always undefined, a loop of three trips that returns 1. By default it drops paths around a loop. With `--src-unroll=4 --tgt-unroll=4` it finds the value mismatch the model finds | Alive2's defaults | Its `src_always_ub` there is its bound on loops, not the source's behavior | Kept as Alive2 is configured in `tests/alive.py`, and explained [below](#disagreements) |
| The pinned `alive-tv` spells the flag `--fail-src-ub`, not `--fail-if-src-is-ub` as the study's reading of `tools/transform.cpp` had it | `tests/alive.py` | None now: `tests/alive.py` passes `--fail-src-ub`, and `tests/alive_test.py` fails without it | |

## What it rests on

Everything in [trust](trust.md), [verify](verify.md#what-proved-rests-on) and
[binding](llvm-proof-binding.md#what-a-bound-verdict-rests-on), and:

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| `llvm-extract` keeps what InstCombine's rewrite of one function depends on | InstCombine is a function pass, and the module keeps the declarations the function uses. A pair the cut changes is checked against the cut module, which is what a certificate binds | A rewrite that reads another function's body. The pair is then still a real `opt` run, but not the one the whole test made |
| `llvm-link` and renaming to `@src` and `@tgt` don't change what either side means | Each side has one definition, renamed with its uses | A name clash `llvm-link` resolves by renaming a declaration |
| The decidable claim in `refute` is refinement on integer and vector functions | It's the negative-verification gate's, lane by lane for a vector, which its controls prove and its wrong cases refute | A difference from `IRLean.Refines` on some case. A `refuted` verdict is the model's counterexample, decided by running compiled code, as [verify](verify.md#counterexamples) says |
| The harness asks for the right claim, file and theorem | Every proved, certified and refuted here is granted by `irlean.verdict`, which checks that nothing it rests on crashed, ran out or failed. Choosing what to ask it is this harness's, about 1,900 lines of Python nothing proves, and `stage1 ci` tests | A bug choosing the claim, the file or the theorem |
| Alive2's verdicts, at its pinned commit on the shell's LLVM | It's the reference this compares with, not a gate | An Alive2 bug, which a disagreement may show |

## Reproducing it

In `nix develop`, after `lake build` and building `build/ir-lean`:

```sh
S=bench/instcombine/stage1.py
$S pairs                                   # every test, into build/stage1
$S prove --upto 4000                       # then certify, alive and refute, each with --upto 4000
$S report --upto 4000 --out build/stage1/summary-4000.json
$S --work build/stage1-known known-pairs   # the known miscompilations
$S --work build/stage1-known prove         # then certify, alive, refute and report
$S --work build/stage1-head pairs          # G0 and G1, on a fresh WORK
$S --work build/stage1-head prove --eligible-only   # then certify, alive --eligible-only and report
$S publish                                 # results/summary.json, from the three summaries
```

Each stage's record carries a key: the pair's id, the hashes of its input, source and target IR, and the toolchain's,
the emitter, `IRLean`'s library, Lean, the checkers, everything `tools/binding.py`'s verdict rests on by its own
account, its checker, `opt`, `leanchecker` and Lean's toolchain among them, the gate and `alive-tv`. A record whose key
isn't the pair's now is
ignored: the stage does the pair again, and the report never counts it. A certificate counts only beside the current
proof of the same pair. `--upto N` keeps a stage to the first `N` changed pairs in the order of their ids. An id is a SHA-256 of the test and the
function, so that's a uniform sample, the same every run, and each larger one holds the smaller. Without it, a stage
takes every pair. Each stage skips pairs it has done, so a long run can stop and go on. Run the heavy stages through
`tools/measure.py run --heavy`, as [the corpus](corpus.md#measuring-a-heavy-job) says. `report` writes `summary.json`,
with every count and the toolchain's hashes.

The raw results, the generated Lean and the bundles stay in `build/`, which git ignores.
[`bench/instcombine/results/summary.json`](../bench/instcombine/results/summary.json) is the summary of the run below.

## The test

`ctest`'s `stage1` runs `stage1.py ci` on [`bench/instcombine/fixture/`](../bench/instcombine/fixture/): five functions
from an InstCombine-style test, one of them a dropped `freeze`, and three known miscompilations, through every stage, against `expect.json`. It fails if
any pair's verdict differs, or if a known-wrong pair is proved or certified, whatever `expect.json` says. On copies of the
run's records, it also changes one certified pair's target hash, and has another's latest proof fail, and each has to
lose its certificate, and with `tools/binding_check.lean` changed, none may keep one. It runs in CI's `binding` job,
alone, one Lean process at a time.
