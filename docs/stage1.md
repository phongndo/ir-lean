# Stage 1: InstCombine's rewrites, certified and compared with Alive2

Stage 1 of [proved superoptimization](roadmap.md#phase-4-certified-translation-validation-and-superoptimization), as
[the gate](prior-art.md#the-gate) narrowed it: InstCombine's own regression tests read through the emitter, each rewrite
certified with `bv_decide` at fixed widths, every verdict compared with Alive2's, and a corpus of known miscompilations
that must never get a certificate. The harness is [`bench/instcombine/stage1.py`](../bench/instcombine/stage1.py). For
what any theorem means, read [trust](trust.md) first.

**This proves no optimization.** A certificate here is translation validation of one `opt` run on one function, as
[binding](llvm-proof-binding.md) says. It says nothing about InstCombine on any other input, or about its C++.

RESULTS

## What a verdict means

Each pair is one function from one test: the function before `opt -passes=instcombine`, and after. It gets one verdict
from `ir-lean`, from the gates only, and one from Alive2.

| `ir-lean` verdict | Means | From |
| --- | --- | --- |
| `certified` | A bound certificate: `IRLean.Refines Src.f Tgt.f`, kernel-checked, bound to the input, the `opt` run and the toolchain, and replayed from scratch | [`tools/binding.py`](llvm-proof-binding.md) `verify` said `bound`, with exit code 0, about this pair's input, function, pass spec and claim kind `ir_instance_refinement` |
| `proved` | The same theorem, kernel-checked, for every input that's a value or poison. Not a certificate: an argument without `noundef` can be `undef`, which this doesn't cover | [`tools/verify.py`](verify.md) said `proved` with the statement pinned, and the [negative-verification gate](llvm-negative-verification.md#the-gate) found no reason to refuse it |
| `refuted` | The model's counterexample: on some input, the target does what the source doesn't allow, and neither side stops the model there | `tools/verify.py` decided a witness false by running the model, and a second run on that witness found no model stop |
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
only when every argument is `noundef` in the source and the target IR has no `mustprogress` or `willreturn`.

`refute` runs the model, through `tools/verify.py`, on each pair the automation didn't prove, with scalar arguments and
result: Alive2's counterexample first, if it has one, then up to 64 edge values, poison among them. The statement is the
decidable form of refinement the [negative-verification gate](llvm-negative-verification.md#the-claim) uses. A witness
that makes it false is then run once more, to ask whether either side stops the model there. A counterexample through a
model stop is `unsupported`, never `refuted`, since a model stop says nothing about LLVM.

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

## What it rests on

Everything in [trust](trust.md), [verify](verify.md#what-proved-rests-on) and
[binding](llvm-proof-binding.md#what-a-bound-verdict-rests-on), and:

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| `llvm-extract` keeps what InstCombine's rewrite of one function depends on | InstCombine is a function pass, and the module keeps the declarations the function uses. A pair the cut changes is checked against the cut module, which is what a certificate binds | A rewrite that reads another function's body. The pair is then still a real `opt` run, but not the one the whole test made |
| `llvm-link` and renaming to `@src` and `@tgt` don't change what either side means | Each side has one definition, renamed with its uses | A name clash `llvm-link` resolves by renaming a declaration |
| The decidable claim in `refute` is refinement on scalar functions | It's the negative-verification gate's, which its controls prove and its wrong cases refute | A difference from `IRLean.Refines` on some case. A `refuted` verdict is the model's counterexample, decided by running compiled code, as [verify](verify.md#counterexamples) says |
| Alive2's verdicts, at its pinned commit on the shell's LLVM | It's the reference this compares with, not a gate | An Alive2 bug, which a disagreement may show |

## Reproducing it

In `nix develop`, after `lake build` and building `build/ir-lean`:

```sh
bench/instcombine/stage1.py all --sample 50 --seed 1   # a sample, into build/stage1
bench/instcombine/stage1.py all                        # every test
bench/instcombine/stage1.py --work build/stage1-known known-pairs
bench/instcombine/stage1.py --work build/stage1-known prove   # then certify, alive, refute, report
```

Each stage skips pairs it has done, so a long run can stop and go on. Run the heavy stages through
`tools/measure.py run --heavy`, as [the corpus](corpus.md#measuring-a-heavy-job) says. `report` writes
`summary.json`, with every count and the toolchain's hashes.

The raw results, the generated Lean and the bundles stay in `build/`, which git ignores.
[`bench/instcombine/results/summary.json`](../bench/instcombine/results/summary.json) is the summary of the run below.

## The test

`ctest`'s `stage1` runs `stage1.py ci` on [`bench/instcombine/fixture/`](../bench/instcombine/fixture/): four functions
from an InstCombine-style test and three known miscompilations, through every stage, against `expect.json`. It fails if
any pair's verdict differs, or if a known-wrong pair is proved or certified, whatever `expect.json` says. It runs in
CI's `semantics` job, alone, one Lean process at a time.
