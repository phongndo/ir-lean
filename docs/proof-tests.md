# Proof tests

A proof test states a property of compiled code once, and escalates: tier 1 runs it on generated inputs for a
counterexample, tier 2 proves it within a bound, and tier 3 proves it outright, from stored lemmas. It never reports a
pass it hasn't earned. That's the second product in the [roadmap](roadmap.md#one-engine-two-products), next to
proved superoptimization, and [Phase 7](roadmap.md#phase-7-proof-tests) has its milestones.

This page has tier 1, which is built, in [`tools/prooftest/`](../tools/prooftest), what it measured against milestone
T1, and the design of tiers 2 and 3, which aren't built. For what any result here means, see [trust](trust.md).

Facts here were checked on 2026-11-08, on top of commit `9d13699`, with Lean 4.35.0 and clang 23.1.3, on x86-64 Linux
with 32 cores, in the dev shell.

## An example

From the repo, after `lake build` and building `build/ir-lean`, in `nix develop`. `tests/prooftest/Cases.ll` has a
function `low16` that keeps the low 16 bits of its argument. Claim, wrongly, that it returns its argument:

```console
$ tools/prooftest/prooftest.py run --ir tests/prooftest/Cases.ll --namespace Cases --function low16 \
    --statement '∀ (x : BitVec 32), Cases.low16 (some x) = IRLean.Outcome.ok (some x)' --pretty
```

That prints, shortened here:

```json
{
  "schema": "ir-lean.prooftest/1",
  "tier": 1,
  "status": "counterexample",
  "reason": "kernel_refuted",
  "exit_code": 2,
  "proved": false,
  "counterexample": {
    "assignment": {"x": "65536#32"},
    "shown": {"x": "0x10000#32"},
    "instance": "Cases.low16 (Option.some 65536#32) = IRLean.Outcome.ok (Option.some 65536#32)",
    "evidence": ["kernel"],
    "kernel": {"ok": true, "axioms": ["propext", "Classical.choice", "Quot.sound"], "calls_rewritten": 1},
    "found": {"phase": "edges", "index": 2, "assignment": {"x": "4294967295#32"}},
    "shrink_steps": 20
  },
  "inputs": {"tried": 3, "satisfied": 3, "discarded": 0, "seed": 0, "max_inputs": 10000},
  "timing": {"verify_setup_seconds": 1.01, "harness_start_seconds": 0.74, "search_ms": 0.15, "shrink_ms": 2.3,
             "kernel_ms": 2.95, "to_counterexample_ms": 5.71, "total_seconds": 1.84}
}
```

The third input it tried, all ones, failed. Shrinking took it to `0x10000`, the least failing input, and the kernel
checked a theorem that the statement is false there. The next run of the same property tries `0x10000` first.

Give it a right statement, with `x &&& 0xFFFF#32`, and it answers `passed_tier1`, with `proved: false`, after
10,000 inputs, which took Lean 61 ms. That's a test, not a proof.

## Tier 1

### What it does

1. **Set up.** It hands the input, the function and the statement to [`tools/verify.py`](verify.md) with no proof and
   no witness. That compiles the C, checks the IR, translates the function, compiles the generated module with code,
   and checks that the statement elaborates and names the function. Its answer is then `error/not_proved`, and
   anything else stops the proof test with verify's reason, such as `function_unsupported`.
2. **Start the harness.** [`tools/prooftest/Harness.lean`](../tools/prooftest/Harness.lean) runs in one Lean
   process, importing only Lean, `IRLean` and the generated module, as verify's pinned statements are elaborated. It
   turns the statement into one compiled function from the inputs to `0` (a hypothesis is false), `1` (the
   conclusion holds) or `2` (it doesn't), and answers requests on stdin, one a line.
3. **Plan inputs** for each binder, in this order: failures stored for this property, then edge cases, then bit
   patterns, then every byte, then seeded random values, up to `max_inputs` after the stored ones. If every input
   fits in `max_inputs`, it plans every input instead, edges and patterns first.
4. **Search** the plan in order, and stop at the first input that fails.
5. **Shrink** that input, deterministically, to one that still fails and is simpler.
6. **Confirm** it in the model: the kernel, or else `tools/verify.py`. Only a confirmed failure is a counterexample.
7. **Store** it, keyed by the property, so the next run tries it first.

| Field | Meaning |
| --- | --- |
| `input`, `function`, `namespace`, `statement` | As [`tools/verify.py`](verify.md#a-request) takes them. The statement is the property |
| `seed` | The seed for random inputs. Default 0 |
| `max_inputs` | How many inputs to plan, after stored ones. Default 10,000 |
| `min_satisfied` | How many inputs have to meet the hypotheses for a pass, unless every input ran. Default 10 |
| `shrink` | Default true |
| `store` | A directory of failing inputs, or `null`. Default `build/prooftest/store` |
| `verify_confirm` | `auto`, `always` or `never`: when `tools/verify.py` confirms a counterexample. `auto` asks it only when the kernel couldn't. Default `auto` |
| `limits` | `timeout_seconds`, default 300, `memory_mb`, default 4,000, and `input_timeout_seconds`, default 2 |

A request can be a JSON file: `tools/prooftest/prooftest.py run request.json`. `tools/prooftest/prooftest.py
capabilities` prints the contract as JSON. The API is `prooftest(request, base, tool, work)` in
`tools/prooftest/prooftest.py`, which the command line is a thin layer over. Each run keeps a directory, under
`build/prooftest/runs/` unless `--work-dir` says where, with verify's setup run, the harness and its config, any
confirmation run, `request.json` to rerun it and `result.json`.

### Statuses

Four statuses, each with an exit code. None of them is `proved`: tier 1 proves nothing, and every result says
`"proved": false`.

| Status | Exit | Means |
| --- | --- | --- |
| `passed_tier1` | 0 | Tested, not proved. No input tried made the statement false. An input not tried may |
| `counterexample` | 2 | The statement is false on the input given, in the model, confirmed as `evidence` says |
| `vacuous` | 3 | No input tried met the hypotheses, so nothing was tested |
| `unknown` | 1 | Nothing was decided |

| Reason | Status | Means |
| --- | --- | --- |
| `sampled` | `passed_tier1` | Every planned input ran, none failed, and at least `min_satisfied` met the hypotheses |
| `exhaustive` | `passed_tier1` | Every input the binders' types allow ran, and none failed. Still compiled evaluation, not a proof: [tier 2](#tier-2-bounded-proofs) is where that becomes one |
| `kernel_refuted` | `counterexample` | The kernel checked a theorem `¬ statement` built from the input |
| `compiled_evaluation` | `counterexample` | The kernel couldn't, and `tools/verify.py` confirmed it by running the model's compiled code |
| `no_input_meets_hypotheses` | `vacuous` | Every input tried made a hypothesis false |
| `too_few_satisfying` | `unknown` | Fewer than `min_satisfied` inputs met the hypotheses, which QuickCheck calls giving up |
| `input_timeout` | `unknown` | An input's run didn't finish in `input_timeout_seconds`, and nothing failed |
| `evaluation_crashed` | `unknown` | Evaluating an input stopped Lean, and nothing failed |
| `time_limit` | `unknown` | `timeout_seconds` ran out before the plan had run |
| `memory_limit` | `unknown` | Lean ran past `memory_mb` |
| `unconfirmed` | `unknown` | An input failed in the search, and neither the kernel nor `tools/verify.py` confirmed it |
| `confirmation_disagrees` | `unknown` | An input failed in the search, and the confirmation found the statement true there: a bug in this tool, Lean's compiler or IRLean's code |
| `binder_unsupported` | `unknown` | A binder isn't `BitVec w`, `IRLean.Val w` or `Bool`. Memory is one |
| `undecidable` | `unknown` | Lean can't decide the statement at an input |
| `statement_unsupported` | `unknown` | The statement uses a hypothesis's proof, or needs an instance Lean can't find |
| `statement_invalid`, `statement_not_about_target`, `function_unsupported`, `function_not_found`, `compile_failed`, `ir_invalid`, `input_not_found`, `toolchain_missing`, `generated_module_failed` | `unknown` | `tools/verify.py` gave this reason in setting up. [Verify](verify.md#the-contract) says what each means |
| `tool_failed` | `unknown` | A tool crashed, or verify answered something this doesn't expect |
| `invalid_request` | `unknown` | The request is malformed |
| `internal_error` | `unknown` | A bug in this tool, including a result that breaks the contract below |

In order of precedence: a confirmed counterexample, then what stopped the run, then a failure nothing confirmed,
then an input that didn't finish, then a limit, and only then what the inputs that ran say. So a run that hit a limit,
or had an input that never finished, is never a pass, even if every other input passed: a run that never ends is how
the model says `none`, or, under a promise to progress, undefined behavior, and either makes a claim of
`= Outcome.ok` false. Running can't show a run never ends, so such an input is `unknown`, never a counterexample. A
counterexample found after an input that hung still counts, since it's decisive.

A second function, `assert_contract`, turns any result that breaks these rules into `unknown/internal_error` before
it's printed: a pass with `proved` true, a pass or `vacuous` with an input that didn't run, a counterexample with no
evidence or with kernel evidence the kernel didn't give, or a counterexample with any other status.

### Inputs

Binders whose type is a proposition are hypotheses. The others have to be `BitVec w`, `IRLean.Val w`, which is
`Option (BitVec w)` with `none` as poison, or `Bool`, with `w` a numeral. Instance binders are synthesized.

- **Edges:** 0, 1, all ones, the signed minimum and maximum, 2, all ones but the lowest bit, the signed minimum plus
  one, and 3, with poison third for `Val`. With several binders, every combination, up to 512, and past that each
  edge of each binder at least once.
- **Patterns:** repeated bytes `0x55`, `0xAA`, `0x0F`, `0xF0`, `0x33`, `0xCC`, `0x01`, `0x80`, `0x7F`, `0xFE` and
  `0x11`, each single bit, runs of ones from the bottom and from the top, and all ones but one bit, with the other
  binders cycling through their own edges and patterns. With several binders of one type, also the same value in
  each.
- **Every byte,** 0 to 255, for each binder wider than 8 bits, with the other binders cycling through their edges.
  Code about characters, such as `isblank`, often differs on one byte only.
- **Random,** seeded: a mix of uniform values, small ones, ones near all ones, a few bits set, a few bits clear, and
  an edge or pattern give or take 3, and poison one time in 20 for `Val`.
- **Every input,** when there are no more than `max_inputs`: one `BitVec 8` is 256, and one `Val 8` 257.

`superopt.py`'s `inputs()` was the start of this, as the [prior-art study](prior-art.md#proof-tests) suggests. Lean's
Plausible isn't used: it admits the goal when it finds nothing, and its default `BitVec` generator never tries a value
above 99, so never `0xFFFFFFFF` or the signed minimum.

**Results stated as `∃`.** A spec such as `∃ r, f x = IRLean.Outcome.ok (some r) ∧ r < 64#32` is natural, and Lean
decides an `∃` over `BitVec 64` by trying every value, which never ends. The equation pins `r`, so when a conclusion
has that shape, with or without the `∧`, the harness decides it by running `f x` once and checking the rest at its
result. It proves that this decides the same thing, `okSomeThen_iff`, and the kernel's refutation uses it too.

**The vacuity guard.** An input that makes a hypothesis false is discarded, and counted. If none meets them, the
answer is `vacuous`, never a pass. If some do but fewer than `min_satisfied`, it's `unknown/too_few_satisfying`,
unless every input ran.

**Shrinking** replaces one value at a time with a simpler one that still fails, until none does: zero, one, half,
the lowest or highest set bit cleared, one less, its negation, each set bit cleared, and shifts right. Simpler means
fewer bits in all, then smaller values, so it ends. Poison stays poison. The candidates go to Lean simplest first, in
one batch a round, and the first that fails is kept, so the same input always shrinks to the same result.

**The store** keeps failing inputs in one JSON file a property, under a key that hashes the elaborated statement and
its binders, and not the code: a fix to the code keeps its old failures, and the next run tries them first, as
Hypothesis's database does. The prior-art study suggested keying by the generated module's hash too. That would never
try an input again on the code that was meant to fix it, so each entry records the module's hash instead. A stored
input that no longer fits the binders is skipped. Writes go through a rename.

### Confirming a counterexample

The search decides each input by running compiled code: the statement, compiled once by `evalExpr`, interpreting the
generated module and running `IRLean`'s own code natively, as `tools/verify.py` does for witnesses. That trusts Lean's
compiler and runtime, as `native_decide` does, and a bug there could make an input fail, or hide one that does. So a
failing input counts only once something else confirms it.

**The kernel, `kernel`.** The harness builds a theorem that the statement is false at the input, and has the kernel
check it, with `Environment.addDeclCore`, in the same Lean process. The obstacle is that every emitted function runs
its blocks through `IRLean.run`, a `partial_fixpoint`, which the kernel can't unfold: its definition goes through a
least fixed point and classical choice. So the harness defines `runFuel`, the same loop with fuel, by structural
recursion the kernel can evaluate, and proves once that a run that finishes within its fuel is the run:

```lean
theorem run_eq_runFuel (step : β → Outcome (Next β ρ)) (n : Nat) (b : β)
    (h : (runFuel step n b).isSome = true) : run step b = runFuel step n b
```

A function under a promise to progress, `mustprogress`, `willreturn` or a loop marked `llvm.loop.mustprogress`,
runs as `promised (run step b) d` since [#62](https://github.com/phongndo/ir-lean/pull/62), where `d` says what a run
that never finishes does: it's undefined. A run that finishes is the run whatever `d` says, so a second lemma,
`promised_run_eq_runFuel`, gives `promised (run step b) d = runFuel step n b` from the same `h`.

For each call of a generated function in the instance, it unfolds the call to `run step b`, or to
`promised (run step b) d`, proves it equal to `runFuel step 1000000 b` with `h` by `rfl`, rewrites the instance with
that, and proves what's left false by `decide`. Then it applies that to the statement at the input. The kernel checks all of it: the fuel run finishing,
every block it took, and the conclusion. The answer lists the theorem's axioms. Every one in the measurements below
rested on `propext`, `Classical.choice` and `Quot.sound` only.

**`tools/verify.py`, `compiled_evaluation`.** When the kernel can't, `prooftest.py` asks
[verify](verify.md#counterexamples), which elaborates the statement again on its own, substitutes the input as a
witness, and decides it by compiled code. That's an independent path from the search, so it catches a bug in how the
harness builds its decision, but not one in Lean's compiler. The kernel can't follow a call made inside a block to
another function that runs blocks of its own, such as `outer` calling `inner` in `Cases.ll`, since only calls in the
statement are rewritten. With `verify_confirm: always`, verify confirms every counterexample, kernel or not. Verify can't decide a spec
stated as `∃ r, f x = Outcome.ok (some r) ∧ …`: it tries every `r`, and runs out of time, so for those the kernel is
the only confirmation, and `verify_confirm` gives verify 60 s.

If the confirmation finds the statement true at the input, the answer is `unknown/confirmation_disagrees`, never a
counterexample. If neither confirms, it's `unknown/unconfirmed`, and the candidate is in the result's `candidate`.

Both confirm the counterexample in the model. Whether the model is faithful to LLVM, and whether the C means what the
IR says, are outside this, as [trust](trust.md#what-a-theorem-covers) says.

### Limits

- **Memory.** A function that takes memory has a `Mem` or a pointer among its binders, and comes back
  `unknown/binder_unsupported`. Tier 1 can't generate memory, and running the model on it is slow: `Mem` is a chain
  of closures, so each access walks back through earlier writes, which kept the zlib differential test to inputs of
  about 800 bytes ([status](status.md)). The executable memory model, milestone E2, is the fix, and generators for
  buffers come after it.
- **Statements** can name Lean's libraries, `IRLean` and the generated module, and nothing else, as verify's pinned
  statements can. A spec written with definitions of its own, such as `pop` in `tests/proofs/Popcount.lean`, has to be
  stated with core's, such as `BitVec.cpop`, or it comes back `unknown/statement_invalid`.
- **Setup costs about 2 s** a property: verify's setup, about 1.2 s, and starting the harness, which imports `Lean`,
  about 0.9 s. The search itself takes milliseconds. Keeping one harness for many properties of one module would cut
  most of that, for [C2](roadmap.md#phase-8-speed).
- **Integer binders only,** of literal widths. A width-generic statement, `∀ w`, isn't tier 1's, and neither is an
  `IRLean.Choice`, which a function with a `freeze` takes since F3.

## T1, measured

Milestone T1 in the [roadmap](roadmap.md#phase-7-proof-tests): for the bugs injected into the C that each make a proof
stop checking, and the negative corpus's wrong rewrites, tier 1 finds a counterexample to each it can run, at a median
under 100 ms, each one it can't run comes back unknown, and a test shows a timeout, an unsupported function and a
resource limit each come back unknown, never as a pass.

Measured on 2026-11-08 on this branch, on top of `9d13699`, which has [#62](https://github.com/phongndo/ir-lean/pull/62)'s promises, with

```console
tools/prooftest/bench.py --workers 4 --verify-confirm always --check-equivalent --deep 1000000 --check-t1
```

under `tools/measure.py run --heavy`, four properties at a time, in 628 s. Every property ran with the defaults:
10,000 inputs, seed 0. It writes every result to `build/prooftest/bench/results.json`, which isn't committed. The bugs
are of four kinds:

- the 100 that [`tests/llvm/targets.toml`](../tests/llvm/targets.toml) injects into the C and C++ it proves, each of
  which `tests/llvm.py` requires to stop its proof;
- 129 more, 3 in each of the 45 compiler-rt builtins without memory, in
  [`tools/prooftest/variants.toml`](../tools/prooftest/variants.toml): every simple operator change in the builtin's
  body that changes its IR, each to IR no other one gives, sampled with a recorded seed;
- the 16 that [`tests/proofs.sh`](../tests/proofs.sh) injects, which are T1's own set, in
  [`tools/prooftest/t1.toml`](../tools/prooftest/t1.toml);
- the 24 cases of [the negative corpus](llvm-negative-verification.md), with the claim each pins.

Each property is the statement of the theorem the bug stops, read from its header.

| Bugs | Refuted | Can't run, so unknown | Missed |
| --- | --- | --- | --- |
| `targets.toml`, 100 | 78 | 22 | None |
| Compiler-rt variants, 129 | 121 | None | 8, none shown to change anything |
| `tests/proofs.sh`, 16 | 1 | 15 | None |

**Every counterexample was confirmed by the kernel,** 207 of 207, each theorem resting on `propext`,
`Classical.choice` and `Quot.sound` only. `tools/verify.py`, asked as well, confirmed 202 of them. It ran out of time on
the other 5, which are `∃` specs it can't decide, and it contradicted none.

**No false alarm.** Each property also ran on the function without a bug, where its theorem is proved: 79 passed
tier 1, 78 after 10,000 inputs and one exhaustively, and 8 came back unknown, for the reasons below. None came back
`counterexample`.

**The negative corpus** came out as `tools/verify.py` is expected to answer it, which `--check-t1` checks. This is
before F3, which changed its `freeze` cases, [below](#the-negative-corpus-since-f3):

| Cases | Tier 1 |
| --- | --- |
| `wrong_mul2_to_shl2`, `poison_add_nsw_introduced`, `freeze_removed`, `freeze_duplicated`, `precondition_insufficient` | `counterexample`, at `x` = 1, 127, poison, poison and 128 |
| `freeze_added_unmodeled`, right in LLVM, but not in the model, where `freeze` of poison stops | `counterexample`, at poison |
| `proof_for_other_target`, whose claim is about a wrong rewrite, `tgt_bad` | `counterexample`, at 1 |
| `wrong_loop_deleted`, and `wrong_promise_added`, which adds `mustprogress` to a loop that never ends at 0, each refuted only by a run that never ends | `unknown/input_timeout` |
| `undef_in_target`, and until SEM-05's second slice `float_fadd_zero_removed` | `unknown/function_unsupported` |
| `freeze_duplicated_equality_pin`, wrong in LLVM, but pinning an equality that holds in the model | `passed_tier1/exhaustive` |
| `precondition_vacuous` | `vacuous` |
| The 4 controls, and the 7 cases about certificates and limits, whose claims are right | `passed_tier1/exhaustive` |

### The negative corpus since F3

On 2026-11-09, F3 made `freeze` of poison a value each run chooses, through `IRLean.Choice`
([refinement](refinement.md#runs-that-make-choices)). A claim about a function with a `freeze` quantifies over its
choices: the target's as a binder, and the source's as `∃`. Tier 1 generates no `Choice`, and can't decide an `∃` over
one, so it answers those claims `unknown`, and `--check-t1` counts a case it can't run as unknown, as it does for
`tests/proofs.sh`. Measured on 2026-11-09 with `tools/prooftest/bench.py --sets negative --check-t1 --workers 2`, in
30 s, the cases that changed:

| Cases | Tier 1 |
| --- | --- |
| `freeze_removed`, wrong, whose source makes choices | `unknown/undecidable` |
| `freeze_duplicated`, wrong, whose target's choice is a binder | `unknown/binder_unsupported` |
| `freeze_duplicated_equality_pin`, wrong, pinning an equality for one way of choosing, which is false | `counterexample`, at poison |
| `control_freeze_added`, until F3 `freeze_added_unmodeled`, right, whose target's choice is a binder | `unknown/binder_unsupported` |
| `control_freeze_noundef_removed`, right, whose source makes choices | `unknown/undecidable` |
| `float_fadd_zero_removed`, wrong, whose source's `fadd` makes a choice of a NaN since SEM-05's second slice, measured the same way on y on 2026-11-09 | `unknown/undecidable` |

The rest answered as above. 5 were refuted, each confirmed by the kernel: `wrong_mul2_to_shl2`,
`poison_add_nsw_introduced`, `precondition_insufficient`, `proof_for_other_target` and
`freeze_duplicated_equality_pin`. The two wrong `freeze` rewrites tier 1 can't run are refuted by kernel-checked
theorems in [`tests/freeze/FreezeModel.lean`](../tests/freeze/FreezeModel.lean). Generating a `Choice` would let tier
1 run a claim where only the target makes choices, such as `control_freeze_added`. One with `∃` over the source's
choices would stay undecidable at an input.

### Time to a counterexample

From the first input sent to Lean to a shrunk counterexample the kernel has checked, over the 207:

| | Median | 90th percentile |
| --- | --- | --- |
| All | 9.1 ms | 46.8 ms |
| T1's set: `tests/proofs.sh` and the negative corpus, 8 | 10.4 ms | 11.3 ms |
| Compiler-rt, from `targets.toml` and the variants, 167 | 9.9 ms | 51.1 ms |
| The search alone, as Lean timed it | 0.3 ms | 0.5 ms |
| Shrinking | 0.1 ms | 28.0 ms |
| The kernel's check | 5.7 ms | 10.4 ms |

So T1's threshold, a median under 100 ms, holds with room, and most of the time is the kernel's check. 61 of the 199
bugs refuted in `targets.toml` and the variants failed on the first input tried, 156 within 10, 195 within 100, and all
within 1,000. 186 failed on an edge, 11 on a bit pattern, one on a byte and one in an exhaustive run.

**Setup isn't in those times,** and it's most of what a person waits for: a median of 2.0 s a property, for
`tools/verify.py` to compile and check the module and for the harness to start. A property that passes takes about
2.3 s in all. With `verify_confirm: always`, verify's confirmation adds a median of 2.0 s.

The slowest, 117 s, was `llvm::isUIntN`'s bug: its spec computes `2 ^ n.toNat` for a 32-bit `n`, which takes about
0.3 s an input, and the 365th input failed. The same spec without the bug ran out of its 300 s after 1,262 inputs,
so it's `unknown/time_limit`. That's the spec's cost, not the model's.

### What it can't run

- **Memory: 34 bugs.** 19 of `targets.toml`'s are in functions with memory, `APInt`'s three, `decodeULEB128`,
  `crc32`, `xxh3_64bits` and `__udivmoddi4`, and so are the 15 zlib bugs of `tests/proofs.sh`. Their theorems use
  predicates about memory from the proofs' own modules, or names Lean binds automatically in a theorem's header, so as
  statements they don't elaborate: `unknown/statement_invalid`. Stated otherwise, they would still come back
  `unknown/binder_unsupported`, as `tests/prooftest_test.py` shows for a load.
- **3 libc bugs** move a `case` in `isdigit`, `islower` and `isupper`, and clang then compiles the `switch` to a table
  in a global. The function reads memory, its type changes, and the property no longer fits it:
  `unknown/statement_invalid`.

### What it missed

All 8 misses are compiler-rt variants. Each passed 10,000 inputs, and again 1,000,000.

- **6 are equivalent:** the builtin's own theorem still proves each of them, with its proof unchanged. `__addvsi3`,
  `__addvdi3` and `__addvti3` turn `s >= a` into `s > a`, and `__subvti3` turns `s <= a` into `s < a`, where they
  differ only at `s == a`, which that branch rules out. In `__negvsi2`, two changes to the shift that makes the
  minimum leave clang's IR still right.
- **2 change only what the result doesn't use,** as far as reading the code goes: `__umodsi3`'s `carry = s & 2` and
  `__umoddi3`'s starting `carry = 1` change quotient bits, which `__umodXi3` never returns. Their proofs stop, but a
  proof stopping shows only that it depends on the code, and no input of a million tells them apart. Nothing here
  proves they're equivalent. Tier 2 would.

The first full run, on the same bugs, missed one more and timed out on five: `isblank`'s bug differs from the original
only at `c = 9`, a tab, which no generator reached, and five `MathExtras` specs are stated as `∃ r, …`. The byte phase
and the handling of `∃` came from those, so they were added after seeing this set, and the numbers above are from a
later run, with both.

### Where the model's speed limits inputs

Running the model on integer code is cheap: over the 79 properties that passed, a median of 9.9 µs an input, and at
most 35.7 µs, for `__ffsti2` on 128 bits, which is why the default is 10,000 inputs. What limits input size
is memory. Tier 1 doesn't generate memory at all yet, and when it does, `Mem` as a chain of closures makes each access
walk back through earlier writes, which kept the zlib differential test to about 800 bytes. The executable memory
model, E2, is the fix.

### In CI

`prooftest_t1` runs `tools/prooftest/bench.py --sets proofs_sh,negative --check-t1`, T1's own set, on every pull
request, and fails unless each bug it can run is refuted, each one it can't is unknown, a true claim is never refuted,
and the median is under 100 ms. `prooftest` shows a timeout, an unsupported function and a memory limit each come back
unknown, never as a pass. The rest of the measurement above takes about 10 minutes on 32 cores, so it isn't in CI.

## Tier 2: bounded proofs

Not built. This is the design.

A tier-2 result is a proof that holds within a bound, which says what bounded it, and becomes `proved` only when
something shows the bound was enough. That's CBMC's and Kani's unwinding assertions: CBMC runs "with the
–unwinding-assertion flag which ensures that we have fully unwound loops", and Kani calls an insufficient bound
"inconclusive beyond the given depth" ([prior art](prior-art.md#proof-tests)).

**Statuses.** Two new ones, so the schema becomes `ir-lean.prooftest/2`:

| Status | Means |
| --- | --- |
| `bounded` | A kernel-checked proof that the statement holds within the bounds in `bounds`, which name what's left out. Not `proved` |
| `proved` | A kernel-checked proof of the statement, with no bound left. `tier` says which tier gave it, and `reason` how |

`bounds` is a list, such as `[{"kind": "fuel", "steps": 64}]`. The kinds are `fuel`, the blocks a run may take,
`width`, the widths of a width-generic statement, `domain`, a subset of inputs, and later `input_length`, a buffer's
size, as AWS-LC names its `InputLength` bounds. A result is `proved` only with reason `bounded_complete`, when the
proof also shows nothing lies outside the bounds, or `kernel_checked`, from tier 3.

**What it tries,** cheapest first, after tier 1 found no counterexample:

1. **Every input, in the kernel.** When tier 1's plan was exhaustive, the same `runFuel` rewrite gives a theorem for
   all of them: `decide` over `∀ x : BitVec 8`, with `(runFuel step n b).isSome` part of what's decided, so the kernel
   also checks that every run finished. That's `proved/bounded_complete`, with the bound `domain` covering the type.
   Tier 1's kernel check of one input of a small function takes about 5 ms, so 256 inputs would take on the order
   of a second, an estimate that hasn't been measured.
2. **Unrolling, with an unwinding assertion.** Unfold `run` symbolically `k` times, as `llvm_step` in
   [`tests/llvm/Kit.lean`](../tests/llvm/Kit.lean) unfolds one block, and generalize each `run` still left into a fresh
   variable. Then `bv_decide`:
   - proves the statement with those variables free: it holds whatever the unfinished runs do, so
     `proved/bounded_complete`;
   - or proves that the paths reaching them are infeasible, which is the unwinding assertion, together with the
     statement on the rest: also `proved/bounded_complete`;
   - or proves only the statement on paths that finish within `k`: `bounded`, with `{"kind": "fuel", "steps": k}`
     and reason `bound_insufficient` if the unwinding assertion failed;
   - or finds a counterexample: tier 1's confirmation runs on it, and if it's confirmed, the answer is
     `counterexample`, tier 2. A property tier 1 passes and tier 2 refutes is reported refuted, as T2 asks.
   `k` starts at the loop's trip count where the width bounds it, such as 32 or 64 for `popcount` or division one bit
   at a time, and doubles up to a limit.
3. **Small widths** for a width-generic statement: tier 1 at each width up to a bound, then `bv_decide` at each.
   `bounded` with `{"kind": "width", "max": 16}`, never `proved`: checking small widths is proved to be enough only
   for narrow fragments, as the prior-art study found.

**What counts.** Every `bounded` or `proved` result is a theorem file the engine writes, checked by
`tools/verify.py` with the statement pinned, so `proved` here is verify's `proved/kernel_checked`, with all its checks.
A `bv_decide` proof rests on its per-call axiom, which verify allows and [lists](verify.md#reading-a-result). A
request can ask for the standard axioms only, as Trivet and Aqueduct do, and then a `bv_decide` proof is `bounded` at
best, with reason `nonstandard_axioms`, until tier 3 proves it without.

**Escalating.** `vacuous` stops: there's nothing to prove that matters. `counterexample` stops. `bounded` goes on to
tier 3. Each result keeps what the tiers below saw, in `tiers`, so a `bounded` result still says how many inputs tier 1
tried.

**Tier 2's own limits.** `bv_decide` doesn't scale to wide multiplication or division, and unrolling a loop with an
input-dependent trip count doesn't finish. Both end at `bounded` or `unknown`, never `proved`.

## Tier 3: proofs from the lemma store

Not built. It builds on [the lemma store](lemma-store.md), milestone E1, which
[#60](https://github.com/phongndo/ir-lean/pull/60) added: `tools/store/store.py lookup --statement` finds stored lemmas
that prove a statement exactly or by instance, and importing `LemmaStore.Select` registers the store with Lean's
premise selection, so `grind +suggestions`, `simp? +suggestions` and `try?` see it.

A tier-3 result is `proved/kernel_checked`, with no bound: the statement for every input.

**What it tries,** on a property tier 2 left `bounded`, in order:

1. **Symbolic execution into goals about `BitVec`s.** `llvm_exec` and `llvm_close`, from
   [`tests/llvm/Kit.lean`](../tests/llvm/Kit.lean), moved somewhere a proof test can import, run the blocks with
   symbolic inputs until what's left is goals about values. This is how most of the 46 compiler-rt proofs in
   `tests/llvm` start.
2. **Exact lemmas.** Each goal goes to `store.py lookup`. An exact match or an instance whose side conditions
   `decide` closes is used directly.
3. **Premise selection.** `grind +suggestions`, with the store's selector first and Lean's default after, on what's
   left.
4. **Loops** need an invariant: a lemma that the loop's block, run from any state meeting it, ends where the spec
   says, as `popcount_loop` is for `tests/proofs/Popcount.lean`. The store keeps such lemmas by the loop's shape, and
   a loop with none in the store stays `bounded`.

The engine writes the proof, and `tools/verify.py` checks it with the statement pinned. A `sorry`, an axiom or a proof
of something else can't pass, for the reasons [verify](verify.md#what-proved-rests-on) gives.

**When it fails,** the answer stays `bounded` from tier 2, with what tier 3 found, as Why3 tells a code bug from a weak
contract:

| Reason | Means |
| --- | --- |
| `lemma_missing` | A goal no stored lemma or selector closed. The goal is in the result |
| `invariant_missing` | A loop with no invariant in the store |
| `search_exhausted` | A time or heartbeat limit ran out |

None of these says the statement is false. Only tiers 1 and 2 can say that, with a counterexample.

**Feeding the store.** A tier-3 proof is cut into lemmas, as [lemma reuse](lemma-reuse.md) prototypes, and offered to
`store.py add`, which admits each one or keeps it as a candidate under the [bar](roadmap.md#the-flywheel). That's the
flywheel: each proof test that reaches tier 3 makes the next one cheaper.

## What's next

After T1. Since 2026-11-09, tiers 2 and 3 wait until chunk 1's G2 is producing lemmas, and the waves are replaced by
the roadmap's [platform track and chunks](roadmap.md#next-steps):

- **Tiers 2 and 3,** milestone T2, as designed above. Tier 2's exhaustive kernel proof and unrolling need nothing new
  in `IRLean`. Tier 3 needs `llvm_exec` where a proof test can import it, and the store, which is in.
- **The unit-test milestone,** T3: compiler-rt's builtins against their own unit tests in
  `compiler-rt/test/builtins/Unit`, scored by injected bugs, as the [prior-art study](prior-art.md#proof-tests)
  proposes. `popcountsi2_test.c` tries 6 edge values and 10,000 `rand()` values, which never set bit 31.
- **Memory,** after the executable memory model, E2: generators for buffers, and a faster `Mem` to run them on.
- **One harness for many properties,** to cut the 2 s of setup each pays, for C2.
