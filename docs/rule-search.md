# Rule search

A deterministic search that rewrites real LLVM IR using only [rules](rules.md) already proved for every input, so what
it finds carries its proof: a chain of proved rules, composed by `IRLean.Refines.trans`. It calls no model. It's the
engine's core, by decision 4 of the
[thirteen decisions after #103](roadmap.md#thirteen-decisions-of-2026-11-09-after-103), whose numbers this page uses.
This page is what it does, what it found on the fixtures it was built on, what each part costs, and what it can't do.
For what any theorem here means, read [trust](trust.md) first.

Facts here were checked on 2026-11-10 on top of `df3e997`, on z, a Linux machine with 32 cores and 30 GB shared with
four other lanes through the machine's pool of heavy jobs, in the dev shell, with Lean 4.35.0 and LLVM 23.1.3. On top
of `c0d070c`, the tests and the first three runs [below](#what-it-found-on-the-fixtures) were run again, with the same
results. The run on LLVM's InstSimplify tests wasn't, after [#105](https://github.com/phongndo/ir-lean/pull/105)
changed what the emitter refuses.

## What it found

- **Nothing that counts as a win, and nothing here is counted toward S3's bar or the checkpoint, of
  [decision 8](roadmap.md#thirteen-decisions-of-2026-11-09-after-103).** The search was run only on small files in the
  repo and on LLVM's own regression tests, never on the corpus, which isn't fixed yet, on zlib, on llama.cpp or on any
  outside project.
- **Against `opt -O3`, `llvm-mca` kept none of what it found.** Every rule it has today was cut from InstSimplify's
  proofs, so `opt -O3` makes the same rewrites itself: on all 225 rewrites found in LLVM's InstSimplify tests, both
  sides come out of `opt -O3` and `llc -O3` with the same uOps. That's
  [decision 3](roadmap.md#thirteen-decisions-of-2026-11-09-after-103)'s point, measured: LLVM's rewrites are the base a
  search starts from, not its wins. A win needs a rule LLVM doesn't have.
- **Everything it found was certified.** On LLVM's 190 InstSimplify test files, with every candidate kept, the search
  found 225 rewrites that aren't part of another, using 115 of the 144 rules it can apply, and Lean proved each
  again, as a slice, and 221 of them as the whole function too: [below](#on-llvms-instsimplify-tests). The longest
  chain it found there is three rules. Alive2, asked as a second opinion, finds all 225 correct.
- **The first such run found a bug in the search, which the gate had refused.** Two slices were written with an
  instruction before one it reads, and `opt -passes=verify` stopped them before any proof. It's fixed.
- **It's fast where it's cheap and slow where Lean runs.** Looking at one instruction takes a median 0.4 ms, counting
  uOps 29 ms a candidate, and certifying one chain about 3 s.

## How it works

[`tools/rules/rules.py search INPUT.ll`](../tools/rules/rules.py) does this, for each function of the module:

1. **Reads the function** as `opt -S -passes=instnamer` prints it, so every value has a name. Only scalar integer
   instructions are looked into: the binary operators but the divisions, `icmp`, `select` on an `i1`, the integer
   casts and the integer intrinsics the [format](rules.md#terms) has. Anything else is a line of text that defines a
   value.
2. **Cuts around each instruction,** in the function's order: the instructions it reads within `--depth`
   instructions, 4 by default, through instructions it looks into. The cut is a term. What it reads from outside, an
   argument, a `phi`, a `load`, a division, is a leaf. This is [prior art](prior-art.md#superoptimizer-v2)'s cut with
   a depth bound.
3. **Rewrites the term, breadth first:** a proved rule a step, at any instruction of the term, for at most `--steps`
   steps, 4 by default, and `--states` terms, 2,000. It keeps the term with the fewest instructions, the first found
   among those. A rule is a refinement, which goes one way, so a state is a term and a step is a directed rewrite:
   nothing is merged as an equality, and there's no e-graph.
4. **Reports the longest rewrites only.** A rewrite found around one instruction is often part of one found around an
   instruction that reads it. Each step is known by its rule and the function's instruction it applied at, and a
   rewrite whose steps are all steps of another isn't reported.
5. **Filters with `llvm-mca`.** The cut before and after, each as a function, go through `opt -O3`, `llc -O3` and
   `llvm-mca`, for `--mcpu`, `x86-64-v3` by default, and a candidate is kept only if it takes fewer uOps. So a rewrite
   `opt -O3` makes itself is dropped. `--baseline none` leaves `opt -O3` out, and `--keep all` keeps every candidate,
   labeled with what `llvm-mca` said. uOps only filter: a claim of speed needs wall time on the real workload, as
   [decision 6](roadmap.md#thirteen-decisions-of-2026-11-09-after-103) says, which nothing here measures.
6. **Certifies each kept rewrite,** in [certify mode](rules.md#how-the-matcher-and-the-statement-are-tied): the
   chain's states as IR, the rules' names, and a certificate the kernel checks.

It draws no random number and reads no clock into its result. Every loop runs in the function's, the term's or the
rule files' order. `results.json`, schema `ir-lean.rule-search/1`, has no time, path or host in it, and the test runs
the search twice and compares every byte. Times go to `timing.json`, beside it.

### What a result has

For each kept rewrite, in a directory of its own:

| File | What it is |
| --- | --- |
| `before.ll`, `after.ll` | The module as the search read it, and with the rewrite applied: the new instructions before the rewritten one, each use of it now a use of the new value, and what's dead of the cut removed. `opt -passes=verify` accepts it |
| `slice-before.ll`, `slice-after.ll` | The cut as a function of what it reads, with the function's own lines, and what the chain turns it into |
| `slice/chain.ll`, `slice/Chain.lean`, `slice/ChainCert.lean`, `slice/verdict.json` | The chain's states, what `build/ir-lean` generated from them, the certificate, and the gate's verdict |
| `function/...` | The same about the whole function, where it's tried |

And in `results.json`: the instruction it's around, the chain, each step with its rule and where it applied, the
instruction counts, `llvm-mca`'s uOps, and each certificate's status, claim, axioms and tier.

### Tiers

By [decision 9](roadmap.md#thirteen-decisions-of-2026-11-09-after-103), each result says what's proved and what the
proof rests on:

| Tier | When | What's proved | What's trusted beyond [the usual](rules.md#whats-trusted) |
| --- | --- | --- | --- |
| Slice | Always | `IRLean.Refines Chain.s0 Chain.sk`, where `@s0` is the cut, as a function of what it reads, and `@sk` what the chain turns it into: on every input, poison included | That the cut is what the function computes there, and that replacing it keeps the function's meaning |
| Whole function | Where the function is one block of instructions the search looks into, ending in `ret` of an integer, with arguments that are at most `noundef` | The same claim, where `@s0` is the function itself, under its own `define` line with its name changed, and `@sk` the function rewritten | Nothing more |

Every certificate here rests on the standard three axioms: a rule's proof may not use `bv_decide`, and a
certificate's proof is rules and congruence. The tier's second half, standard axioms or `bv_decide`'s too, is in each
verdict, and is `standard` for all of them.

A function with more than one block, memory or a call gets a slice only. Making those whole-function wins takes the
lemma that a refined cut gives a refined function, and memory in `Refines`, which are F4's.

## What it found on the fixtures

Every input the search has been run on is listed here. Each run kept every candidate, `--keep all`, so that
everything found was certified, and counted uOps against `opt -O3`.

| Input | Files | Functions | Instructions looked at | With a rewrite | Rewrites that aren't part of another | Fewer uOps than `opt -O3`'s | Slices certified | Whole functions certified, of those tried |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| [`tests/rules/search.ll`](../tests/rules/search.ll), written for the test | 1 | 7 | 21 | 12 | 5 | 0 | 5 | 4 of 4 |
| [`tools/corpus/seeds/*.ll`](../tools/corpus/seeds), the corpus's seeds | 10 | 10 | 35 | 5 | 2 | 0 | 2 | 2 of 2 |
| `tests/real/*.ll` but llama.cpp's fixture | 10 | 220 | 91 | 4 | 4 | 0 | 4 | None tried |
| `llvm/test/Transforms/InstSimplify/*.ll` at the pin | 190 | 7,215 | 7,945 | 258 | 225 | 0 | 225 | 221 of 223 |

On `tests/rules/search.ll`, which [`tests/rules/expect.json`](../tests/rules/expect.json) pins:

| Function | Around | Chain | Instructions | Certified as |
| --- | --- | --- | --- | --- |
| `@masked` | `%o` | `or_zero`, `and_allOnes`, `add_sub_cancel` | 4 to 0 | Slice and whole function |
| `@sum`, a loop that reads memory | `%u` | `xor_xor_cancel`, `umin_umax_left` | 4 to 0 | Slice |
| `@mask` | `%s` | `sub_mask_xor_nuw`, whose side condition 7 meets | 2 to 0 | Slice and whole function |
| `@notmask` | | Nothing: 6 fails the side condition | | |
| `@widths` | `%t` | `trunc_zext` | 2 to 0 | Slice and whole function |
| `@twice` | `%a` | `or_zero`, at an instruction read twice | 1 to 0 | Slice and whole function |
| `@plain` | | Nothing | | |

`@sum`'s chain is the one `--baseline none` keeps: `llc` alone gives its cut 11 uOps, and 4 after the rewrite. Against
`opt -O3` both are 4.

### On LLVM's InstSimplify tests

With every candidate kept, the search found 225 rewrites in the 190 files: 158 of one rule, 57 of two and 10 of three,
using 115 rules. Lean certified all 225 as slices. 223 of them are in a function of one block, and 221 of those are
certified as whole functions too. The two that aren't are in functions of several blocks. The other two have an argument
with a `range` attribute, which `build/ir-lean` turns into a check before the block, a shape the certifier doesn't
follow: `unsupported`, with their slices certified. The run took 1,367 s, one certificate at a time.

The first full run, earlier the same day, found a bug, and not in a rule. Two rewrites in `icmp-constant.ll`, in
`@mul_nsw_by_zero` and `@mul_nuw_by_zero`, came back `error`, `ir_invalid`, so 223 of the 225 were certified. LLVM
writes those two functions with a block before the one that runs before it, and a slice was written in the function's
order, so an instruction came before one it reads. `opt -passes=verify` refused the slice before any proof was tried. A
slice's lines now come after what they read, `tests/rules_test.py` has the case, and the run above is the one after the
fix.

Alive2, asked about each of the 225 certified slices with `undef` inputs off, through
[`tests/rules_alive.py`](../tests/rules_alive.py), finds 225 correct. It finds none incorrect. It's a second opinion:
nothing is accepted on it.

The search reads these files as IR, not as tests: it doesn't run their `RUN` lines or compare with `opt`'s output.
They're where the rules' patterns occur, since the rules were cut from the proofs of what these files test.

## What it costs

| Step | Each | Measured over |
| --- | --- | --- |
| Checking the rules are proved, once a run | 5.7 s, 2.9 GB | `rules.py check`, 182 rules |
| Searching one instruction's cut | Median 0.4 ms, at most 30 ms | 7,945 instructions of LLVM's InstSimplify tests, 5.9 s in all |
| `llvm-mca` on one candidate, both sides | Median 29 ms | 225 candidates, 6.6 s in all |
| Certifying one chain as a slice | Median 3.0 s, at most 8.1 s | 225 chains, 681 s in all |
| Certifying one chain as a whole function | Median 3.0 s, at most 4.6 s | 223 chains, 662 s in all |

The first three rows are from runs that certify nothing, and the last two from the run on LLVM's InstSimplify tests
that keeps every candidate. That run was before each certificate's replay reached every module it imports, 29 of
them, one `leanchecker` process each, which took the chain in `tests/rules/chain.ll` from 2.9 s to 4.5 s. It
hasn't been run again.

Certifying is ir-lean, two Lean compiles, the checker, the axiom audit and `leanchecker` on each module the
certificate imports, each a process of its own that imports the libraries again. It's done one chain at a time. Putting many chains in one module would share that
cost, and isn't done.

## What it can't do

- **Find a win over `clang -O3`.** With only LLVM's own rewrites as rules, it finds what `opt -O3` finds. Rules from
  elsewhere, an agent's or Minotaur's, each proved once and stored, are what
  [decision 4](roadmap.md#thirteen-decisions-of-2026-11-09-after-103) expects to feed it, and none exists yet.
- **Divisions.** `udiv`, `sdiv`, `urem` and `srem` can be undefined, so they aren't values, and a cut stops at one.
  38 of the 182 rules have a division in their pattern: each is proved, and none is applied. Following a division
  takes a congruence lemma for runs that can be undefined, which isn't written.
- **Vectors, floating point, memory, calls, `freeze` and `phi`.** Each is a leaf. So nothing here rewrites SIMD code,
  which is where [decision 7](roadmap.md#thirteen-decisions-of-2026-11-09-after-103)'s corpus is. Vector rules need
  lane-wise statements and congruence, and the x86 intrinsics another lane is adding.
- **Whole functions of more than one block, or with memory.** Slices only, until F4's cut lemma and memory in
  `Refines`.
- **Operands the other way round.** A pattern isn't commutative, and the search has commutativity as a rule only
  for `and`, `xor` and the four min and max intrinsics, which have no flags to keep. `x + (y - x)` isn't matched by
  `add_sub_cancel`, which is `(y - x) + x`.
- **Analyses.** No rule asks known bits, a range or dominance, so no rewrite that needs one is found.
- **Rank by where code runs.** It looks at every instruction once, in order. With no profile there's nothing to rank
  by.
- **Rewrites across cuts.** A chain rewrites one cut. It reports the longest chains and doesn't apply two to one
  function, so `after.ll` has one rewrite in it.
- **More than its bounds.** Past `--depth`, `--steps` or `--states` it doesn't look. A step's proof follows the state
  as a tree, so a cut where one instruction is read many times over gets a long proof, and past 4,000 nodes none.
- **Everything in a function's text.** It reads IR as text. Constant expressions, `undef`, vector operands and metadata
  on an instruction make that instruction a leaf, which loses rewrites and can't make a wrong one pass: a certificate
  is about what `build/ir-lean` reads from the IR the search wrote.

## Reproducing

In `nix develop`, after `lake build` and building `build/ir-lean`. On a shared machine, run each under
`tools/measure.py run --heavy`:

```console
tools/rules/rules.py check
tools/rules/rules.py search tests/rules/search.ll --keep all --out build/rule-search/fixture
tools/rules/rules.py search tests/rules/search.ll --baseline none --out build/rule-search/fixture-none
tools/rules/rules.py survey tools/corpus/seeds/*.ll --keep all --out build/rule-search/seeds
tools/rules/rules.py survey tests/real/{choices,gep,heap,lanes,memory_errors,promises,stops,ub,vectors,x86}.ll \
  --keep all --out build/rule-search/real
tools/rules/rules.py survey $LLVM_PROJECT_SRC/llvm/test/Transforms/InstSimplify/*.ll \
  --out build/rule-search/instsimplify-fewer
tools/rules/rules.py survey $LLVM_PROJECT_SRC/llvm/test/Transforms/InstSimplify/*.ll --keep all \
  --out build/rule-search/instsimplify-all
tests/rules_alive.py build/rule-search/instsimplify-all   # Alive2's opinion of each certified slice
tests/rules_test.py --tier static
tests/rules_test.py --tier live
```

`survey` runs the search on each input with one check of the rules, writes `survey.json` with the totals, the rules
used and the times, and fails if a kept rewrite isn't certified.
