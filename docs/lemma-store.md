# Lemma store

Checked, reusable lemmas that later proofs, the superoptimizer and proof tests can find and use. This is lemma store
v1, milestone E1 of [Phase 6](roadmap.md#phase-6-the-engine-and-the-lemma-store): the store is built by `lake build`,
checked again in CI by the `store` test, and holds [#48](https://github.com/phongndo/ir-lean/pull/48)'s rewrites at
every width, the laws of `IRLean.Refines` and LangRef's integer contracts. For what any theorem means, read
[trust](trust.md) first: a stored lemma is a theorem about IRLean's model, like any other.

Measured on 2026-11-08 on top of `c0c4e0b`, on x86-64 Linux with 32 cores and 30 GB, with Lean 4.35.0, in the dev
shell, while other work ran on the same machine.

## What it found

- **163 lemmas meet the first three rules of the bar,** checked: 16 of them meet all four, and 147 are candidates,
  which no second proof uses yet. 53 hypotheses each have a counterexample showing they're needed. None of #48's 38
  rewrites is used by two proofs yet: the 16 are 9 of refinement's laws, 5 of the contracts and 2 facts about
  `BitVec w`.
- **Seeding refused 6 of 169.** Two of #48's lemmas, `shl_lshr_eq_iff` and `shl_sshr_eq_iff`, hold without their
  bound on the shift, so their hypothesis is one nothing needs. `grind` alone closes two more and `Refines.of_eq`, and
  `add_of_and_eq_zero`'s conclusion isn't in the normalizer's form. [Below](#what-seeding-refused).
- **Lookup finds a lemma restated.** Renamed and reordered variables, reordered hypotheses, `>` for `<`, `¬ =` for
  `≠`, swapped operands of `∨` and `∧`, and an equation the other way round all give a stored lemma's key. A goal at
  a real width, such as `mul nuw nsw i32 %x, 8` to `shl nuw nsw i32 %x, 3`, finds the lemma for every width it's an
  instance of, with its side conditions closed by `decide`.
- **The checker refuses each kind of bad lemma,** in `tests/store/must_refuse`: a `sorry`, an axiom of its own, an
  axiom from `bv_decide`, a fixed width, a hypothesis with no counterexample, a counterexample proved by `sorry`, a
  duplicate after normalization and a false statement.
- **A proof from the store is shorter, width-independent and faster where the solver struggles.** InstSimplify's
  `lshr (shl nuw x, s), s` to `x`, on what ir-lean emits, checks in 15.8 s at `i256` with `bv_decide`, which needs
  more than its default 10 s of solving, and in 0.2 s from the store, whose proof rests on the standard three axioms
  only. [Below](#a-proof-before-and-after).
- **The prototype's lemmas don't meet the bar.** All 13 of its population-count lemmas are stated at one width, and
  10 rest on `bv_decide`'s axioms. [Below](#the-prototype).

## What's in it

[`store/index.json`](../store/index.json) names every stored lemma, the module that proves it, the family it's in,
where it came from, its key, its status, the counterexamples for its hypotheses, and the proofs that use it. Seeds
stay where they're proved: the store names them, and `lake build` builds them as part of it.

| Family | From | Lemmas | Admitted | Candidates |
| --- | --- | --- | --- | --- |
| `generic-rewrites` | #48, [`IRLean/Generic`](../IRLean/Generic), the rewrites at every width | 38 | 0 | 38 |
| `bitvec` | #48, [`IRLean/Generic/BitVec.lean`](../IRLean/Generic/BitVec.lean), facts about `BitVec w` | 4 | 2 | 2 |
| `refinement` | [#46](https://github.com/phongndo/ir-lean/pull/46), [`IRLean/Refine.lean`](../IRLean/Refine.lean) | 20 | 9 | 11 |
| `contracts` | [#42](https://github.com/phongndo/ir-lean/pull/42), [`IRLean/Contract/Poison.lean`](../IRLean/Contract/Poison.lean) | 101 | 5 | 96 |
| All | | 163 | 16 | 147 |

| Path | What it is |
| --- | --- |
| [`store/index.json`](../store/index.json) | The catalog, and its version |
| [`store/LemmaStore.lean`](../store/LemmaStore.lean) | Imports every stored lemma, and `LemmaStore.catalog` names them. `store.py` writes it from the index |
| [`store/LemmaStore/Counter`](../store/LemmaStore/Counter) | A counterexample for each hypothesis, and a witness that they can all hold |
| [`store/LemmaStore/Normal.lean`](../store/LemmaStore/Normal.lean) | The normalizer, and the key |
| [`store/LemmaStore/Select.lean`](../store/LemmaStore/Select.lean) | Retrieval, and the selector registered with Lean's premise selection |
| [`tools/store/store.py`](../tools/store/store.py) | `check`, `lookup`, `add`, `forget`, `report` and `capabilities`, with JSON answers |
| [`tools/store/StoreTool.lean`](../tools/store/StoreTool.lean) | What `store.py` asks Lean: the facts about each lemma, and lookups |

## The bar

The [roadmap](roadmap.md#the-flywheel)'s four rules, and how each is checked:

| Rule | Checked by | Refused as | Test that a lemma breaking it is refused |
| --- | --- | --- | --- |
| 1. Checked by the kernel, with only the standard axioms | `tests/check_axioms.lean` on each module that holds a stored lemma or a counterexample, reading it as data, with none of `bv_decide`'s axioms allowed, `leanchecker` replaying the module, and each lemma's own axioms read again | `sorry`, `nonstandard_axiom`, `compiled_code`, `replay_failed`, `does_not_check` | `Sorried.lean`, `ExtraAxiom.lean`, `BvDecide.lean`, `FalseStatement.lean` |
| 2. Stated for every width where that makes sense | No `BitVec n` or `Val n` with `n` written as a number other than 1, which LLVM fixes for conditions, flags and comparisons, unless the index records why | `fixed_width` | `FixedWidth.lean` |
| 3. Each hypothesis shown necessary by a counterexample | For each hypothesis `h`, a theorem `LemmaStore.Counter.<lemma>.drop_<h>` stating exactly that the lemma without `h` is false, and `LemmaStore.Counter.<lemma>.sat` that the hypotheses can all hold, each resting on the standard axioms only | `hypothesis_unwitnessed`, `hypotheses_unsatisfiable` | `NoCounterexample.lean`, `SorriedCounterexample.lean` |
| 4. Reused by at least 2 proofs | The theorems whose proofs use it, directly or through declarations private to their module, in the store's modules and the consumer modules the index names | Not refused: a candidate until a second proof uses it | |

`check` builds the statement each counterexample has to have from the lemma itself, so one stating something else is
refused as a `mismatch`, and `store.py add` prints the statement it wants. A hypothesis that's an instance argument,
such as `[Refine.Reflexive α]`, counts as one, named by its position.

The other admission checks, from [prior art](prior-art.md#the-lemma-store)'s eight:

| Check | Refused as |
| --- | --- |
| What a use site matches against a goal is in the normalizer's form: an equation's or equivalence's left side, or the whole conclusion, as Mathlib's `simpNF` asks of a simp lemma's left side | `not_normal` |
| No stored lemma has the same key, either way round | `duplicate` |
| No stored lemma proves it by being applied, with every side condition one of its hypotheses or closed by `decide` | `subsumed` |
| `simp`, `bv_normalize`, `grind` and `decide` each fail to close it alone, within 20,000 heartbeats | `trivial` |
| The kernel checks it again, under a fresh name, in under 1 s | `slow` |
| No bit-vector constant other than 0 or 1 written as a number, which a general lemma lifts into a variable with a side condition, as `mul_twoPow` has `c = BitVec.twoPow w k` | `unlifted_constant` |
| Its entry says where it came from | `no_provenance` |
| Its key is the one the index records | `statement_changed` |

`tools/store/store.py capabilities` lists every reason with the rule it enforces.

## Keys

A lemma's key is a SHA-256 hash, cut to 20 hex digits, of its elaborated statement in a canonical form, never of its
text: `≠`, `>` and `≥` unfolded to `¬ =`, `<` and `≤`; the operands of every associative and commutative operator in
one order, by core's `ac_nf` machinery; variables ordered by where they first occur, the conclusion first, with
hypotheses after them, sorted; and binder names, binder annotations and metadata dropped. It's printed with every
constant's full name and universe levels and every argument, implicit ones and instances included. Variables are
ordered and `ac_nf` run again until neither changes, since ordering variables changes how `ac_nf` orders operands.

The key includes the normalizer's version, so a change to the normalizer changes every key, and `check` reports each
as `statement_changed` until the index is written again.

Two statements with the same key are the same up to the reorderings above. Two with different keys may still be
equivalent: the normalizer doesn't know which of `Val`'s operations commute, since none is registered as commutative, or
that on `Nat`, `a < b` is `¬ b ≤ a`.

## Finding a lemma

```console
tools/store/store.py lookup --pretty \
  --statement '∀ (x : Val 32), Val.mul x (some 8#32) true true = Val.shl x (some 3#32) true true'
```

finds `mul_twoPow`, stated for every width with its constant lifted, and closes what's left with `decide`. Shortened:

```json
{
  "schema": "ir-lean.store.lookup/1",
  "status": "instance",
  "exact": [],
  "instances": [
    {
      "name": "IRLean.Generic.mul_twoPow",
      "status": "candidate",
      "reversed": false,
      "side_conditions": [
        { "statement": "8#32 = BitVec.twoPow 32 3", "closed_by": "decide" },
        { "statement": "3 < 32", "closed_by": "decide" },
        { "statement": "true = false ∨ 3 + 1 < 32", "closed_by": "decide" }
      ],
      "free_variables": 0,
      "closes": true
    }
  ]
}
```

The statement is a closed proposition, elaborated with `open IRLean` and the store imported. `--import` adds modules
it needs. The answer, schema `ir-lean.store.lookup/1`, has a `status`:

| Status | Exit | Means |
| --- | --- | --- |
| `exact` | 0 | A stored lemma has the statement's key, either way round |
| `instance` | 0 | A stored lemma's conclusion, instantiated, is the statement's conclusion, with its hypotheses left as `side_conditions`. `closes` says whether `decide` closes every one and no variable is left free |
| `none` | 3 | Nothing in the store states it |
| `error` | 1 | No verdict: `reason` says why, such as `statement_invalid` |

The second tier is a `DiscrTree` over the stored lemmas' conclusions, as `simp`, `exact?` and `rw?` index lemmas, then
unification at reducible transparency. The third is Lean's own: importing `LemmaStore.Select` registers its selector
with `@[library_suggestions]`, which puts the store's matches first and Lean's default selector's after them, so
`grind +suggestions`, `simp? +suggestions` and `try?` see the store.
[`tests/store/Suggest.lean`](../tests/store/Suggest.lean) proves `add i32 %x, 0` to `%x` and
`lshr i256 (shl nuw %x, %s), %s` to `%x` with `grind +suggestions` and no other hint, where plain `grind` proves
neither.

A match only says what to try. A proof that uses it is checked by the kernel like any other, and the lemma with it.

## A proof before and after

`lshr (shl nuw x, s), s` to `x` is a fold InstSimplify makes, at
`llvm/lib/Analysis/InstructionSimplify.cpp`, line 1448, at `llvmorg-23.1.3`. [`tests/store/reuse`](../tests/store/reuse)
has it at `i64` and `i256`, as IR that ir-lean translates, and two proofs of each that the target refines the source:

- **Before,** without the store, as a proof of a rewrite is written today: run both sides, split on each `if` in the
  semantics of `shl nuw` and `lshr`, and hand each case to `bv_decide` at that width.
- **After,** from the store: run both sides, then `IRLean.Generic.lshr_shl_nuw_refines`, a stored lemma for every
  width, and `IRLean.Refine.outcome_ok_ok`.

```lean
theorem round_trip_256 : Refines Src256.f Tgt256.f := by
  intro x s
  simp only [Src256.f, Tgt256.f]
  rw [run_ret Src256.f.step (b := .bb1 x s) (r := Val.lshr (Val.shl x s true false) s) rfl,
    run_ret Tgt256.f.step (b := .bb1 x) (r := x) rfl]
  exact (Refine.outcome_ok_ok _ _).2 (Generic.lshr_shl_nuw_refines x s false false)
```

| | `i64` | `i256` |
| --- | --- | --- |
| Before: Lean, from start to end | 0.9 s | 15.8 s, with `bv_decide` given 300 s. Given its default 10 s, it ran out once of two runs |
| After | 0.2 s | 0.2 s |
| In CI's `store` test, before and after | 1.5 s and 0.4 s | 22.3 s and 0.4 s |
| Before rests on | the standard three, and one of `bv_decide`'s axioms | the same |
| After rests on | the standard three | the standard three |

Each is one Lean process compiling the proof, with the generated modules already compiled, on 2026-11-08, on this
machine while other lanes' jobs kept the load average near 5, and in CI on a 4-core runner. The proof after is the same text at every width, but for the modules
it names; the one before is a new SAT problem at each, which grows with the width. `tests/store_test.py` checks all
four, their axioms, and that `leanchecker` replays them.

Don't overread this. One rewrite, on one machine. Rewrites `bv_decide` normalizes away gain little:
`mul nuw nsw x, 8` to `shl nuw nsw x, 3` checked in about the same time at `i256` with `bv_decide` as from
`mul_twoPow`. The roadmap's E3 measures whether proofs get cheaper over the next 20 proofs, not one.

## Adding and forgetting lemmas

```console
tools/store/store.py add Lemmas.lean --family NAME --provenance 'where it came from' --dry-run
tools/store/store.py add --existing IRLean.Foo.bar --family NAME --provenance '#NN, IRLean/Foo.lean'
tools/store/store.py forget NAME --reason 'why'
```

`add` judges each theorem a file declares, apart from its counterexamples, against the store, with every check above,
the axiom check and replay of its module included, as `--existing` does for a lemma already proved elsewhere.
A file's counterexamples go in it, under `LemmaStore.Counter.<lemma>`. If every theorem is admitted or a candidate, and
it isn't a dry run, the file becomes `store/LemmaStore/Lemmas/<name>.lean`, the index gets an entry for each, and
`store/LemmaStore.lean` is written again. A file mustn't import `LemmaStore` itself, which would import it back.

The answer, schema `ir-lean.store.admission/1`, is `accepted` or `refused`, with each lemma's status and reasons. A
Lean error that's a resource limit is an `error`, never a refusal: it says nothing about the lemma.

`forget` takes a lemma out of the catalog and records it, its key, its status, the reason and the date under
`forgotten`. A module the store owns goes too, once nothing stored is left in it. A lemma proved elsewhere, such as
in `IRLean`, stays there.

When to forget is the maintainer's call for now. `report` lists each candidate with how many proofs use it, so a
candidate nothing uses after a wave of proofs, as DreamProver forgets the least-used, is the one to look at first.

## Versioning

The index records the version it was last checked at: Lean's toolchain, the normalizer's version, and a SHA-256 hash
of the toolchain and the source of every module the store imports from this repo, as Mathlib's cache hashes a file
with its imports and toolchain. A lemma's identity is its key. Whether it still checks is what `check` finds, every
time, in CI.

When a change to `IRLean` breaks a stored lemma, `lake build` fails in that lemma's module, and `check` doesn't pass,
so the lemma is reported, not dropped. When it changes a statement, `check` reports `statement_changed`. When it
changes only how many proofs use a lemma, so its status changes, `check` reports the drift. `check --write` records
the new key or status, so the change shows in `store/index.json`'s diff.

The store keeps no LRAT files, because it admits nothing proved by `bv_decide`: rule 1 rules its axioms out. A lemma
only `bv_decide` proves waits outside the store until it's proved without it.

## What seeding refused

The checker ran on every public theorem in the five seed modules, 169 of them, and refused 6:

| Lemma | Refused as | Why |
| --- | --- | --- |
| `IRLean.Generic.shl_lshr_eq_iff` | `hypothesis_unwitnessed` | Holds without `k ≤ w`: past the width, both sides say `x = 0`. No counterexample exists |
| `IRLean.Generic.shl_sshr_eq_iff` | `hypothesis_unwitnessed` | The same, for `k < w` |
| `IRLean.Generic.add_of_and_eq_zero` | `not_normal` | `ac_nf` puts its conclusion's conjuncts in another order |
| `IRLean.Generic.shl_lshr_eq_and` | `trivial` | `grind` closes it alone |
| `IRLean.Generic.shl_lshr_shl` | `trivial` | `grind` closes it alone |
| `IRLean.Refines.of_eq` | `trivial` | `simp` and `grind` close it alone |

They stay in `IRLean`, where other proofs use them. The first two could be stated without their hypothesis, which
would make them more general.

## The prototype

[`prototypes/lemma-reuse`](../prototypes/lemma-reuse) kept its lemmas in a directory of modules with an `index.json`,
outside the build and CI, matched them word for word, and had a vocabulary of two facts. Run through this store's
checks on 2026-11-08, its 13 population-count lemmas are all refused: all 13 are stated at one width, 10 rest on
`bv_decide`'s axioms, 7 have hypotheses such as `x ≤ 255#8` with no counterexample, most because none exists, and 10
have constants written as numbers. Its seed lemmas in `Count.lean`, and the every-width counting lemmas in
`tests/llvm/Bits.lean` they build on, mostly pass: 6 of 18 would be admitted and 5 candidates, and the rest need
counterexamples. They aren't in the store, because neither file is in a library `lake build` builds.

Its q4_K half runs against the q4_K proof, which
[#57](https://github.com/phongndo/ir-lean/pull/57) brought to `main` on 2026-11-08. Its two core lemmas each rest on
one of `bv_decide`'s axioms and are stated at 256 and 512 bits, as [lemma reuse](lemma-reuse.md#proof-time) records,
so rules 1 and 2 would refuse them. Checking them here, and retiring the prototype, is the next pull request.

## What it rests on

- **The kernel and the standard three axioms,** for each stored lemma. `tests/check_axioms.lean` reads each module
  holding one, and everything it imports, as data, so nothing in it runs, and allows none of `bv_decide`'s axioms
  here. `leanchecker` replays each module through the kernel. `StoreTool` reads each lemma's axioms again.
- **Nothing in the store is trusted.** A proof that uses a stored lemma is checked by Lean, with the lemma, like any
  proof. The index, the keys, the counts of uses and the selector only say what to try and what's worth keeping.
- **The counterexamples** are kernel-checked theorems too, so a hypothesis shown needed is needed in IRLean's model.
  As with [#48's](generic-rewrites.md), that says nothing about whether LLVM needs it.
- **`StoreTool` runs the store's code,** as any file importing it does: the checks for normal form, triviality,
  subsumption and uses aren't what makes a lemma trusted, and a bug in them could only keep a lemma out or let one
  in that's true but not worth keeping.

## Cost

| | Time |
| --- | --- |
| `lake build` of the store and its tool, on top of `IRLean`, from nothing | 4.2 s, compiling its 12 modules one at a time on this machine |
| `store.py check`, with the store built | 22.7 s in CI, on a 4-core runner: 3 consumer modules compiled, 9 modules' axioms checked and replayed, and Lean's facts about all 163 lemmas |
| Checking one lemma again in the kernel | 0.28 ms at the median, 3.9 ms at most |
| `store.py lookup` | 0.5 s for its Lean process on this machine |
| The `store` test | 94.5 s in CI, in the `semantics` job |

## Gaps

- **Reuse is counted only where `check` looks:** the store's own modules, `IRLean`'s, and the consumer modules the
  index names, [`RefineCases.lean`](../tests/refine/RefineCases.lean),
  [`ContractPoison.lean`](../tests/contracts/ContractPoison.lean) and
  [`RewriteCounter.lean`](../tests/generic_rewrites/RewriteCounter.lean). Proofs in `tests/proofs`, `tests/llvm` and
  `tests/binding` need generated modules, so they aren't scanned, and an `example` leaves nothing to count. Proofs in
  the same file count: `urem_isUB_iff`'s two users are both in `IRLean/Contract/Poison.lean`. The reuse example's
  proofs aren't consumers, since they were written to show reuse.
- **Most candidates are LangRef's contracts,** which no proof uses yet. They wait as rule 4 says.
- **Normalization knows `ac_nf`'s operators only.** `Val`'s operations aren't registered as commutative, so
  `Val.and a b` and `Val.and b a` have different keys, and lookup won't find one stated as the other.
- **The width rule reads numbers, not intent.** A lemma at width 1 passes, as LLVM fixes `i1` for conditions and flags.
  So does one stated for a width variable `w` with a hypothesis such as `w = 8`, given a counterexample and a witness.
- **Triviality is judged with a budget.** A lemma `grind` would close with more heartbeats is admitted.
- **Subsumption only tries applying one lemma.** A lemma derivable in two steps is admitted.
- **The prototype isn't retired yet.** That, with its q4_K lemmas recorded against the bar, is the next pull request.
  `Count.lean`'s and `tests/llvm/Bits.lean`'s counting lemmas aren't in the store, since no library `lake build`
  builds them.
- **No lemma store for memory yet.** Every stored lemma is about values and runs without `Mem`, since `Refines` has no
  instance for it until SEM-06.

## Reproducing

In `nix develop`, after `lake build` and building `build/ir-lean`:

```console
tools/store/store.py check
tools/store/store.py report --pretty
tests/store_test.py build/ir-lean
```

`check --write` writes what it computed into the index: each lemma's key, status, counterexamples and users, and the
version. Run it after changing a stored lemma, its counterexamples, or a consumer module.
