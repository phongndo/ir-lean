# Rewrites at every width

Integer rewrites LLVM's InstSimplify and InstCombine make, proved in Lean for a variable width `w`, every operand,
poison included, and every combination of the flags each instruction carries. This is the start of AUTO-03 in the
[task list](llvm-verification-tasks.md#auto-03-from-instances-to-every-width). For what any theorem means, read
[trust](trust.md) and [refinement](refinement.md) first.

**These are theorems about the rewrites' patterns in IRLean's model, not about LLVM's code.** None says InstCombine or
InstSimplify is correct, or that their C++ applies only the pattern stated here.

## Equality or refinement

Each rewrite is one of two kinds, and the theorem's name says which:

- An equality, `src = tgt`: the two are the same function of their operands in the model. It holds in both directions.
- A refinement, `Refines src tgt` from [`IRLean.Refine`](refinement.md), named `..._refines`: where `src` is a value,
  `tgt` is the same value, and where `src` is poison or undefined, `tgt` may be anything. These are the rewrites that
  aren't equalities, because `src` is poison or undefined somewhere `tgt` isn't, so they only hold in one direction.

A hypothesis on `w`, on a constant or on a flag is there because the rewrite is wrong without it in the model.
[`RewriteCounter.lean`](../tests/generic_rewrites/RewriteCounter.lean) has one input that shows it for each, and one
that shows each refinement isn't an equality.

## The rewrites

In [`IRLean/Generic`](../IRLean/Generic), namespace `IRLean.Generic`. The theorems are in `Arith.lean` and
`Bitwise.lean`. The facts about `BitVec w` they need, which `bv_decide` can't check for a variable `w`, are in
`BitVec.lean`. When a shift left by `k` can be undone, logically or arithmetically, is `shl_lshr_eq_iff` and
`shl_sshr_eq_iff`. `mul` by `2 ^ k` overflowing exactly when `shl` by `k` does is `umulOverflow_twoPow` and
`smulOverflow_twoPow`. Disjoint values adding without overflow is `add_of_and_eq_zero`.

Where LLVM does each is given at `llvmorg-23.1.3`, the dev shell's `LLVM_PROJECT_SRC`, as the place that fold is
written. `InstructionSimplify.cpp` is in `llvm/lib/Analysis`, the others in `llvm/lib/Transforms/InstCombine`.
`not x` is `xor x, -1`, as LLVM writes it.

### Arithmetic

| Rewrite | Theorem | Kind | Needs | In LLVM |
| --- | --- | --- | --- | --- |
| `add x, 0` to `x` | `add_zero` | Equality, any flags | | `InstructionSimplify.cpp:607` |
| `sub x, 0` to `x` | `sub_zero` | Equality, any flags | | `InstructionSimplify.cpp:761` |
| `mul x, 1` to `x` | `mul_one` | Equality, any flags | No `nsw`, or `w ≠ 1`. In `i1`, `1` is `-1`, and `mul nsw i1 1, 1` is poison | `InstructionSimplify.cpp:913` |
| | `mul_one_refines` | Refinement, any flags | | |
| `sub x, x` to `0` | `sub_self_refines` | Refinement, any flags | | `InstructionSimplify.cpp:765` |
| `mul x, 0` to `0` | `mul_zero_refines` | Refinement, any flags | | `InstructionSimplify.cpp:909` |
| `add x, x` to `shl x, 1` | `add_self` | Equality, keeping `nuw` and `nsw` | `1 < w`. In `i1`, `shl x, 1` is poison; InstCombine turns `add i1` into `xor` first, at line 1639 | `InstCombineAddSub.cpp:1642` |
| `mul x, 2 ^ k` to `shl x, k` | `mul_twoPow` | Equality, keeping `nuw` and `nsw` | `k < w`, and no `nsw` or `k + 1 < w` | `InstCombineMulDivRem.cpp:249` |
| | `mul_twoPow_refines` | Refinement, with the flags InstCombine sets: `nuw` if `mul` had it, `nsw` if `mul` had it and `k + 1 < w` | `k < w`. At `k + 1 = w`, `2 ^ k` is the signed minimum, and keeping `nsw` is wrong | Lines 249 to 262 |
| `or disjoint x, y` to `add nuw nsw x, y` | `or_disjoint_refines_add` | Refinement. The other direction is wrong: `add nuw nsw 1, 1` is `2` | | `InstCombineAddSub.cpp:2426` calls them equivalent, and `m_AddLike` matches both |
| `udiv x, 1` to `x` | `udiv_one` | Equality, any `exact` | `0 < w`, since `1` is `0` at width zero | `InstructionSimplify.cpp:1094` |
| `sdiv x, 1` to `x` | `sdiv_one` | Equality, any `exact` | `1 < w`. In `i1`, `1` is `-1`, and dividing `-1` or poison by it is undefined | `InstructionSimplify.cpp:1094` |
| | `sdiv_one_refines` | Refinement, any `exact`, at every width: where the equality fails, the source is undefined | | |
| `urem x, 1`, `srem x, 1` to `0` | `urem_one_refines`, `srem_one_refines` | Refinement, at every width | | `InstructionSimplify.cpp:1095` |

### Bitwise

| Rewrite | Theorem | Kind | Needs | In LLVM |
| --- | --- | --- | --- | --- |
| `and x, x` to `x` | `and_self` | Equality | | `InstructionSimplify.cpp:2084` |
| `or x, x` to `x` | `or_self` | Equality | No `disjoint` | `InstructionSimplify.cpp:2361` |
| | `or_self_disjoint_refines` | Refinement, any `disjoint`. With it, `or disjoint x, x` is poison unless `x` is `0` | | |
| `xor x, x` to `0` | `xor_self_refines` | Refinement | | `InstructionSimplify.cpp:2547` |
| `and x, -1` to `x` | `and_allOnes` | Equality | | `InstructionSimplify.cpp:2092` |
| `or x, 0` to `x` | `or_zero` | Equality, any `disjoint` | | `InstructionSimplify.cpp:2362` |
| `xor x, 0` to `x` | `xor_zero` | Equality | | `InstructionSimplify.cpp:2543` |
| `and x, 0` to `0` | `and_zero_refines` | Refinement | | `InstructionSimplify.cpp:2088` |
| `or x, -1` to `-1` | `or_allOnes_refines` | Refinement, any `disjoint` | | `InstructionSimplify.cpp:2356` |
| `not (and x, y)` to `or (not x), (not y)` | `not_and` | Equality | No `disjoint` on the `or`: `or disjoint -1, -1` is poison | `InstCombineAndOrXor.cpp:1712`, which rewrites the other way |
| `not (or x, y)` to `and (not x), (not y)` | `not_or` | Equality | No `disjoint` | The same |
| | `not_or_refines` | Refinement, any `disjoint` | | |
| `xor (xor x, y), y` to `x` | `xor_xor_cancel_refines` | Refinement: poison `y` makes the source poison | | `InstructionSimplify.cpp:263` reassociates, then `xor y, y` and `xor x, 0` |
| `and x, (or x, y)` to `x` | `and_or_absorb_refines` | Refinement, any `disjoint`: poison `y` makes the source poison | | `InstructionSimplify.cpp:2026` |

### Shifts

The shift amount `s` is any value, poison included, and the same one at both shifts.

| Rewrite | Theorem | Kind | Needs | In LLVM |
| --- | --- | --- | --- | --- |
| `shl x, 0`, `lshr x, 0`, `ashr x, 0` to `x` | `shl_zero`, `lshr_zero`, `ashr_zero` | Equality, any flags | `0 < w`: at width zero no amount is in range | `InstructionSimplify.cpp:1316` |
| `lshr (shl x, s), s` to `and x, (lshr -1, s)` | `lshr_shl` | Equality, any `exact` on `lshr` | No flags on `shl` | `InstCombineShifts.cpp:1530`, for a constant amount |
| `shl (lshr x, s), s` to `and x, (shl -1, s)` | `shl_lshr` | Equality | No flags on either | `InstCombineShifts.cpp:599` |
| `lshr (shl nuw x, s), s` to `x` | `lshr_shl_nuw_refines` | Refinement, any other flags | `nuw`: shifting `255` left by one loses a bit | `InstructionSimplify.cpp:1448` |
| `ashr (shl nsw x, s), s` to `x` | `ashr_shl_nsw_refines` | Refinement, any other flags | `nsw` | `InstructionSimplify.cpp:1492` |
| `shl (lshr exact x, s), s` to `x` | `shl_lshr_exact_refines` | Refinement, any flags on `shl` | `exact` | `InstructionSimplify.cpp:1413` |
| `shl (ashr exact x, s), s` to `x` | `shl_ashr_exact_refines` | Refinement, any flags on `shl` | `exact` | `InstructionSimplify.cpp:1413` |

## What these say about LLVM

Each theorem is about the operations in [`IRLean/Int.lean`](../IRLean/Int.lean), the definitions emitted code uses,
so it says the same of LLVM only as far as those match LangRef. The [contracts](llvm-semantic-contracts.md) and
`tests/opcheck.py` are the evidence for that, and their gaps are these theorems' gaps. Beyond those:

| Gap | What it means |
| --- | --- |
| Not the pass | A theorem checks a pattern, with the flags the C++ at the cited line sets, as read by a person. It doesn't check that the C++ matches only that pattern, computes `k` or a mask right, or is reached where it should be. Binding one run of a pass to a theorem is [binding](llvm-proof-binding.md)'s job, per instance |
| No `undef` | An operand is a value or poison. A rewrite reading an operand twice, such as `sub x, x`, `add x, x`, the cancellations, the absorption and the shift round trips, which read `s` twice, says nothing about an `undef` operand, which LLVM lets each read see differently. [Refinement](refinement.md#what-it-says-about-llvm) has the rule for arguments |
| Scalars only | LLVM makes the same rewrites on vectors, lane by lane, with constants that may have poison lanes. No theorem here is about a vector |
| Width zero | LLVM has no `i0`. The model has `Val 0`, so a theorem needs `0 < w` where the model does, and says so |
| Constants are values | A theorem takes a constant as a `BitVec w`, such as `BitVec.twoPow w k` for `mul`. A use at a real width shows its constant is that one, by `decide` on the constant alone |
| Not a list | These are 33 rewrites, in 38 theorems, chosen by hand, not the list [INV-04](llvm-verification-tasks.md#inv-04-rewrite-level-inventory) is to generate. AUTO-03 is done when that list is proved, and it isn't yet |

Every theorem here is proved for all widths at once. None checks finitely many widths or inputs. The counterexamples
are concrete inputs, and only show a hypothesis is needed in the model, not that LLVM gets anything wrong.

## Tests

`tests/generic_rewrites.sh`, the `generic_rewrites` test in [testing](testing.md), checks this in about 20 s, one
Lean process at a time, each capped at 2 GB and 300 s, from copies in a temporary directory:

- `IRLean/Generic` builds with warnings as errors, against `IRLean/Int.lean` and `IRLean/Refine.lean`.
- [`RewriteUse.lean`](../tests/generic_rewrites/RewriteUse.lean) uses the theorems at `i8` to `i64`: the `add i8 %x, 0`
  rewrite `tests/binding` binds, `mul` by `8` and by the `i64` signed minimum, `or disjoint`, `sdiv exact`, the shift
  round trips, two rewrites joined by `Refines.trans` and `Refine.val_map₂_mono`, and a run in the shape the emitter
  writes, joined through `andThen`.
- [`RewriteCounter.lean`](../tests/generic_rewrites/RewriteCounter.lean) has a counterexample for each hypothesis and
  flag above, and for each refinement as an equality.
- Every module rests on the standard three axioms, read as data by `tests/check_axioms.lean`, and `leanchecker` replays
  it.
- Two false rewrites in [`must_fail`](../tests/generic_rewrites/must_fail), `add x, x` to `shl x, 1` at every width and
  `mul nsw` to `shl nsw` at `k + 1 = w`, fail with an error that isn't a resource limit, and a `sorry` is refused.
- Five edits to a copy of `IRLean/Int.lean` each stop the theorem they target: `or` ignoring `disjoint` stops
  `or_disjoint_refines_add`, `mul nsw` checking unsigned overflow stops `mul_twoPow`, `udiv exact` tested the wrong way
  round stops `udiv_one`, a logical `ashr` stops `ashr_shl_nsw_refines`, and `shl` out of range giving a value stops
  `shl_lshr`. Each edit makes its theorem false, not just its proof stale.
