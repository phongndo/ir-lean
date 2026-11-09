# Prove InstCombine's folds for every input, starting with `visitAdd` through `foldAddWithConstant`, and compare their new IR with `opt`'s

This starts InstCombine in chunk 1's G2, on top of #97. It does three things: it says how an InstCombine fold is
modelled and proved, beside the core and without changing it; it fills in the comparison of new IR with `opt`, which
answered "not compared" before; and it proves InstCombine's first family, `ic-add`, `visitAdd` as far as
`foldAddWithConstant` and through it. Its registry is `tests/passes-proofs/peephole/folds/ic-add.json`.

## The method

`Peephole.IC.Base` adds what InstCombine's models share. Nothing in `Peephole.{Term,Match,Oracle,Fold}` changes: a
fold is still a list of `Step`s run by `run`, and its answer is a `Repl`.

- **New instructions:** a step that returns `BinaryOperator::CreateSub(C, X)` fires `.bin .sub {} (.const c) (.old
  x)`, with the flags the C++ sets on what it creates.
- **Constant folding:** `Builder.CreateNot`, `CreateIsNotNeg`, `CreateShl`, `CreateBinaryIntrinsic`,
  `ConstantExpr::getAdd` and `getSub`, and `InstCombiner::AddOne` and `SubOne` fold constant operands to a constant,
  as `TargetFolder` and `ConstantFold.cpp` do, poison and `undef` by their rules. Each is a function on `Term`s, with a
  theorem that its value is the instruction's.
- **In-place changes:** `I.setHasNoSignedWrap(true)` or `replaceOperand(I, ...)` and `return &I` fire the instruction
  `I` becomes. `return &I` after a change the model doesn't follow, as after `SimplifyAssociativeOrCommutative`, is
  `.delegate`.
- **Forwards:** `replaceInstUsesWith(I, V)` answers `V`, and `visitAdd`'s call to `simplifyAddInst` forwards to
  `Peephole.IS.simplifyAddInst`, whose `sound` theorem is that step's.
- **What isn't an operand or an analysis:** `V->hasOneUse()` and `isa<PHINode>(V)` are a `Ctx` the model takes, and
  every theorem holds for every `Ctx`.
- **Delegated:** the pass around the fold, its worklist, replacing uses, revisiting users, deleting what's dead and
  running to a fixpoint, and every step the model doesn't follow, where it could fire.

A fold's theorem 1, in the sense of `docs/binding-approach.md`'s two theorems per unit, is that
each value it answers refines `I`, with `Repl.eval` running the new instructions, at every width, for every flag,
`Ctx` and sound `Oracle`, poison included. `Peephole.IC.visitAdd.sound` is it for `visitAdd`. An entry point takes the
`Ctx` first: `visitAdd.onInst (c : Ctx) (o : Oracle) : {w : Nat} → Term w → Result w`.

## The comparison of new IR

`compare_new_ir` in `tests/peephole.py` is filled in, and an entry point whose `opt` pass is `instcombine` changes the
comparison in four ways:

1. **Two shapes per case:** with a call keeping the root's operands alive, so each has more than one use, and without
   it, so each has the uses the tree gives it and a fold that needs one use can fire.
2. **The `Ctx` is the case's function's:** the harness counts each argument's and instruction's uses in the function
   `opt` runs, and the Lean driver builds the `Ctx` from them. `tests/peephole/Harness.lean` runs an entry point that
   takes a `Ctx` with it, and one that doesn't as before.
3. **An operand changed first:** with the call, every line up to it has to come out as it went in; without it, the
   same function with the root replaced by an opaque call of the same operands, which has the same uses, has to.
4. **Normalized answers:** the case's function with the root replaced by the model's new instructions is run through
   `opt -passes=instcombine`, and has to return the same expression as `opt`'s output, read down to arguments and
   constants, so names and the order of lines don't matter.

A model that fires where `opt` leaves the root alone is a mismatch, even where its answer normalizes back to the root,
and so is one whose normalized answer returns another expression. A step the model delegates, which `opt`'s first fold
may be, leaves the case uncompared. Two right answers that normalize apart would be reported as a mismatch, which
errs toward failing; none came up. `alive-tv` isn't in the dev shell, so nothing checks two different answers are
equivalent. `docs/rewrite-proofs.md` says what this can and can't catch.

Three broken models of `foldAddWithConstant` are caught, each at its own site only, and `tests/peephole_test.py
--tier live` keeps them:

- dropping `(nsw || nuw)` from `X + signmask` to a disjoint `or`: 60 mismatches, at `L936`;
- dropping the one-use guard of `add (sub X, Y), -1`: 9, at `L881`, in the shape with the call;
- folding `add (sub C1, X), C2`'s constants with `sub`: 58, at `L874`.

InstCombine's tests also turned up a harness bug: an instruction reached both near the root and past the depth limit
got one identity as a node and as an argument, so the case's function used a value it never defined. A cut-off
instruction is now an argument of its own.

## What's modelled and proved

- `visitAdd`, step by step: the forward to `simplifyAddInst`; `SimplifyAssociativeOrCommutative`, `foldVectorBinop`,
  `foldBinopWithPhiOperands`, `foldUsingDistributiveLaws`, `foldBoxMultiply` and `factorizeMathWithShlOps`, each
  delegating where it could fire, as far as its first matches say; `foldAddWithConstant`; and the rest of `visitAdd`,
  from `foldNoWrapAdd` on, one step that delegates unless both operands are different arguments or constants wider
  than `i1`, where none of its steps fires.
- `foldAddWithConstant`, all 18 of its sites, each with a theorem named by its ID, such as
  `Peephole.IC.AddSub.foldAddWithConstant.L874`, and `Peephole.IC.foldAddWithConstant.sound` over them.

**18 sites listed as proved, all 18 count, 13 exercised by `opt`.** `L959`, `L976` and `L1020` need known bits or
`isKnownNonZero` of an instruction operand, which `Oracle.none` doesn't give. `L989` and `L997` can't fire: `L891`
takes every `sext` of an `i1` plus a constant first, and `L911` every `ashr` by `N - 1` with one use plus 1. They're
modelled and proved as the C++ has them.

**`L902` is wrong at `i1` on its own.** `~X + C` to `(C - 1) - X` keeps `nsw` when `C - 1` doesn't overflow, but at
`i1` the constant `1` is `-1`: `add nsw (xor %p, true), true` is `true` for `%p = true`, and `sub nsw false, %p` is
poison. `visitAdd` never reaches it there, since `simplifyAddInst`, which it calls first, answers every `i1` `add`. The
site's theorem assumes the `add` has no `nsw` or isn't an `i1`, and `visitAdd.sound` proves that from the steps'
order.

The new modules:

- `Peephole.IC.Base`: the method, as above.
- `Peephole.IC.AddConst`: `foldAddWithConstant`'s model, its matchers, its 18 site theorems and its `sound`.
- `Peephole.IC.Add`: `visitAdd`'s model, `onInst`, and `visitAdd.sound`.
- `Peephole.Lemmas.ICAdd`: 33 value lemmas, and 28 counterexamples and witnesses for their hypotheses.

## What the proofs rest on

Beyond the standard hypotheses (operands `Consistent` with the run, no `undef`, `Oracle.Sound`):

- **`L902`, and `foldAddWithConstant.sound`:** `w ≠ 1 ∨ nsw = false`, as above. `visitAdd.sound` has no hypothesis
  beyond the standard ones. The registry's `rests_on` says so.
- **Analyses on constants:** `willNotOverflowSignedAdd` and `willNotOverflowSignedSub` on two constants are computed,
  as `computeOverflowForSigned*` answers on them, not taken from the `Oracle`.

The registry's `delegates` names each callee a `.delegate` step hands over to, with the condition it delegates on.

## What `opt` compared

`tests/peephole.py compare --family ic-add`, against the pinned `opt`, in 5 s:

- 22,376 cases, half in each shape: 2,800 from 1,673 of InstCombine's regression test files, 1,400 distinct `add`s,
  and 19,576 generated.
- 4,319 compared: 3,675 where the model fires and `opt` agrees, 3,210 of them through `simplifyAddInst`'s model and
  465 new IR; 644 where neither folds; **0 mismatched**.
- 10,684 delegated: 5,204 to the rest of `visitAdd`, 1,708 to `SimplifyAssociativeOrCommutative`, 1,160 to the
  constant folder, 1,138 to `simplifyAssociativeBinOp`, 772 to `simplifyXorInst`, 692 to `foldUsingDistributiveLaws`
  and 10 to `factorizeMathWithShlOps`.
- 7,373 where `opt` changed an operand first.
- 0 where `opt` folds and the model doesn't.

The model answers `nullptr` only on two leaves, so most cases where `foldAddWithConstant` declines are delegated: a
model that failed to fire where the C++ does would mostly go unseen, and one that fires where it doesn't is always
seen. `is-add`'s comparison is unchanged: 9,915 cases, 6,318 compared, 0 mismatched.

## The store's dry run

`tests/peephole.py store --family ic-add --dry-run` offered 27 of the 33 lemmas: **2 admitted, 25 candidates, 0
refused.** The admitted ones are `sub_eq_xor_of_and_eq` and `add_ashr_sign_one`. The 9 offered lemmas with hypotheses
have a `drop_<hypothesis>` counterexample for each, 11 in all, and a `sat` witness, in `Peephole/Lemmas/ICAdd.lean`.
The 6 not offered are helpers the store found trivial, or not in its normal form. Four hypotheses no counterexample
could show needed, such as `0 < w` where the lemma holds at width 0 too, were dropped from their lemmas. Nothing is stored
yet.

## E3

`tests/peephole.py measure --family ic-add`:

- Each site's proof takes 6.7 to 56.5 ms, of which the kernel takes 0.41 to 2.63 ms.
- `Peephole.IC.Base` takes 1.16 s and peaks at 876 MiB, `Peephole.Lemmas.ICAdd` 0.65 s and 875 MiB,
  `Peephole.IC.AddConst` 0.93 s and 919 MiB, and `Peephole.IC.Add` 0.48 s and 841 MiB. Importing alone costs about
  800 MiB on this machine.
- 17 of the 18 proofs use a stored rewrite lemma, each cut from `simplifyAddInst`'s proofs, which E3 counts as reuse:
  `add_refines_of_sum` in 15, `add_intMin` in 5 and `add_none_right` in 3. `L924`'s uses none. `IRLean.Generic`'s
  `add_of_and_eq_zero` and `shiftOk_iff` helped prove the new lemmas.
- One pair of a site and a stored lemma its proof names came up: the kernel took 1.14 ms with the lemma and 1.23 ms
  with its proof inlined.

## What's unproved and why

All 35 of `visitAdd`'s own sites, `IC.AddSub.visitAdd.L1640` to `L1996`: the model follows `visitAdd` through
`foldAddWithConstant` and delegates the rest, from `foldNoWrapAdd` on, as one step. Each entry in the registry says
which rewrite it is, and what more it needs, such as `willNotOverflowSignedAdd` for the in-place `nsw` of `L1943`.

## Tests

Run on Linux, 32 cores and 30 GB shared with four other lanes, on `chunk1/g2-ic-add` with `chunk1/g2-core` at
`656eddd`. #97 hasn't merged, so `main` isn't merged in:

- `lake build --wfail Peephole`.
- `tests/check_axioms.lean` on `Peephole.IC.Base`, `IC.AddConst`, `IC.Add` and `Lemmas.ICAdd`: at most the standard
  three axioms, and 0 from `bv_decide`.
- `tests/peephole.py compare --family ic-add --write`, `compare` for both families, `score --check`, `store --family
  ic-add --dry-run` and `measure --family ic-add`.
- `tests/peephole_test.py --tier static`, 25 tests, and `--tier live`, 7, and `tests/irlean_test.py`.
- `ruff format --check` and `ruff check`, and `rumdl check` on the docs.

The score with this family, from `score`:

| Pass | Rewrites | Proved | % | Of those, exercised by `opt` | Integers only | Proved of those | % |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InstSimplify | 541 | 7 | 1.29 | 7 | 300 | 7 | 2.33 |
| InstCombine | 2,536 | 18 | 0.71 | 13 | 1,499 | 18 | 1.2 |
| All | 3,174 | 25 | 0.79 | 20 | 1,837 | 25 | 1.36 |

| Family | Sites listed | Proved | Exercised by `opt` | Proved, model not compared | Undef only | Listed unproved |
| --- | --- | --- | --- | --- | --- | --- |
| `ic-add` | 18 | 18 | 13 | 0 | 0 | 35 |
