# Prove InstSimplify's sub, mul, division and remainder rewrites for every input, and their shared helpers

This is the `is-arith` family of chunk 1's G2, on top of #97. It models InstSimplify's integer arithmetic folds other
than `add`, step by step in the C++'s order, and proves each rewrite in them for every input. Its registry is
`tests/passes-proofs/peephole/folds/is-arith.json`.

## What's modelled and proved

The entry points `simplifyInstruction` calls, one per opcode:

- `simplifySubInst` (`sub`);
- `simplifyMulInst` (`mul`);
- `simplifyUDivInst` and `simplifySDivInst` (`udiv`, `sdiv`);
- `simplifyURemInst` and `simplifySRemInst` (`urem`, `srem`).

The folds and helpers they reach, each modelled for every opcode it's called with:

- `simplifyDivRem`, `simplifyDiv` and `simplifyRem`, with `isDivZero` and `isICmpTrue`;
- `simplifyByDomEq`, which `sub` and the divisions call, and which `xor`, `and` and `or` call too;
- `simplifyAssociativeBinOp`, `expandBinOp`, `expandCommutativeBinOp` and `threadBinOpOverSelect`, which `mul` and the
  divisions call, and which the logic folds call too.

Each fold has a `sound` theorem, built from one theorem per site, named by its ID, such as
`Peephole.IS.simplifyDivRem.L1114`. Each says the replacement refines the instruction for every width, every flag and
every operand, poison and undefined behaviour included. A division is an `Outcome`: dividing by zero or poison, and
the minimum divided by -1, are undefined, and an undefined source allows any replacement. The returns that hand back a
recursive call's answer, such as `return W;` after reassociating, are forwards, not sites, and have theorems too. Each
`sound` covers every value its fold returns, not just its sites.

- **40 sites** in these functions in #79's inventory:
  - 37 listed as proved;
  - 36 of those count;
  - 23 of those were exercised by `opt`.
- **`IS.threadBinOpOverSelect.L394`** is proved but doesn't count: no compared run reaches its fold. Both arms'
  recursive calls are unknown to `onInst`, so the fold always delegates.
- **3 are listed unproved:** `IS.simplifySubInst.L860` needs memory; `L759` and `IS.simplifyDivRem.L1073` are
  undef-only. [Below](#whats-unproved-and-why).

The new modules:

- `Peephole.Lemmas.Arith`: 43 value lemmas and the counterexamples for their hypotheses.
- `Peephole.IS.ArithBase`: when a division is defined, what it says about its operands, and what an analysis's answer
  says about a value.
- `Peephole.IS.ArithCore`: recursive calls, dominating conditions, forwarding to a fold modelled here, and associative
  operators.
- `Peephole.IS.ArithRecur`: the five shared helpers.
- `Peephole.IS.ArithSub`, `ArithMul`, `ArithDiv` and `ArithDivInst`: the folds.

Nothing in the core changes. `Peephole.IS.Add`'s `isKnownNegation` and its matcher lemmas are reused.

## What the proofs rest on

Beyond the standard hypotheses (operands `Consistent` with the run, no `undef`, `Oracle.Sound`):

- **`Peephole.IS.Arith.Recur.Sound`.** A recursive call into InstSimplify is a parameter, `Recur`: `simplifyBinOp`,
  and `simplifyICmpInst` for `isICmpTrue`. The hypothesis is that each value it answers, for operands consistent with
  the run and with no `undef`, is consistent, has no `undef`, and refines the operation with no flags. The sites using
  it are the four of `simplifyAssociativeBinOp`, `IS.expandBinOp.L218`, `IS.threadBinOpOverSelect.L394` and
  `IS.simplifyDivRem.L1119`. `onInst` runs with `Recur.unknown`, which is sound and answers that the model doesn't say,
  so a recursive call delegates in the comparison with `opt`.
- **`Peephole.IS.Arith.DomOracle.Sound`.** `isImpliedByDomCondition`, which `Oracle` doesn't have, is a family-local
  oracle. Each answer is true in the run for operands that aren't poison. The three sites of `simplifyByDomEq` use it,
  and `onInst` runs with `DomOracle.none`.
- **Opcodes the C++ asserts or its callers pass:**
  - an associative opcode for `simplifyAssociativeBinOp`;
  - a pair where the operator distributes over the expanded one, for `expandBinOp` (`mul` over `add`, `and` over `or`
    and `xor`, `or` over `and`);
  - `udiv`, `sdiv`, `urem` or `srem` for `simplifyDivRem`.

The registry's `rests_on` names each by site. Its `delegates` names each callee a `.delegate` step hands over to: the
constant folder, `simplifyBinOp`, `simplifyICmpInst`, `simplifyXorInst`, `simplifyAndInst`, `simplifyCastInst` and
`threadBinOpOverPHI`, which the model can't rule out for a `var` operand, since a phi is one. Each entry says why.
`Q.IIQ.UseInstrInfo` is taken as true, as InstSimplify's query has it.

## What `opt` compared

`tests/peephole.py compare --family is-arith`, against the pinned `opt`:

- 34,572 cases: 314 from 190 of InstSimplify's regression test files, and 34,258 generated.
- 16,593 compared: 7,314 where the model fires and `opt` agrees, 9,279 where neither folds, **0 mismatched**.
- 13,085 delegated: 4,997 to `simplifyICmpInst`, 2,877 to `simplifyBinOp`, 2,032 to the constant folder, 1,704 to
  `threadBinOpOverPHI`, 859 to `simplifyXorInst` and 616 to `simplifyAndInst`.
- 4,802 where `opt` changed an operand first.

`opt` exercised 23 of the counted sites, with no `undef` in the case. The other 13:

- **Recursive answers and dominating conditions:** the four of `simplifyAssociativeBinOp`, `IS.expandBinOp.L218` and
  the three of `simplifyByDomEq` fire only on a recursive answer or a dominating condition, which `onInst` doesn't
  give.
- **`IS.simplifyDivRem.L1092`** needs `computeKnownBits` to know every bit of the divisor is zero.
- **`IS.simplifyDiv.L1157`, `L1168` and `IS.simplifyRem.L1189`, `L1204`** sit behind `isDivZero`'s call to
  `simplifyICmpInst` or the `threadBinOpOverPHI` check, where the model delegates first.

In 92 cases `opt` folds and the model with `Oracle.none` doesn't, and no always-yes oracle makes it give `opt`'s
answer. Each is an analysis answer the harness's oracles don't produce, checked by running the model with the one LLVM
computes:

- **90:** `sdiv` and `srem` by `and %v0, 1`, generated, at `i8` and `i32`, 60 `sdiv` and 30 `srem`.
  - `computeKnownBits` knows every bit of the divisor is zero but the lowest. So `Known.isZero()` (L1092) is false, and
    `countMinLeadingZeros() == BitWidth - 1` (L1100) holds. `opt` answers the dividend for `sdiv` and 0 for `srem`.
  - The oracle that says every bit is zero makes the model fire L1092 and answer poison. With the known bits LLVM
    computes, it fires L1100 with `opt`'s answer.
  - The matching `udiv` and `urem` cases delegate at `isDivZero` first.
- **2:** `negate.ll`'s `@negate_zero_or_minsigned_nsw` and `@negate_zero_or_minsigned`, `sub nsw i8 0, (and %v,
  -128)` to 0 and `sub i8 0, (shl %v, 7)` to `%n1`.
  - LLVM knows every bit but the sign bit is zero there, which is what `Known.Zero.isMaxSignedValue()` (L780, L783)
    tests for.
  - No always-yes oracle gives that. With it, the model fires L780 and L783 with `opt`'s answers.

## The store's dry run

`tests/peephole.py store --family is-arith --dry-run` offered the registry's 43 lemmas: **7 admitted, 36 candidates,
0 refused.**

- The admitted ones are `mul_comm`, `mul_udiv_exact_refines`, `mul_sdiv_exact_refines` and the four `*_self_refines`
  for `udiv`, `urem`, `sdiv` and `srem`.
- The 19 lemmas with hypotheses have a `drop_<hypothesis>` counterexample for each, 21 in all, and a `sat` witness in
  `Peephole/Lemmas/Arith.lean`. The store checked each states what it has to.

Nothing is stored yet.

## E3

`tests/peephole.py measure --family is-arith`:

- Each site's proof takes 2.1 to 66.3 ms, of which the kernel takes 0.09 to 2.0 ms.
- Each module of the family peaks at 690 to 751 MiB, and takes 0.34 to 0.56 s.
- 9 of the 37 listed proofs use a stored rewrite lemma, all of them #48's: `sub_zero`, `sub_self_refines`,
  `mul_zero_refines`, `mul_one_refines`, `xor_self_refines`, `and_self`, `or_self_disjoint_refines`, `udiv_one`,
  `sdiv_one_refines`, `urem_one_refines` and `srem_one_refines`. This family's own lemmas count once the store admits
  them.
- Over 12 pairs of a site and a lemma it names, the kernel's median check is 0.975 ms with the stored lemma and 1.434
  ms with its proof inlined.

## What's unproved and why

- **`IS.simplifySubInst.L860`** needs memory. It folds `ptrtoint` of two pointers off one base to their constant offset
  difference. No `Term` is a `ptrtoint`, so the model's step for it never matches.
- **`IS.simplifySubInst.L759`** (`X - undef` to `undef`) and **`IS.simplifyDivRem.L1073`** (`undef / X` to 0) are
  undef-only. `Q.isUndefValue` holds of poison too, but the poison steps before them, L754 and L1068, take poison
  first. Only `undef` reaches them, and every case they fired on had one. Their theorems, about the poison reading,
  stay, and their folds' `sound` theorems use them.

## Tests

Run locally on macOS, on `chunk1/g2-is-arith` with `chunk1/g2-core` at `435684e` merged in:

- `lake build`, then `lake build --wfail Peephole`.
- `tests/check_axioms.lean` on `Peephole.IS.ArithSub`, `ArithMul` and `ArithDivInst`, which import the rest: at most
  the standard three axioms, and 0 from `bv_decide`.
- `tests/peephole.py compare --family is-arith --write` and `score --check`: every site the registry lists as proved
  counts but L394, which is proved and not compared.
- `tests/peephole.py store --family is-arith --dry-run` and `measure --family is-arith`.
- `ruff format --check` passes. `ruff check` reports I001 in `tests/verdict_test.py`, `tests/verify_claims_test.py` and
  `tools/prooftest/bench.py`, which this doesn't touch: the case-insensitive disk's sorting of `irlean` imports that
  #97 describes.
- `rumdl check` on this text.

The score with this family, from `score`:

| Pass | Rewrites | Proved | % | Of those, exercised by `opt` | Integers only | Proved of those | % |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InstSimplify | 541 | 43 | 7.95 | 30 | 300 | 43 | 14.33 |

| Family | Sites listed | Proved | Exercised by `opt` | Proved, model not compared | Undef only | Listed unproved |
| --- | --- | --- | --- | --- | --- | --- |
| `is-arith` | 37 | 36 | 23 | 1 | 0 | 3 |
