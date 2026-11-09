# Chunk 1's G2: where the 2026-11-09 wave stopped

## On `main`

- **#97** (squash `4da6cbb`): the core. That's the `Peephole` library, `tests/peephole.py` (`compare`, `score`,
  `measure`, `store`), the store's link to rewrites, and `simplifyAddInst`.
- **#103** (squash `5812c8b`): InstSimplify's families `is-arith`, `is-logic`, `is-icmp`, `is-icmp-b` (connected to
  `is-icmp`), `is-shift` and `is-intrinsic`, their lemmas in the store, and the inventory's fix for integer-intrinsic
  tags.
- **Score:** InstSimplify 244 of 541 rewrites counted (45.1%), 242 of its 335 integer-only (72.2%), and 171 of the 244
  exercised by `opt`. InstCombine, AggressiveInstCombine and Reassociate are at 0. `tests/peephole.py score`
  re-runs it; `docs/rewrite-proofs.md` has the tables and E3.

## Parked

- **`chunk1/g2-ic-add`** (head `7a3d4ea`): InstCombine's method and its first family. `Peephole/IC/Base.lean`, the
  comparison of new IR with `opt` (`compare_new_ir`), and `visitAdd` through `foldAddWithConstant`: 18 sites counted,
  0 mismatches. Independent review: 1 round, approved. It branched from the core before #97 merged.
  Next step:
  - merge `origin/main`, and resolve `docs/rewrite-proofs.md` and `tests/peephole.py` against #103's changes;
  - `compare --family ic-add --write` and the InstSimplify families' compares, since the harness changed;
  - `score --check`, then `store --family ic-add`;
  - open the PR with `handoff/pr-ic-add.md`'s body, numbers refreshed.
- **Nothing else.** The rest of `visitAdd`, `visitSub` and the floating-point pilot (`is-fp`) were stopped before
  they committed anything. Their branches were never pushed.

## Next, in order

1. Ship `ic-add`, as above.
2. InstCombine families on its method, using `handoff/agent-common.md` and `handoff/agent-ic.md` as the briefs:
   - the rest of `visitAdd` (35 sites), and `visitSub` (39), in `InstCombineAddSub.cpp`;
   - then `visitMul` and the divisions, the `and`/`or`/`xor` visitors, `foldICmpBinOp` and the shifts.

   E3 should show whether InstCombine reuses InstSimplify's stored lemmas: across InstSimplify's families only 28 of
   247 proofs used another family's.
3. Floating point: SEM-05 slices 1 to 3 are in the model, `nsz` included.
   - A float operand type and refinement over the NaN choice, beside `Term`;
   - then InstSimplify's `fneg`, `fadd`, `fsub`, `fmul`, `fdiv` and `frem` folds.

   The 34 integer instances in `unproved` that floating point reaches are the other half of that.
4. Pointers wait for F4.
5. The inventory's two known rule errors:
   - `foldMinMaxSharedOp`'s case label is in its caller;
   - `m_FShl`/`m_FShr` read as floating-point matchers.

   Fixing them would let `is-icmp-b`'s `L4876`, `L4890`, `L4896` and `L4900` count.

## The hardest left in InstSimplify

- **`simplifySelectInst`'s 30 sites:** a select's arms can be any type, so each needs floating point and pointers too.
- **The vector and aggregate folds:** `extractelement`, `insertelement`, `shufflevector`, `insertvalue` and
  `extractvalue` need a vector `Term`.
- **`simplifyWithOpsReplaced` past its first loop:** induction over the recursive calls on `V`'s operands.
- **`IS.simplifySelectWithICmpCond.L4857`:** needs `matchDecomposedSelectPattern`.
