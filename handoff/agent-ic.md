# InstCombine family agents: what's on top of the common rules

Read `handoff/agent-common.md` first; everything there applies.

InstCombine's method is on branch `chunk1/g2-ic-add` (head 7a3d4ea, in review, not merged yet). Read, in this order:
- `handoff/pr-ic-add.md (on branch chunk1/g2-handoff)`: what the pilot built and decided.
- `docs/rewrite-proofs.md` on that branch: the InstCombine sections (how folds are modelled, how new IR is compared
  with `opt`, what the comparison can and can't catch).
- `tests/passes-proofs/peephole/Peephole/IC/Base.lean` (`Ctx`, builder constant folding, in-place changes),
  `Peephole/IC/Add.lean` (`visitAdd`'s model: forward to `simplifyAddInst`'s model, delegations, then
  `foldAddWithConstant`), `Peephole/IC/AddConst.lean` (the 18 proved sites), `Peephole/Lemmas/ICAdd.lean`,
  `folds/ic-add.json`, `compared/ic-add.json`.
- The pinned C++: `$LLVM_PROJECT_SRC/llvm/lib/Transforms/InstCombine/` (`InstCombineAddSub.cpp`,
  `InstructionCombining.cpp`, `InstCombineInternal.h`), `llvm/include/llvm/Transforms/InstCombine/InstCombiner.h`,
  `llvm/include/llvm/IR/PatternMatch.h`, `llvm/lib/IR/ConstantFold.cpp`.

Rules on top of the common ones:
- Build on `Peephole/IC/Base.lean` as it is. If you need more in it, add beside it (your own module, or an additive
  definition with its own theorem) and say why; don't change what `ic-add` uses.
- Each site's theorem holds for every `Ctx`, every width, flag and operand, poison included. A `return &I` after an
  in-place change fires the instruction `I` becomes, under the change's ID. IRBuilder's constant folding uses Base's
  functions.
- Steps the C++ takes that you don't model are `.delegate` with predicates as precise as you can make them, so the
  comparison isn't all delegated, and never narrower than the C++ (a delegate that's too narrow lets the model answer
  where LLVM would have taken an earlier fold, which shows up as a mismatch).
- Reuse stored lemmas first (`IRLean.Generic.*`, `Peephole.Lemmas.*` from `is-add`, `is-arith`, `ic-add`). E3 is
  measuring whether the store makes later proofs cheaper; report which you reused.
- The lane owner may merge review fixes into `chunk1/g2-ic-add`: `git fetch` and merge `origin/chunk1/g2-ic-add` when
  it moves. When `main` has the core (PR #97) and `ic-add`, merge `origin/main`.
- `compare --family <yours> --write` must have 0 mismatches, and `--family ic-add` must stay at 0 too if you touch
  anything it imports.
