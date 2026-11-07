import CrtBswapdi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

set_option linter.unusedSimpArgs false

namespace Llvm

/-- `__bswapdi2`: the bytes in the opposite order. -/
theorem bswapdi2_correct (u : BitVec 64) :
    CrtBswapdi2._bswapdi2 (some u) =
      IRLean.Outcome.ok (some (u.extractLsb' 0 8 ++ u.extractLsb' 8 8 ++ u.extractLsb' 16 8 ++ u.extractLsb' 24 8 ++
        u.extractLsb' 32 8 ++ u.extractLsb' 40 8 ++ u.extractLsb' 48 8 ++ u.extractLsb' 56 8)) := by
  simp only [CrtBswapdi2._bswapdi2, IRLean.noundef_some]
  rw [IRLean.run]
  simp only [CrtBswapdi2._bswapdi2.step, IRLean.Val.bswap, IRLean.Val.map₁, IRLean.Val.bswapRaw, IRLean.ret, IRLean.Outcome.ok,
    IRLean.noundef_some]
  simp only [Nat.reduceDiv, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceSub, Nat.sub_zero, Nat.add_zero, BitVec.ofNat_eq_ofNat]
  llvm_close

end Llvm
