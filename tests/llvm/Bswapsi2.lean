import CrtBswapsi2
import Kit

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

set_option linter.unusedSimpArgs false

namespace Llvm

/-- `__bswapsi2`: the bytes in the opposite order. -/
theorem bswapsi2_correct (u : BitVec 32) :
    CrtBswapsi2._bswapsi2 (some u) =
      IRLean.Outcome.ok (some (u.extractLsb' 0 8 ++ u.extractLsb' 8 8 ++ u.extractLsb' 16 8 ++ u.extractLsb' 24 8)) := by
  simp only [CrtBswapsi2._bswapsi2, IRLean.noundef_some]
  rw [IRLean.run]
  simp only [CrtBswapsi2._bswapsi2.step, IRLean.Val.bswap, IRLean.Val.map₁, IRLean.Val.bswapRaw, IRLean.ret, IRLean.Outcome.ok,
    IRLean.noundef_some]
  simp only [Nat.reduceDiv, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    Nat.reduceMul, Nat.reduceSub, Nat.sub_zero, Nat.add_zero, BitVec.ofNat_eq_ofNat]
  llvm_close

end Llvm
