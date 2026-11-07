import CrtParityti2
import Kit
import Bits

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

open Bits

/-- `__parityti2`: 1 if an odd number of bits are set. -/
theorem parityti2_correct (a : BitVec 128) :
    CrtParityti2._parityti2 (some a) = IRLean.Outcome.ok (some ((a.cpop &&& 1#128).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtParityti2._parityti2
  apply IRLean.result_congr
  have hfold := parity_fold a 64 rfl
  generalize hb : a.extractLsb' 0 64 ^^^ a.extractLsb' 64 64 = b at hfold
  have hfold' := parity_fold b 32 rfl
  have hy : ((((a >>> 64#128) ^^^ a) >>> 32#128) ^^^ ((a >>> 64#128) ^^^ a)).setWidth 32 =
      b.extractLsb' 0 32 ^^^ b.extractLsb' 32 32 := by
    subst hb
    bv_decide
  rw [show (1#128 : BitVec 128) = BitVec.ofNat 128 1 from rfl,
    parity_setWidth (by omega) a _ (hfold'.trans hfold), hy]
  generalize b.extractLsb' 0 32 ^^^ b.extractLsb' 32 32 = y
  bv_decide

end Llvm
