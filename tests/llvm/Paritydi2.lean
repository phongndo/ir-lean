import CrtParitydi2
import Kit
import Bits

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

open Bits

/-- `__paritydi2`: 1 if an odd number of bits are set. -/
theorem paritydi2_correct (a : BitVec 64) :
    CrtParitydi2._paritydi2 (some a) = IRLean.Outcome.ok (some ((a.cpop &&& 1#64).setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtParitydi2._paritydi2
  apply IRLean.result_congr
  have hfold := parity_fold a 32 rfl
  have hy : ((a >>> 32#64) ^^^ a).setWidth 32 = a.extractLsb' 0 32 ^^^ a.extractLsb' 32 32 := by bv_decide
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, parity_setWidth (by omega) a _ hfold, hy]
  generalize a.extractLsb' 0 32 ^^^ a.extractLsb' 32 32 = y
  bv_decide

end Llvm
