import CrtPopcountdi2
import Kit
import Bits

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

open Bits

/-- The first three steps leave each byte's count in that byte. -/
theorem popcountdi2_bytes (a : BitVec 64) :
    let s := a - (a >>> 1#64 &&& 6148914691236517205#64)
    let t := (s >>> 2#64 &&& 3689348814741910323#64) + (s &&& 3689348814741910323#64)
    (t >>> 4#64) + t &&& 1085102592571150095#64 =
      byte a 7 ++ byte a 6 ++ byte a 5 ++ byte a 4 ++ byte a 3 ++ byte a 2 ++ byte a 1 ++ byte a 0 := by
  simp only [byte, Nat.reduceMul]
  bv_decide (config := { timeout := 120 })

/-- `__popcountdi2`: the number of set bits. -/
theorem popcountdi2_correct (a : BitVec 64) :
    CrtPopcountdi2._popcountdi2 (some a) = IRLean.Outcome.ok (some (a.cpop.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtPopcountdi2._popcountdi2
  apply IRLean.result_congr
  have layer := popcountdi2_bytes a
  simp only at layer
  rw [layer]
  have h0 := byte_le a 0; have h1 := byte_le a 1; have h2 := byte_le a 2; have h3 := byte_le a 3
  have h4 := byte_le a 4; have h5 := byte_le a 5; have h6 := byte_le a 6; have h7 := byte_le a 7
  have hcpop := cpop_eq_bytes64 a
  rw [hcpop]
  generalize byte a 0 = c0 at *; generalize byte a 1 = c1 at *; generalize byte a 2 = c2 at *
  generalize byte a 3 = c3 at *; generalize byte a 4 = c4 at *; generalize byte a 5 = c5 at *
  generalize byte a 6 = c6 at *; generalize byte a 7 = c7 at *
  clear layer hcpop
  rw [fold8 (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)
    (by bv_decide)]
  have := fold4Small (e0 := c4 + c0) (e1 := c5 + c1) (e2 := c6 + c2) (e3 := c7 + c3)
    (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)
  simp only at this
  rw [this]
  congr 1
  ac_rfl

end Llvm
