import CrtPopcountti2
import Kit
import Bits

/-! `tests/llvm.py` generates the module this imports from unmodified compiler-rt, and checks this fails on an injected bug. -/

namespace Llvm

open Bits

/-- The first three steps leave each byte's count in that byte. -/
theorem popcountti2_bytes (a : BitVec 128) :
    let s := a - (a >>> 1#128 &&& 113427455640312821154458202477256070485#128)
    let t := (s >>> 2#128 &&& 68056473384187692692674921486353642291#128) +
      (s &&& 68056473384187692692674921486353642291#128)
    (t >>> 4#128) + t &&& 20016609818878733144904388672456953615#128 =
      byte a 15 ++ byte a 14 ++ byte a 13 ++ byte a 12 ++ byte a 11 ++ byte a 10 ++ byte a 9 ++ byte a 8 ++
        byte a 7 ++ byte a 6 ++ byte a 5 ++ byte a 4 ++ byte a 3 ++ byte a 2 ++ byte a 1 ++ byte a 0 := by
  simp only [byte, Nat.reduceMul]
  bv_decide (config := { timeout := 120 })

/-- `__popcountti2`: the number of set bits. -/
theorem popcountti2_correct (a : BitVec 128) :
    CrtPopcountti2._popcountti2 (some a) = IRLean.Outcome.ok (some (a.cpop.setWidth 32)) := by
  simp only [IRLean.Outcome.ok]
  llvm_exec CrtPopcountti2._popcountti2
  apply IRLean.result_congr
  have layer := popcountti2_bytes a
  simp only at layer
  rw [layer]
  have h0 := byte_le a 0; have h1 := byte_le a 1; have h2 := byte_le a 2; have h3 := byte_le a 3
  have h4 := byte_le a 4; have h5 := byte_le a 5; have h6 := byte_le a 6; have h7 := byte_le a 7
  have h8 := byte_le a 8; have h9 := byte_le a 9; have h10 := byte_le a 10; have h11 := byte_le a 11
  have h12 := byte_le a 12; have h13 := byte_le a 13; have h14 := byte_le a 14; have h15 := byte_le a 15
  have hcpop := cpop_eq_bytes128 a
  rw [hcpop]
  generalize byte a 0 = c0 at *; generalize byte a 1 = c1 at *; generalize byte a 2 = c2 at *
  generalize byte a 3 = c3 at *; generalize byte a 4 = c4 at *; generalize byte a 5 = c5 at *
  generalize byte a 6 = c6 at *; generalize byte a 7 = c7 at *; generalize byte a 8 = c8 at *
  generalize byte a 9 = c9 at *; generalize byte a 10 = c10 at *; generalize byte a 11 = c11 at *
  generalize byte a 12 = c12 at *; generalize byte a 13 = c13 at *; generalize byte a 14 = c14 at *
  generalize byte a 15 = c15 at *
  clear layer hcpop
  rw [fold16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]
  rw [fold8 (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)
    (by bv_decide)]
  have := fold4 (e0 := c12 + c4 + (c8 + c0)) (e1 := c13 + c5 + (c9 + c1)) (e2 := c14 + c6 + (c10 + c2))
    (e3 := c15 + c7 + (c11 + c3)) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)
  simp only at this
  rw [this]
  congr 1
  ac_rfl

end Llvm
