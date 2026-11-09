import IRLean.Generic.Arith

open IRLean IRLean.Generic

/-- False: at `k + 1 = w`, `mul nsw x, 2 ^ k` isn't `shl nsw x, k`, which is why `instcombine` drops `nsw` there.
`tests/generic_rewrites.sh` checks that this fails to check. -/
theorem mul_twoPow_keeps_nsw {w k : Nat} (a : Val w) (hk : k < w) (nuw : Bool) :
    Refines (Val.mul a (some (BitVec.twoPow w k)) nuw true) (Val.shl a (some (BitVec.ofNat w k)) nuw true) := by
  rw [mul_twoPow a rfl hk nuw true (.inr (by omega))]
  exact Refines.refl _
