import UndefFreezeTests

/-! Must fail to check, with an error that isn't a resource limit: duplicating a `freeze` isn't a refinement, so no
proof that it is can go through. This is the proof that would work if two `freeze`s of `%x` chose the same value.
`tests/undef_freeze.sh` runs this. -/

open IRLean IRLean.Experimental.UndefFreeze UndefFreezeTests

theorem freeze_duplicated_right : Refines dupSrc dupTgt := by
  rintro x T ⟨a, ⟨c, hc, rfl⟩, b, ⟨d, hd, rfl⟩, rfl⟩
  exact ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, UVal.le_refl _⟩
