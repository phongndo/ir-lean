import LemmaStore.Select

/-! Lean's own premise selection sees the store once `LemmaStore.Select` is imported: its selector puts the stored
lemmas a goal is an instance of first, so `grind +suggestions` proves these from them, with no hint of which. -/

open IRLean

/-- `add i32 %x, 0` to `%x`, from `IRLean.Generic.add_zero`. -/
example (x : Val 32) : Val.add x (some 0#32) true false = x := by grind +suggestions

/-- `lshr i256 (shl nuw i256 %x, %s), %s` to `%x`, from `IRLean.Generic.lshr_shl_nuw_refines`. -/
example (x s : Val 256) : Refines (Val.lshr (Val.shl x s true false) s) x := by grind +suggestions
