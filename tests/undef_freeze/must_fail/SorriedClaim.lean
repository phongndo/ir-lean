import UndefFreezeTests

/-! Compiles, but must fail the axiom check: `sorry` is an axiom outside the standard three. `tests/undef_freeze.sh`
compiles this without warnings as errors, so only the axiom check can stop it. -/

open IRLean IRLean.Experimental.UndefFreeze UndefFreezeTests

theorem freeze_duplicated_right : Refines dupSrc dupTgt := sorry
