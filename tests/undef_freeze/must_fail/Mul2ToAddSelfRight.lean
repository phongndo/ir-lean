import UndefFreezeTests

/-! Must fail to check, with an error that isn't a resource limit: `mul %x, 2` to `add %x, %x` isn't a refinement,
so no proof that it is can go through. This is the proof that would work if both uses of `%x` saw the same value.
`tests/undef_freeze.sh` runs this. -/

open IRLean IRLean.Experimental.UndefFreeze UndefFreezeTests

theorem mul2_to_add_self_right :
    Refines (fun x : Arg 8 => pure (mul x.uses (UVal.const 2))) (fun x => pure (add x.uses x.uses)) := by
  intro x
  rw [Run.le_pure]
  rintro b ⟨e, e', he, he', rfl⟩
  refine ⟨Val.mul e (some 2), ⟨e, some 2, he, rfl, rfl⟩, ?_⟩
  cases e <;> cases e' <;> simp [Val.add, Val.mul, ValLe] <;> bv_decide
