/-- **The candidate's `fill_block_with_xor` does what the baseline's does,** for every pointer and memory: where the
baseline's returns, the candidate's returns with the same memory, and where the baseline's never finishes, neither
does the candidate's. Where the baseline's is undefined or the model has no answer for it, there's no claim. -/
theorem fill_block_with_xor_same (a0 a1 a2 : PtrVal) (m : Mem) :
    Outcome.Sim Eq (Base.fill_block_with_xor a0 a1 a2 m) (Cand.fill_block_with_xor a0 a1 a2 m) := by
  simp only [Base.fill_block_with_xor, Cand.fill_block_with_xor]
  refine Mono.noundefPtr (Refine.Reflexive.refl _) (Mono.noundefPtr (Refine.Reflexive.refl _)
    (Mono.noundefPtr (Refine.Reflexive.refl _) ?_))
  rw [Mem.call_eq, Mem.call_eq]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  exact Outcome.Sim.promised step_sim promise_eq rfl

/-- **libsodium's `fill_block_with_xor` with rows A, C and D rotated refines the one with rows B, C and D rotated, as
clang compiled both,** for every pointer, on every memory the model has an answer for. -/
theorem fill_block_with_xor :
    Refines (fun a0 a1 a2 m => (Base.fill_block_with_xor a0 a1 a2 m).answered) Cand.fill_block_with_xor :=
  fun a0 a1 a2 m => (Refine.answered_iff _ _).2
    ((fill_block_with_xor_same a0 a1 a2 m).mono fun x y h => by subst h; exact ⟨Refine.unit _ _, Mem.le.refl _⟩)

#print axioms fill_block_with_xor_same
#print axioms fill_block_with_xor
