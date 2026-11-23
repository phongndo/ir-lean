/-- **The candidate's `argon2_fill_segment_avx512f` does what the baseline's does,** for every argument and memory:
where the baseline's returns, the candidate's returns with the same memory, and where the baseline's never finishes,
neither does the candidate's. Where the baseline's is undefined or the model has no answer for it, there's no
claim. -/
theorem argon2_fill_segment_avx512f_same (a0 : PtrVal) (a1 a2 : Val 64) (m : Mem) :
    Outcome.Sim Eq (Base.argon2_fill_segment_avx512f a0 a1 a2 m) (Cand.argon2_fill_segment_avx512f a0 a1 a2 m) := by
  simp only [Base.argon2_fill_segment_avx512f, Cand.argon2_fill_segment_avx512f]
  refine Mono.noundefPtr (Refine.Reflexive.refl _) ?_
  rw [Mem.call_eq, Mem.call_eq]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  simp only [Mem.withFrame]
  refine Outcome.Sim.andThen (r := Eq) ?_ fun x y h => by subst h; exact Outcome.Sim.refl (fun _ => rfl) _
  exact Outcome.Sim.promised step_sim promise_eq rfl

/-- **libsodium's `argon2_fill_segment_avx512f` with rows A, C and D rotated refines the one with rows B, C and D
rotated, as clang compiled both,** for every argument, on every memory the model has an answer for. -/
theorem argon2_fill_segment_avx512f :
    Refines (fun a0 a1 a2 m => (Base.argon2_fill_segment_avx512f a0 a1 a2 m).answered)
      Cand.argon2_fill_segment_avx512f :=
  fun a0 a1 a2 m => (Refine.answered_iff _ _).2
    ((argon2_fill_segment_avx512f_same a0 a1 a2 m).mono fun x y h => by
      subst h; exact ⟨Refine.unit _ _, Mem.le.refl _⟩)

#print axioms argon2_fill_segment_avx512f_same
#print axioms argon2_fill_segment_avx512f
