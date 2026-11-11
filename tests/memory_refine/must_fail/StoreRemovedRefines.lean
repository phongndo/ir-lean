import MemoryRefine

/-! A wrong rewrite mustn't be certified. This is `MemoryRefine.store_forwarded_right`'s proof, about
`store_removed_wrong`: the target drops the store the load reads, so where the source's load gives what was stored,
the target's gives what was there. `tests/memory_refine.sh` checks it fails, with an error of its own. -/

open IRLean

theorem store_removed_refines :
    Refines (fun p a m => (store_removed_wrong_ir.src p a m).answered) store_removed_wrong_ir.tgt := by
  intro p a m
  rw [Refine.answered_iff]
  simp only [store_removed_wrong_ir.src, store_removed_wrong_ir.tgt, run_eq, store_removed_wrong_ir.src.step,
    store_removed_wrong_ir.tgt.step, andThen_assoc, andThen_ret_run]
  rcases Mem.storeInt_error_or_ok m p a 4 with ⟨e, he⟩ | ⟨m₁, h₁⟩
  · rw [he]; trivial
  · rw [h₁, andThen_ok]
    rcases Mem.loadInt_of_storeInt h₁ (by decide) (by decide) with hl | ⟨e, hl⟩
    · rw [hl, andThen_ok]
      exact Outcome.Sim.ok ⟨Refine.refl_val a, Mem.le.refl m₁⟩
    · rw [hl]; trivial
