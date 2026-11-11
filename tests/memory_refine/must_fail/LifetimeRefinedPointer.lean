import IRLean.MemRefineOps

/-! `llvm.lifetime.start` and `.end` keep the relation only through the same pointer: on poison they do nothing, and
on the pointer the target has for it they start or end an allocation's life, which the source's memory doesn't
allow. This states `IRLean.Mem.le.lifetime` for a pointer the target's refines, and its proof stops at the source's
poison. `tests/memory_refine.sh` checks this fails, there. -/

open IRLean

theorem lifetime_refined {m m' : Mem} (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (alive : Bool) :
    Outcome.Sim Refine.le (m.lifetime p alive) (m'.lifetime p' alive) := by
  cases p with
  | none => exact Outcome.Sim.ok h
  | some q =>
    cases hp
    simp only [Mem.lifetime]
    cases ha : m.allocs q.block with
    | none => rw [h.gone ha]; exact Outcome.Sim.ok h
    | some a =>
      obtain ⟨a', ha', hle⟩ := h.alloc ha
      rw [ha']
      exact Outcome.Sim.ok (h.setAlloc _ (.some ⟨hle.size, rfl, hle.heap, hle.stack, fun _ => Byte.le.refl _⟩))
