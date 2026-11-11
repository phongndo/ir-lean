import IRLean.MemRefineOps

/-! On memories related by `Mem.le`, a load of a vector keeps refinement or the target's stops the model: where the
source's bytes were poison or uninitialized, the target's may hold a pointer, which a load of integers can't read.
This states it without the second case, and `IRLean.Mem.le.loadVec`'s proof, word for word, stops where the target's
load stops the model. `Mem.leData` is the relation that rules that out. `tests/memory_refine.sh` checks this fails,
there. -/

open IRLean

theorem loadVec_outright {m m' : Mem} (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (n w align : Nat) :
    Outcome.Sim Refine.le (Mem.loadVec n w m p align) (Mem.loadVec n w m' p' align) := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    simp only [Mem.loadVec]
    rcases h.access_cases (some q) (n * (w / 8)) align with ⟨e, he, he'⟩ | ⟨q₀, a, a', ha, ha', hle⟩
    · rw [he, he']; trivial
    · simp only [ha, ha', h.check hle]
      cases m.check q₀ a false with
      | some e => trivial
      | none =>
        dsimp only
        -- Each side's lanes, as the loads collect them.
        generalize hL : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L
        generalize hL' : List.map (fun (i : Nat) => (_ : Except ModelStop (Option Nat))) (List.range n) = L'
        have hlane : ∀ (i k : Nat), L[i]? = some (.ok (some k)) → L'[i]? = some (.ok (some k)) := by
          intro i k hk
          rw [← hL, List.getElem?_map] at hk
          rw [← hL', List.getElem?_map]
          cases hr : (List.range n)[i]? with
          | none => rw [hr] at hk; cases hk
          | some j =>
            rw [hr] at hk
            simp only [Option.map_some, Option.some.injEq] at hk ⊢
            exact Mem.le.collect (forall₂_map_self (fun _ => h.visible hle q₀ _) _) hk
        -- Both sides test a lane for an error the same way.
        generalize hP : (fun (l : Except ModelStop (Option Nat)) => (_ : Option ModelStop)) = P
        cases hS : L.findSome? P with
        | some e => trivial
        | none =>
          cases hT : L'.findSome? P with
          | some e => exact trivial
          | none =>
            refine Outcome.Sim.ok fun i => ?_
            rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
            cases hi : L[i.val]? with
            | none => trivial
            | some r =>
              cases r with
              | error e => trivial
              | ok r =>
                cases r with
                | none => trivial
                | some k => rw [hlane _ _ hi]; exact Refine.refl_val _
