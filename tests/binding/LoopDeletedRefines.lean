import Fx.Src
import Fx.Tgt

/-! tests/binding.py's certificate for a loop deleted under a promise: `loop-deletion` removed a loop with no side
effects, whose result nothing used, from a function marked `mustprogress`. The loop counts up from 0 by 2 until it
reaches `n`, so it never ends for an odd `n`, which the promise makes undefined, and for an even `n` it ends. Either
way the function after only does what the one before allows, on every input. Without the promise the source would
never finish on an odd `n`, and the target returns, so this proof would fail there. -/

open IRLean

/-- From an even `i` at or below an even `n`, the loop reaches `n`, and the function returns 0. -/
theorem Fx.reaches (n : BitVec 32) (k : Nat) : ∀ i : BitVec 32, i.toNat ≤ n.toNat → n.toNat - i.toNat = 2 * k →
    run Fx.Src.f.step (.loop_1 (some i) (some n)) = Outcome.ok (some 0#32) := by
  induction k with
  | zero =>
    intro i hle hk
    have : i = n := BitVec.eq_of_toNat_eq (by omega)
    subst this
    rw [run_jump _ (show Fx.Src.f.step _ = jump .exit by simp [Fx.Src.f.step, llvm_val, br])]
    exact run_ret _ rfl
  | succ k ih =>
    intro i hle hk
    have hne : i ≠ n := by rintro rfl; omega
    rw [run_jump _ (show Fx.Src.f.step _ = jump (.loop_1 (some (i + 2#32)) (some n)) by
      simp [Fx.Src.f.step, llvm_val, hne])]
    have h2 : (i + 2#32).toNat = i.toNat + 2 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := n.isLt; omega
    exact ih _ (by omega) (by omega)

/-- For an odd `n`, the loop's `i` stays even, never reaches `n`, and the loop is all the function runs: the
promise is broken. -/
theorem Fx.spins (n : BitVec 32) (hn : n.toNat % 2 = 1) : Fx.Src.f (some n) = Outcome.ub .noProgress := by
  let I : Fx.Src.f.Block → Prop := fun b => ∃ i : BitVec 32, i.toNat % 2 = 0 ∧ b = .loop_1 (some i) (some n)
  have hI : ∀ b, I b → ∃ b', Fx.Src.f.step b = jump b' ∧ (fun _ => true) b' = true ∧ I b' := by
    rintro b ⟨i, hi, rfl⟩
    have hne : i ≠ n := by rintro rfl; omega
    refine ⟨.loop_1 (some (i + 2#32)) (some n), ?_, rfl, i + 2#32, ?_, rfl⟩
    · simp [Fx.Src.f.step, llvm_val, hne]
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h0 : I (.loop_1 (some 0#32) (some n)) := ⟨0#32, rfl, rfl⟩
  have entry : Fx.Src.f.step (.entry (some n)) = jump (.loop_1 (some 0#32) (some n)) := rfl
  simp only [Fx.Src.f, noundef_some]
  rw [run_jump _ entry, run_forever I (fun b hb => let ⟨b', h, _, h'⟩ := hI b hb; ⟨b', h, h'⟩) h0,
    promised_none, runPromised_jump entry]
  exact runPromised_forever I hI h0

theorem Fx.cert : IRLean.Refines Fx.Src.f Fx.Tgt.f := by
  intro n
  cases n with
  | none =>
    simp only [Fx.Src.f, noundef]
    exact Refine.outcome_ub _ _
  | some n =>
    have tgt : Fx.Tgt.f (some n) = Outcome.ok (some 0#32) := by
      simp only [Fx.Tgt.f, noundef_some]
      rw [run_jump _ (show Fx.Tgt.f.step .entry = jump .exit from rfl),
        run_ret Fx.Tgt.f.step (b := .exit) (r := some 0#32) rfl]
      rfl
    rw [tgt]
    by_cases hn : n.toNat % 2 = 0
    · have src : Fx.Src.f (some n) = Outcome.ok (some 0#32) := by
        simp only [Fx.Src.f, noundef_some]
        rw [run_jump _ (show Fx.Src.f.step (.entry (some n)) = jump (.loop_1 (some 0#32) (some n)) from rfl),
          Fx.reaches n (n.toNat / 2) 0#32 (by simp) (by simp; omega)]
        rfl
      rw [src]
      exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)
    · rw [Fx.spins n (by omega)]
      exact Refine.outcome_ub _ _
