import CrtUmodsi3
import Kit
import Div

/-! compiler-rt's `__umodsi3`, the remainder from shift-and-subtract division, for a target with no divide instruction. -/

namespace Llvm.Umodsi3

open IRLean Llvm.Div.W32

variable {n d r q c sub inc unroll niter : BitVec 32}

theorem exit (h : St n d 0 r q c) :
    run CrtUmodsi3._umodsi3.step (._umodXi3_exit (some r)) = Outcome.ok (some (n % d)) := by
  have hres := h.finish.2
  llvm_step CrtUmodsi3._umodsi3.step
  rw [hres]

theorem epilogue (h : St n d 1 r q c) (hodd : inc.toNat % 2 = 1) :
    run CrtUmodsi3._umodsi3.step (.for_body_i_epil_preheader (some r) (some q) (some d) (some inc)) =
      Outcome.ok (some (n % d)) := by
  have hodd' : inc &&& 1#32 = 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_and_one, hodd]
    rfl
  llvm_step CrtUmodsi3._umodsi3.step
  exact exit (h.iter.congr (by bv_decide) rfl rfl)

/-- What comes after the unrolled loop: one more step, if there was an odd number. -/
theorem afterLoop {k : Nat} (h : St n d k r q c) (hk : k = inc.toNat % 2)
    (hsub : sub = inc - 1#32) :
    run CrtUmodsi3._umodsi3.step (._umodXi3_exit_loopexit_unr_lcssa (some d) (some sub) (some inc) (some q) (some r)) =
      Outcome.ok (some (n % d)) := by
  llvm_step CrtUmodsi3._umodsi3.step
  apply ite_cases <;> intro hc
  · have hodd : inc.toNat % 2 = 1 := by
      have : inc &&& 1#32 = 1#32 := by subst hsub; simp only [beq_iff_eq] at hc; bv_decide
      have := congrArg BitVec.toNat this
      rw [toNat_and_one] at this
      simpa using this
    rw [hodd] at hk
    subst hk
    exact epilogue h hodd
  · have heven : inc.toNat % 2 = 0 := by
      have : inc &&& 1#32 = 0#32 := by subst hsub; simp only [beq_iff_eq] at hc; bv_decide
      have := congrArg BitVec.toNat this
      rw [toNat_and_one] at this
      simpa using this
    rw [heven] at hk
    subst hk
    exact exit h

/-- The unrolled loop, with `2 * m + 2` steps to go in it. -/
theorem loop (m : Nat) (hinc : inc.toNat ≤ 32) (hsub : sub = inc - 1#32) (hun : unroll = inc &&& 62#32) :
    ∀ (k : Nat) (r q c niter : BitVec 32), St n d k r q c → k + niter.toNat = inc.toNat →
      unroll.toNat = niter.toNat + 2 * (m + 1) →
      run CrtUmodsi3._umodsi3.step
        (.for_body_i (some c) (some r) (some q) (some niter) (some d) (some sub) (some inc) (some unroll)) =
        Outcome.ok (some (n % d)) := by
  have hunN : unroll.toNat + inc.toNat % 2 = inc.toNat := by
    have e : inc &&& 62#32 = inc - (inc &&& 1#32) := by
      have : inc ≤ 32#32 := by simpa [BitVec.le_def] using hinc
      bv_decide
    subst hun
    rw [e, BitVec.toNat_sub_of_le (by bv_decide)]
    rw [toNat_and_one]
    omega
  induction m with
  | zero =>
    intro k r q c niter h hk hn
    have hc := h.carry_le
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h2 := h.iter.iter
    simp only at h2
    llvm_step CrtUmodsi3._umodsi3.step
    have hcond : (niter + 2#32 == unroll) = true := by
      simp only [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [hcond]
    simp only [ite_true]
    exact afterLoop (h2.congr (by bv_decide) rfl rfl) (by omega) hsub
  | succ m ih =>
    intro k r q c niter h hk hn
    have hc := h.carry_le
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h2 := h.iter.iter
    simp only at h2
    llvm_step CrtUmodsi3._umodsi3.step
    have hstep : (niter + 2#32).toNat = niter.toNat + 2 := by
      rw [BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    have hcond : (niter + 2#32 == unroll) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      rw [← e] at hn
      omega
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    exact ih k' _ _ _ _ (h2.congr (by bv_decide) rfl (by bv_decide)) (by omega) (by omega)

/-- `__umodsi3`: for a nonzero divisor, the remainder. Its source says what happens for a zero one is unspecified. -/
theorem correct (n d : BitVec 32) (hd : d ≠ 0#32) :
    CrtUmodsi3._umodsi3 (some n) (some d) = Outcome.ok (some (n % d)) := by
  simp only [CrtUmodsi3._umodsi3, noundef_some]
  llvm_step CrtUmodsi3._umodsi3.step
  apply ite_cases <;> intro hbig
  · llvm_step CrtUmodsi3._umodsi3.step
    have hlt : n < d := by bv_decide
    have : n % d = n := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_umod, Nat.mod_eq_of_lt (show n.toNat < d.toNat from hlt)]
    rw [this]
  · llvm_step CrtUmodsi3._umodsi3.step
    apply ite_cases <;> intro hone
    · llvm_step CrtUmodsi3._umodsi3.step
      have hd1 : d = 1#32 := by bv_decide
      subst hd1
      have : n % 1#32 = 0#32 := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [this]
    · llvm_step CrtUmodsi3._umodsi3.step
      generalize hsub : d.clz - n.clz = sub at *
      generalize hinc : sub + 1#32 = inc at *
      have hsmall : sub ≤ 30#32 := by bv_decide
      have hsubN : sub.toNat ≤ 30 := by simpa [BitVec.le_def] using hsmall
      have hincN : inc.toNat = sub.toNat + 1 := by
        rw [← hinc, BitVec.toNat_add]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hrest : (31#32 - sub).toNat = 32 - inc.toNat := by
        rw [BitVec.toNat_sub_of_le (by bv_decide), hincN]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hstart : St n d inc.toNat (n >>> inc) (n <<< (31#32 - sub)) 0#32 := by
        have hrd : n >>> inc < d := by subst hinc hsub; bv_decide
        have hsafe : d.msb = true → inc = 1#32 ∧ 1073741824#32 ≤ n >>> inc ∧ n >>> inc < 2147483648#32 := by
          intro hm
          subst hinc hsub
          bv_decide
        have := St.start (n := n) (d := d) (s := inc.toNat) (by omega) hrd (fun _ hm => by
          obtain ⟨h1, h2, h3⟩ := hsafe hm
          exact ⟨by rw [h1]; rfl, h2, h3⟩)
        rw [← hrest] at this
        exact this
      apply ite_cases <;> intro heq
      · have hone' : inc.toNat = 1 := by
          have : sub = 0#32 := by subst hsub; simp only [beq_iff_eq] at heq; bv_decide
          rw [hincN, this]
          rfl
        rw [hone'] at hstart
        exact epilogue hstart (by omega)
      · llvm_step CrtUmodsi3._umodsi3.step
        have hne : sub ≠ 0#32 := by subst hsub; simp only [beq_iff_eq] at heq; bv_decide
        have hsub1 : 1 ≤ sub.toNat := by
          rcases Nat.eq_zero_or_pos sub.toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
          · exact h0
        have hsubeq : sub = inc - 1#32 := by subst hinc; bv_decide
        have hun : (inc &&& 62#32).toNat + inc.toNat % 2 = inc.toNat := by
          have e : inc &&& 62#32 = inc - (inc &&& 1#32) := by
            have : inc ≤ 32#32 := by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
            bv_decide
          rw [e, BitVec.toNat_sub_of_le (by bv_decide), toNat_and_one]
          omega
        exact loop ((inc &&& 62#32).toNat / 2 - 1) (by omega) hsubeq rfl _ _ _ _ _ hstart (by simp)
          (by simp only [BitVec.toNat_ofNat]; omega)

end Llvm.Umodsi3
