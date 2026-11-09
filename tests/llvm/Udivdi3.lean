import CrtUdivdi3
import Kit
import Div

/-! compiler-rt's `__udivdi3`, shift-and-subtract division, for a target with no divide instruction. -/

namespace Llvm.Udivdi3

open IRLean Llvm.Div.W64

variable {n d r q c : BitVec 64} {sub inc unroll niter : BitVec 32}

theorem finish (h : St n d 0 r q c) :
    run CrtUdivdi3._udivdi3.step (.for_end_i (some q) (some c)) = Outcome.ok (some (n / d)) := by
  have hc := h.carry_le
  have hres := h.finish.1
  llvm_step CrtUdivdi3._udivdi3.step
  llvm_step CrtUdivdi3._udivdi3.step
  rw [hres]

theorem epilogue (h : St n d 1 r q c) (hodd : inc.toNat % 2 = 1) :
    run CrtUdivdi3._udivdi3.step (.for_body_i_epil_preheader (some c) (some r) (some q) (some d) (some inc)) =
      Outcome.ok (some (n / d)) := by
  have hc := h.carry_le
  have hodd' : inc &&& 1#32 = 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [Llvm.Div.W32.toNat_and_one, hodd]
    rfl
  llvm_step CrtUdivdi3._udivdi3.step
  exact finish (h.iter.congr rfl (by bv_decide) (by bv_decide))

/-- What comes after the unrolled loop: one more step, if there was an odd number. -/
theorem afterLoop {k : Nat} (h : St n d k r q c) (hk : k = inc.toNat % 2)
    (hsub : sub = inc - 1#32) :
    run CrtUdivdi3._udivdi3.step (.for_end_i_unr_lcssa (some d) (some sub) (some inc) (some q) (some c) (some r)) =
      Outcome.ok (some (n / d)) := by
  llvm_step CrtUdivdi3._udivdi3.step
  apply ite_cases <;> intro hc
  · have hodd : inc.toNat % 2 = 1 := by
      have : inc &&& 1#32 = 1#32 := by subst hsub; simp only [beq_iff_eq] at hc; bv_decide
      have := congrArg BitVec.toNat this
      rw [Llvm.Div.W32.toNat_and_one] at this
      simpa using this
    rw [hodd] at hk
    subst hk
    exact epilogue h hodd
  · have heven : inc.toNat % 2 = 0 := by
      have : inc &&& 1#32 = 0#32 := by subst hsub; simp only [beq_iff_eq] at hc; bv_decide
      have := congrArg BitVec.toNat this
      rw [Llvm.Div.W32.toNat_and_one] at this
      simpa using this
    rw [heven] at hk
    subst hk
    exact finish h

/-- The unrolled loop, with `2 * m + 2` steps to go in it. -/
theorem loop (m : Nat) (hinc : inc.toNat ≤ 64) (hsub : sub = inc - 1#32) (hun : unroll = inc &&& 126#32) :
    ∀ (k : Nat) (r q c : BitVec 64) (niter : BitVec 32), St n d k r q c → k + niter.toNat = inc.toNat →
      unroll.toNat = niter.toNat + 2 * (m + 1) →
      run CrtUdivdi3._udivdi3.step
        (.for_body_i (some c) (some r) (some q) (some niter) (some d) (some sub) (some inc) (some unroll)) =
        Outcome.ok (some (n / d)) := by
  have hunN : unroll.toNat + inc.toNat % 2 = inc.toNat := by
    have e : inc &&& 126#32 = inc - (inc &&& 1#32) := by
      have : inc ≤ 64#32 := by simpa [BitVec.le_def] using hinc
      bv_decide
    subst hun
    rw [e, BitVec.toNat_sub_of_le (by bv_decide)]
    rw [Llvm.Div.W32.toNat_and_one]
    omega
  induction m with
  | zero =>
    intro k r q c niter h hk hn
    have hc := h.carry_le
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h2 := h.iter.iter
    simp only at h2
    llvm_step CrtUdivdi3._udivdi3.step
    have hcond : (niter + 2#32 == unroll) = true := by
      simp only [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [hcond]
    simp only [ite_true]
    exact afterLoop (h2.congr (by bv_decide) rfl (by bv_decide)) (by omega) hsub
  | succ m ih =>
    intro k r q c niter h hk hn
    have hc := h.carry_le
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h2 := h.iter.iter
    simp only at h2
    llvm_step CrtUdivdi3._udivdi3.step
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

/-- `__udivdi3`: for a nonzero divisor, the quotient. Its source says what happens for a zero one is unspecified. -/
theorem correct (n d : BitVec 64) (hd : d ≠ 0#64) :
    CrtUdivdi3._udivdi3 (some n) (some d) = Outcome.ok (some (n / d)) := by
  simp only [CrtUdivdi3._udivdi3, noundef_some]
  -- The loop is marked `llvm.loop.mustprogress`. A run that finishes keeps that promise, so it's set aside.
  refine promised_of_eq ?_
  llvm_step CrtUdivdi3._udivdi3.step
  apply ite_cases <;> intro hbig
  · llvm_step CrtUdivdi3._udivdi3.step
    have hlt : n < d := by bv_decide
    have : n / d = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_udiv, Nat.div_eq_of_lt (show n.toNat < d.toNat from hlt)]
    rw [this]
  · llvm_step CrtUdivdi3._udivdi3.step
    apply ite_cases <;> intro hone
    · llvm_step CrtUdivdi3._udivdi3.step
      have hd1 : d = 1#64 := by bv_decide
      subst hd1
      have : n / 1#64 = n := by
        apply BitVec.eq_of_toNat_eq
        simp
      rw [this]
    · llvm_step CrtUdivdi3._udivdi3.step
      generalize hsub : BitVec.setWidth 32 d.clz - BitVec.setWidth 32 n.clz = sub at *
      generalize hinc : sub + 1#32 = inc at *
      have hsmall : sub ≤ 62#32 := by bv_decide
      have hsubN : sub.toNat ≤ 62 := by simpa [BitVec.le_def] using hsmall
      have hincN : inc.toNat = sub.toNat + 1 := by
        rw [← hinc, BitVec.toNat_add]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have hrest : (63#32 - sub).toNat = 64 - inc.toNat := by
        rw [BitVec.toNat_sub_of_le (by bv_decide), hincN]
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
        omega
      have e1 : n >>> BitVec.setWidth 64 inc = n >>> inc.toNat := by
        show n >>> (BitVec.setWidth 64 inc).toNat = _
        simp only [BitVec.toNat_setWidth, Nat.reducePow]
        rw [Nat.mod_eq_of_lt (by omega)]
      have e2 : n <<< BitVec.setWidth 64 (63#32 - sub) = n <<< (63#32 - sub).toNat := by
        show n <<< (BitVec.setWidth 64 (63#32 - sub)).toNat = _
        simp only [BitVec.toNat_setWidth, Nat.reducePow]
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [e1, e2]
      have hstart : St n d inc.toNat (n >>> inc.toNat) (n <<< (63#32 - sub).toNat) 0#64 := by
        have hrd : n >>> inc.toNat < d := by subst hinc hsub; bv_decide
        have hsafe : d.msb = true → inc = 1#32 ∧ 4611686018427387904#64 ≤ n >>> inc.toNat ∧ n >>> inc.toNat < 9223372036854775808#64 := by
          intro hm
          subst hinc hsub
          bv_decide
        have := St.start (n := n) (d := d) (s := inc.toNat) (by omega) hrd (fun _ hm => by
          obtain ⟨h1, h2, h3⟩ := hsafe hm
          exact ⟨by rw [h1]; rfl, h2, h3⟩)
        rw [← hrest] at this
        exact this
      generalize n >>> inc.toNat = X at hstart ⊢
      generalize n <<< (63#32 - sub).toNat = Y at hstart ⊢
      apply ite_cases <;> intro heq
      · have hone' : inc.toNat = 1 := by
          have : sub = 0#32 := by subst hsub; simp only [beq_iff_eq] at heq; bv_decide
          rw [hincN, this]
          rfl
        rw [hone'] at hstart
        exact epilogue hstart (by omega)
      · llvm_step CrtUdivdi3._udivdi3.step
        have hne : sub ≠ 0#32 := by subst hsub; simp only [beq_iff_eq] at heq; bv_decide
        have hsub1 : 1 ≤ sub.toNat := by
          rcases Nat.eq_zero_or_pos sub.toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
          · exact h0
        have hsubeq : sub = inc - 1#32 := by subst hinc; bv_decide
        have hun : (inc &&& 126#32).toNat + inc.toNat % 2 = inc.toNat := by
          have e : inc &&& 126#32 = inc - (inc &&& 1#32) := by
            have : inc ≤ 64#32 := by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
            bv_decide
          rw [e, BitVec.toNat_sub_of_le (by bv_decide), Llvm.Div.W32.toNat_and_one]
          omega
        exact loop ((inc &&& 126#32).toNat / 2 - 1) (by omega) hsubeq rfl _ _ _ _ _ hstart (by simp)
          (by simp only [BitVec.toNat_ofNat]; omega)

end Llvm.Udivdi3
