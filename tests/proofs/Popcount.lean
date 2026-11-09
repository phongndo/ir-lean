import Real

/-! Clang's `popcount` at `-O2`, proved correct. `tests/proofs.sh` regenerates `Real` from
`tests/real/bi_reverse.c`, so this is about what the compiler produced, not a copy of it. -/

open IRLean Real

/-- The number of set bits, as a formula with no loop. -/
def pop (x : BitVec 32) : BitVec 32 :=
  let a := x - ((x >>> 1) &&& 0x55555555#32)
  let b := (a &&& 0x33333333#32) + ((a >>> 2) &&& 0x33333333#32)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f#32
  let d := c + (c >>> 8)
  (d + (d >>> 16)) &&& 0x3f#32

theorem pop_step (x : BitVec 32) : pop x = (x &&& 1#32) + pop (x >>> 1) := by
  simp only [pop]
  bv_decide

theorem pop_zero : pop 0#32 = 0#32 := by decide

/-- The loop block, from any state: it finishes, with no UB or poison. -/
theorem popcount_loop (n : Nat) : ∀ (x c : BitVec 32), x.toNat = n →
    run popcount.step (.while_body (some c) (some x)) = Outcome.ok (some (c + pop x)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x c hx
    have hstep := pop_step x
    rw [run]
    by_cases h : x >>> 1 = 0#32
    · have e : x &&& 1#32 = pop x := by rw [hstep, h, pop_zero]; simp
      simp [popcount.step, llvm, h]
      rw [run]
      simp [popcount.step, llvm, e]
    · have lt : (x >>> 1).toNat < n := by
        subst hx
        have : x ≠ 0#32 := by rintro rfl; simp at h
        have : 0 < x.toNat := by
          rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) this
          · exact h0
        simp only [BitVec.toNat_ushiftRight]
        omega
      have next := ih _ lt (x >>> 1) (c + (x &&& 1#32)) rfl
      simp [popcount.step, llvm, h]
      simp [llvm] at next
      rw [next, hstep]
      congr 3
      bv_decide

/-- For every input the compiled function returns the bit count: no UB, no poison, always finishes. -/
theorem popcount_correct (x : BitVec 32) :
    popcount (some x) = Outcome.ok (some (pop x)) := by
  simp only [popcount, noundef]
  rw [run]
  by_cases h : x = 0#32
  · subst h
    simp [popcount.step, llvm]
    rw [run]
    simp [popcount.step, llvm, pop_zero]
  · simp [popcount.step, llvm, h]
    have := popcount_loop x.toNat x 0#32 rfl
    simp [llvm] at this
    simp [this]

#print axioms popcount_correct
