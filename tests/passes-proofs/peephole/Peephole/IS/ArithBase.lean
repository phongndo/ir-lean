import IRLean.Int
import IRLean.Refine

/-! # What the arithmetic folds' proofs share about values

Plumbing for `Peephole.IS.Arith*` and `Peephole.Lemmas.Arith`: when a division is defined and what it gives, what a
defined division says about its operands, and what an analysis's answer says about a value. The facts that rewrites
rest on are in `Peephole.Lemmas.Arith`; these are the steps between them and the C++'s conditions. -/

namespace Peephole.IS.Arith

open IRLean

variable {w : Nat}

/-! ### Runs that return -/

theorem ok_none_refines (b : Val w) : Refines (Outcome.ok (none : Val w)) (Outcome.ok b) :=
  (Refine.outcome_ok_ok _ _).2 trivial

theorem ok_refl (a : Val w) : Refines (Outcome.ok a) (Outcome.ok a) :=
  (Refine.outcome_ok_ok _ _).2 (Refine.refl_val a)

theorem ok_refines_of_eq {a b : Val w} (h : b = a) : Refines (Outcome.ok a) (Outcome.ok b) := h ▸ ok_refl a

/-- A value that refines another refines it as a run. -/
theorem ok_refines {a b : Val w} (h : Refines a b) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok a b).2 h

/-- A run that refines poison refines any value: it's poison or undefined. -/
theorem refines_of_refines_ok_none {o : Outcome (Val w)} (h : Refines o (Outcome.ok none)) (b : Val w) :
    Refines o (Outcome.ok b) := by
  match o, h with
  | some (.error (.undefined _)), _ => exact Refine.outcome_ub _ _
  | some (.ok x), ⟨y, hy, hxy⟩ =>
    cases hy
    cases x with
    | none => exact ok_none_refines b
    | some _ => cases hxy

/-! ### When a division is defined, and what it gives -/

theorem udiv_refines_of {x y : BitVec w} {r : Val w} (exact : Bool) (h : y ≠ 0#w → r = some (x / y)) :
    Refines (Val.udiv (some x) (some y) exact) (Outcome.ok r) := by
  simp only [Val.udiv]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · rw [h hy]
    simp only [hy, beq_iff_eq, ite_false]
    split
    · exact ok_none_refines _
    · exact ok_refl _

theorem urem_refines_of {x y : BitVec w} {r : Val w} (h : y ≠ 0#w → r = some (x % y)) :
    Refines (Val.urem (some x) (some y)) (Outcome.ok r) := by
  simp only [Val.urem]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · rw [h hy]
    simp only [hy, beq_iff_eq, ite_false]
    exact ok_refl _

theorem sdiv_refines_of {x y : BitVec w} {r : Val w} (exact : Bool)
    (h : y ≠ 0#w → x.sdivOverflow y = false → r = some (x.sdiv y)) :
    Refines (Val.sdiv (some x) (some y) exact) (Outcome.ok r) := by
  simp only [Val.sdiv, Val.divOverflows]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · by_cases ho : x.sdivOverflow y = true
    · simp [hy, ho]; exact Refine.outcome_ub _ _
    · simp only [Bool.not_eq_true] at ho
      rw [h hy ho]
      simp only [hy, ho, beq_iff_eq, ite_false, Bool.false_eq_true]
      split
      · exact ok_none_refines _
      · exact ok_refl _

theorem srem_refines_of {x y : BitVec w} {r : Val w}
    (h : y ≠ 0#w → x.sdivOverflow y = false → r = some (x.srem y)) :
    Refines (Val.srem (some x) (some y)) (Outcome.ok r) := by
  simp only [Val.srem, Val.divOverflows]
  by_cases hy : y = 0#w
  · simp [hy]; exact Refine.outcome_ub _ _
  · by_cases ho : x.sdivOverflow y = true
    · simp [hy, ho]; exact Refine.outcome_ub _ _
    · simp only [Bool.not_eq_true] at ho
      rw [h hy ho]
      simp only [hy, ho, beq_iff_eq, ite_false, Bool.false_eq_true]
      exact ok_refl _

/-! ### A poison operand -/

theorem udiv_none_left (b : Val w) (exact : Bool) (r : Val w) : Refines (Val.udiv none b exact) (Outcome.ok r) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · simp only [Val.udiv, hy, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · simp only [Val.udiv, beq_iff_eq, hy, ite_false]; exact ok_none_refines _

theorem urem_none_left (b : Val w) (r : Val w) : Refines (Val.urem none b) (Outcome.ok r) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · simp only [Val.urem, hy, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · simp only [Val.urem, beq_iff_eq, hy, ite_false]; exact ok_none_refines _

theorem sdiv_none_left (b : Val w) (exact : Bool) (r : Val w) : Refines (Val.sdiv none b exact) (Outcome.ok r) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · simp only [Val.sdiv, hy, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · have h0 : (y == 0#w) = false := by simpa using hy
      simp only [Val.sdiv, h0, Bool.false_eq_true, ite_false]
      split
      · exact Refine.outcome_ub _ _
      · exact ok_none_refines _

theorem srem_none_left (b : Val w) (r : Val w) : Refines (Val.srem none b) (Outcome.ok r) := by
  cases b with
  | none => exact Refine.outcome_ub _ _
  | some y =>
    by_cases hy : y = 0#w
    · simp only [Val.srem, hy, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _
    · have h0 : (y == 0#w) = false := by simpa using hy
      simp only [Val.srem, h0, Bool.false_eq_true, ite_false]
      split
      · exact Refine.outcome_ub _ _
      · exact ok_none_refines _

theorem udiv_none_right (a : Val w) (exact : Bool) (r : Val w) : Refines (Val.udiv a none exact) (Outcome.ok r) :=
  Refine.outcome_ub _ _

theorem urem_none_right (a : Val w) (r : Val w) : Refines (Val.urem a none) (Outcome.ok r) :=
  Refine.outcome_ub _ _

theorem sdiv_none_right (a : Val w) (exact : Bool) (r : Val w) : Refines (Val.sdiv a none exact) (Outcome.ok r) :=
  Refine.outcome_ub _ _

theorem srem_none_right (a : Val w) (r : Val w) : Refines (Val.srem a none) (Outcome.ok r) :=
  Refine.outcome_ub _ _

theorem udiv_zero_right (a : Val w) (exact : Bool) (r : Val w) :
    Refines (Val.udiv a (some 0#w) exact) (Outcome.ok r) := by
  simp only [Val.udiv, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _

theorem urem_zero_right (a : Val w) (r : Val w) : Refines (Val.urem a (some 0#w)) (Outcome.ok r) := by
  simp only [Val.urem, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _

theorem sdiv_zero_right (a : Val w) (exact : Bool) (r : Val w) :
    Refines (Val.sdiv a (some 0#w) exact) (Outcome.ok r) := by
  simp only [Val.sdiv, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _

theorem srem_zero_right (a : Val w) (r : Val w) : Refines (Val.srem a (some 0#w)) (Outcome.ok r) := by
  simp only [Val.srem, beq_self_eq_true, ite_true]; exact Refine.outcome_ub _ _

/-! ### What a division that ran says about its operands -/

theorem udiv_ok {a b x : Val w} {exact : Bool} (h : Val.udiv a b exact = Outcome.ok x) :
    ∃ y, b = some y ∧ y ≠ 0#w ∧
      (x = none ∨ ∃ p, a = some p ∧ (exact = true → p % y = 0#w) ∧ x = some (p / y)) := by
  cases b with
  | none => simp [Val.udiv, Outcome.ub, Outcome.ok] at h
  | some y =>
    by_cases hy : y = 0#w
    · simp [Val.udiv, hy, Outcome.ub, Outcome.ok] at h
    · refine ⟨y, rfl, hy, ?_⟩
      cases a with
      | none =>
        simp only [Val.udiv, beq_iff_eq, hy, ite_false, Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
        exact .inl h.symm
      | some p =>
        simp only [Val.udiv, beq_iff_eq, hy, ite_false, Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
        by_cases he : exact = true ∧ p % y ≠ 0#w
        · left; rw [← h]; simp [he.1, he.2]
        · right
          refine ⟨p, rfl, fun hex => ?_, ?_⟩
          · exact Classical.byContradiction fun hn => he ⟨hex, hn⟩
          · rw [← h]
            have : (exact && p % y != 0#w) = false := by
              cases exact <;> simp_all
            simp [this]

theorem urem_ok {a b x : Val w} (h : Val.urem a b = Outcome.ok x) :
    ∃ y, b = some y ∧ y ≠ 0#w ∧ (x = none ∨ ∃ p, a = some p ∧ x = some (p % y)) := by
  cases b with
  | none => simp [Val.urem, Outcome.ub, Outcome.ok] at h
  | some y =>
    by_cases hy : y = 0#w
    · simp [Val.urem, hy, Outcome.ub, Outcome.ok] at h
    · refine ⟨y, rfl, hy, ?_⟩
      cases a with
      | none =>
        simp only [Val.urem, beq_iff_eq, hy, ite_false, Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
        exact .inl h.symm
      | some p =>
        simp only [Val.urem, beq_iff_eq, hy, ite_false, Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
        exact .inr ⟨p, rfl, h.symm⟩

theorem sdiv_ok {a b x : Val w} {exact : Bool} (h : Val.sdiv a b exact = Outcome.ok x) :
    ∃ y, b = some y ∧ y ≠ 0#w ∧ (x = none ∨ ∃ p, a = some p ∧ p.sdivOverflow y = false ∧
      (exact = true → p.srem y = 0#w) ∧ x = some (p.sdiv y)) := by
  cases b with
  | none => simp [Val.sdiv, Outcome.ub, Outcome.ok] at h
  | some y =>
    by_cases hy : y = 0#w
    · simp [Val.sdiv, hy, Outcome.ub, Outcome.ok] at h
    · refine ⟨y, rfl, hy, ?_⟩
      have h0 : (y == 0#w) = false := by simpa using hy
      cases a with
      | none =>
        simp only [Val.sdiv, h0, Bool.false_eq_true, ite_false] at h
        split at h
        · simp [Outcome.ub, Outcome.ok] at h
        · simp only [Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
          exact .inl h.symm
      | some p =>
        simp only [Val.sdiv, h0, Bool.false_eq_true, ite_false] at h
        split at h
        · simp [Outcome.ub, Outcome.ok] at h
        · next ho =>
          simp only [Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
          simp only [Val.divOverflows, Bool.not_eq_true] at ho
          by_cases he : exact = true ∧ p.srem y ≠ 0#w
          · left; rw [← h]; simp [he.1, he.2]
          · right
            refine ⟨p, rfl, ho, fun hex => ?_, ?_⟩
            · exact Classical.byContradiction fun hn => he ⟨hex, hn⟩
            · rw [← h]
              have : (exact && p.srem y != 0#w) = false := by
                cases exact <;> simp_all
              simp [this]

theorem srem_ok {a b x : Val w} (h : Val.srem a b = Outcome.ok x) :
    ∃ y, b = some y ∧ y ≠ 0#w ∧ (x = none ∨ ∃ p, a = some p ∧ p.sdivOverflow y = false ∧ x = some (p.srem y)) := by
  cases b with
  | none => simp [Val.srem, Outcome.ub, Outcome.ok] at h
  | some y =>
    by_cases hy : y = 0#w
    · simp [Val.srem, hy, Outcome.ub, Outcome.ok] at h
    · refine ⟨y, rfl, hy, ?_⟩
      have h0 : (y == 0#w) = false := by simpa using hy
      cases a with
      | none =>
        simp only [Val.srem, h0, Bool.false_eq_true, ite_false] at h
        split at h
        · simp [Outcome.ub, Outcome.ok] at h
        · simp only [Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
          exact .inl h.symm
      | some p =>
        simp only [Val.srem, h0, Bool.false_eq_true, ite_false] at h
        split at h
        · simp [Outcome.ub, Outcome.ok] at h
        · next ho =>
          simp only [Outcome.ok, Option.some.injEq, Except.ok.injEq] at h
          simp only [Val.divOverflows, Bool.not_eq_true] at ho
          exact .inr ⟨p, rfl, ho, h.symm⟩

/-! ### Signed division through `toInt` -/

theorem toInt_ne_zero {y : BitVec w} (hy : y ≠ 0#w) : y.toInt ≠ 0 := by
  intro h
  exact hy (BitVec.eq_of_toInt_eq (by rw [h, BitVec.toInt_zero]))

theorem pos_of_ne_zero {y : BitVec w} (hy : y ≠ 0#w) : 0 < w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact absurd BitVec.of_length_zero hy
  · exact hw

/-- The signed quotient as an integer, where it doesn't overflow. -/
theorem toInt_sdiv_of {x y : BitVec w} (hy : y ≠ 0#w) (ho : x.sdivOverflow y = false) :
    (x.sdiv y).toInt = x.toInt.tdiv y.toInt := by
  apply BitVec.toInt_sdiv_of_ne_or_ne
  rw [BitVec.sdivOverflow_eq] at ho
  have hw := pos_of_ne_zero hy
  simp only [hw, decide_true, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ho
  rw [BitVec.neg_one_eq_allOnes]
  exact ho

/-- A value whose `toInt` is `-1` is all ones. -/
theorem eq_allOnes_of_toInt {x : BitVec w} (hw : 0 < w) (h : x.toInt = -1) : x = BitVec.allOnes w :=
  BitVec.eq_of_toInt_eq (by rw [h, BitVec.toInt_allOnes]; simp [hw])

/-- The signed range, as `omega` reads it. -/
theorem toInt_range (x : BitVec w) : -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

/-! ### What an analysis's answer says about a value -/

/-- A value with no bit where `kz` has one is at most `~kz`: `KnownBits::getMaxValue`. -/
theorem toNat_le_not_of_and_eq_zero {x kz : BitVec w} (h : x &&& kz = 0#w) : x.toNat ≤ (~~~kz).toNat := by
  have hx : x = x &&& ~~~kz := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases hxi : x.getLsbD i <;> cases hk : kz.getLsbD i <;> simp_all
  rw [hx, BitVec.toNat_and]
  exact Nat.and_le_right

/-- Known zeros in every bit: the value is `0`. `KnownBits::isZero`. -/
theorem eq_zero_of_and_allOnes {x : BitVec w} (h : x &&& BitVec.allOnes w = 0#w) : x = 0#w := by
  rwa [BitVec.and_allOnes] at h

/-- Known zeros in every bit but the lowest: the value is `0` or `1`. `KnownBits::countMinLeadingZeros`, which is the
known zeros' leading ones, is `w - 1`. -/
theorem le_one_of_clz_not {y kz : BitVec w} (h : y &&& kz = 0#w) (hc : (~~~kz).clz.toNat = w - 1) :
    y = 0#w ∨ y = 1#w := by
  have h1 := toNat_le_not_of_and_eq_zero h
  have h2 := BitVec.toNat_lt_two_pow_sub_clz (x := ~~~kz)
  rw [hc] at h2
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact .inl BitVec.of_length_zero
  · have : w - (w - 1) = 1 := by omega
    rw [this] at h2
    have hy : y.toNat ≤ 1 := by omega
    rcases (by omega : y.toNat = 0 ∨ y.toNat = 1) with h0 | h0
    · left; apply BitVec.eq_of_toNat_eq; simp [h0]
    · right; apply BitVec.eq_of_toNat_eq; rw [h0, BitVec.toNat_one hw]

/-- Known zeros in every bit but the sign bit: the value is `0` or the signed minimum.
`KnownBits.Zero.isMaxSignedValue()`. -/
theorem eq_zero_or_intMin_of_and_intMax {y : BitVec w} (h : y &&& BitVec.intMax w = 0#w) :
    y = 0#w ∨ y = BitVec.intMin w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact .inl BitVec.of_length_zero
  have hm : (BitVec.intMax w).toNat = 2 ^ (w - 1) - 1 := BitVec.toNat_intMax
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.zero_mod] at hn
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hlt := y.isLt
  obtain ⟨q, hq⟩ : 2 ^ (w - 1) ∣ y.toNat := Nat.dvd_of_mod_eq_zero hn
  have hp : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
  have : q < 2 := by
    rw [hq, h2, Nat.mul_comm 2] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · left; apply BitVec.eq_of_toNat_eq; simp [hq]
  · right; apply BitVec.eq_of_toNat_eq; rw [hq, BitVec.toNat_intMin_of_pos hw, Nat.mul_one]

/-- A value with every bit `ko` has, has the lowest of them: `KnownBits.One.countr_zero()`. -/
theorem getLsbD_ctz_of_and {x ko : BitVec w} (h : x &&& ko = ko) (hk : ko.ctz.toNat < w) :
    x.getLsbD ko.ctz.toNat = true := by
  have hne : ko ≠ 0#w := by
    apply BitVec.ctz_lt_iff_ne_zero.1
    rw [BitVec.lt_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
    exact hk
  have hb := BitVec.getLsbD_true_ctz_of_ne_zero hne
  have := congrArg (·.getLsbD ko.ctz.toNat) h
  simp only [BitVec.getLsbD_and, hb, Bool.and_true] at this
  exact this

/-- The bits below a value's trailing zeros are zero, so `2 ^ ctz` divides it. -/
theorem two_pow_ctz_dvd (y : BitVec w) : 2 ^ y.ctz.toNat ∣ y.toNat := by
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < y.ctz.toNat
  · simp only [hi, decide_true, Bool.true_and]
    have := BitVec.getLsbD_false_of_lt_ctz (x := y) hi
    simpa [BitVec.getLsbD] using this
  · simp [hi]

theorem ctz_le (y : BitVec w) : y.ctz.toNat ≤ w := by
  rw [BitVec.ctz_eq_reverse_clz]
  have := BitVec.clz_le (x := y.reverse)
  simpa [BitVec.le_def] using this

end Peephole.IS.Arith
