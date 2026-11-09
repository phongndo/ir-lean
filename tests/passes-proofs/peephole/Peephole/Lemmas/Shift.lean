import IRLean.Int
import IRLean.Refine
import IRLean.Generic.BitVec

/-! # Facts about shifts and integer casts, at every width, that InstSimplify's rewrites of them rest on

Each is about values, not about LLVM's code: a candidate for the lemma store, which any proof about a shift or a cast
can use. The rewrite each one was cut from is named in its docstring. A shift by `w` or more is poison
(`Val.shiftOk`), and most of `simplifyShift`'s rewrites rest on that: an amount that isn't 0 is either out of range,
so the shift is poison, or shifts a bit out that a flag forbids.

For each hypothesis, `LemmaStore.Counter.<lemma>.drop_<hypothesis>` at the end gives an input where the lemma without
it fails, and `.sat` one where they all hold, as `store/LemmaStore/Counter/Generic.lean` has them. -/

namespace Peephole.Lemmas

open IRLean

variable {w : Nat}

/-- A value that's poison when `p` holds, and `v` otherwise, is one or the other. -/
private theorem ite_none_or {p : Prop} {_ : Decidable p} {v : Val w} :
    (if p then none else v) = none ∨ v = (if p then none else v) := by
  by_cases h : p <;> simp [h]

private theorem refines_of_eq_or_none {a b : Val w} (h : a = none ∨ b = a) : Refines a b :=
  (Refine.val_iff a b).2 h

/-! ### Out of range -/

/-- `shl` by `w` or more is poison, whatever the flags. `IS.simplifyShift.L1326`, `L1344` and `L1350`, and `L1322`
for a `sext` of `true`, which is all ones. -/
theorem shl_of_le_toNat (a : Val w) {y : BitVec w} (h : w ≤ y.toNat) (nuw nsw : Bool) :
    Val.shl a (some y) nuw nsw = none := by
  cases a <;> simp [Val.shl, Generic.shiftOk_iff, Nat.not_lt.2 h]

/-- `lshr` by `w` or more is poison, with or without `exact`. -/
theorem lshr_of_le_toNat (a : Val w) {y : BitVec w} (h : w ≤ y.toNat) (exact : Bool) :
    Val.lshr a (some y) exact = none := by
  cases a <;> simp [Val.lshr, Generic.shiftOk_iff, Nat.not_lt.2 h]

/-- `ashr` by `w` or more is poison, with or without `exact`. -/
theorem ashr_of_le_toNat (a : Val w) {y : BitVec w} (h : w ≤ y.toNat) (exact : Bool) :
    Val.ashr a (some y) exact = none := by
  cases a <;> simp [Val.ashr, Generic.shiftOk_iff, Nat.not_lt.2 h]

/-! ### Shifting zero -/

/-- `shl 0, y` refines 0, whatever the flags: it's 0, or poison. `IS.simplifyShift.L1314`. -/
theorem shl_zero_left_refines (b : Val w) (nuw nsw : Bool) : Refines (Val.shl (some 0#w) b nuw nsw) (some 0#w) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.shl, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq', BitVec.zero_shiftLeft,
      BitVec.zero_ushiftRight, BitVec.zero_sshiftRight, bne_self_eq_false, Bool.and_false]
    split <;> simp

/-- `lshr 0, y` refines 0, with or without `exact`. `IS.simplifyShift.L1314`. -/
theorem lshr_zero_left_refines (b : Val w) (exact : Bool) : Refines (Val.lshr (some 0#w) b exact) (some 0#w) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.lshr, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.zero_shiftLeft, BitVec.zero_ushiftRight,
      bne_self_eq_false, Bool.and_false]
    split <;> simp

/-- `ashr 0, y` refines 0, with or without `exact`. `IS.simplifyShift.L1314`. -/
theorem ashr_zero_left_refines (b : Val w) (exact : Bool) : Refines (Val.ashr (some 0#w) b exact) (some 0#w) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.ashr, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', BitVec.zero_shiftLeft, BitVec.zero_sshiftRight,
      bne_self_eq_false, Bool.and_false]
    split <;> simp

/-! ### Shifting a value by itself -/

/-- A value is less than 2 to its own power, so shifting it right by itself leaves 0. -/
theorem ushiftRight_toNat_self (x : BitVec w) : x >>> x.toNat = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- `lshr x, x` refines 0, with or without `exact`. `IS.simplifyRightShift.L1381`. -/
theorem lshr_self_refines (a : Val w) (exact : Bool) : Refines (Val.lshr a a exact) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    simp only [Val.lshr, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', ushiftRight_toNat_self, BitVec.zero_shiftLeft]
    split
    · simp
    · split <;> simp

/-- An amount in range has its sign bit clear: `w ≤ 2 ^ (w - 1)`. -/
theorem msb_eq_false_of_toNat_lt {x : BitVec w} (h : x.toNat < w) : x.msb = false := by
  rw [BitVec.msb_eq_decide]
  have : w - 1 < 2 ^ (w - 1) := Nat.lt_two_pow_self
  simp only [decide_eq_false_iff_not, Nat.not_le]
  omega

/-- `ashr x, x` refines 0, with or without `exact`: an amount in range isn't negative. `IS.simplifyRightShift.L1381`. -/
theorem ashr_self_refines (a : Val w) (exact : Bool) : Refines (Val.ashr a a exact) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    by_cases hy : Val.shiftOk x = true
    · have hlt : x.toNat < w := by simpa [Generic.shiftOk_iff] using hy
      have hx : x.sshiftRight x.toNat = 0#w := by
        rw [BitVec.sshiftRight_eq_of_msb_false (msb_eq_false_of_toNat_lt hlt), ushiftRight_toNat_self]
      simp only [Val.ashr, hy, BitVec.sshiftRight_eq', BitVec.shiftLeft_eq', hx, BitVec.zero_shiftLeft]
      split
      · simp
      · split <;> simp
    · simp [Val.ashr, hy]

/-! ### Flags that let nothing through but a shift by 0 -/

/-- A shift left by at least one clears bit 0. -/
theorem getLsbD_zero_shiftLeft {x : BitVec w} {n : Nat} (hn : n ≠ 0) : (x <<< n).getLsbD 0 = false := by
  simp [BitVec.getLsbD_shiftLeft]; omega

/-- `lshr exact x, y` refines `x` if bit 0 of `x` is set: shifting by more than 0 drops it, which `exact` makes
poison. `IS.simplifyRightShift.L1393`. -/
theorem lshr_exact_of_getLsbD_refines (x : BitVec w) (hx : x.getLsbD 0 = true) (b : Val w) :
    Refines (Val.lshr (some x) b true) (some x) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.lshr, Bool.true_and, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next he =>
        right
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at he
        have h0 : y.toNat = 0 := by
          false_or_by_contra
          have := congrArg (·.getLsbD 0) he
          simp only [getLsbD_zero_shiftLeft (by assumption), hx] at this
          cases this
        rw [h0, BitVec.ushiftRight_zero]

/-- `ashr exact x, y` refines `x` if bit 0 of `x` is set. `IS.simplifyRightShift.L1393`. -/
theorem ashr_exact_of_getLsbD_refines (x : BitVec w) (hx : x.getLsbD 0 = true) (b : Val w) :
    Refines (Val.ashr (some x) b true) (some x) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.ashr, Bool.true_and, BitVec.sshiftRight_eq', BitVec.shiftLeft_eq']
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next he =>
        right
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at he
        have h0 : y.toNat = 0 := by
          false_or_by_contra
          have := congrArg (·.getLsbD 0) he
          simp only [getLsbD_zero_shiftLeft (by assumption), hx] at this
          cases this
        rw [h0, BitVec.sshiftRight_zero]

/-- `shl nuw x, y` refines `x` if the sign bit of `x` is set: shifting by more than 0 drops it, which `nuw` makes
poison. `IS.simplifyShlInst.L1421`. -/
theorem shl_nuw_of_msb_refines (x : BitVec w) (hx : x.msb = true) (b : Val w) (nsw : Bool) :
    Refines (Val.shl (some x) b true nsw) (some x) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.shl, Bool.true_and, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.sshiftRight_eq']
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next he =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at he
        have h0 : y.toNat = 0 := by
          false_or_by_contra
          have := congrArg BitVec.msb he
          simp only [BitVec.msb_ushiftRight, hx] at this
          simp_all
        simp only [h0, BitVec.shiftLeft_zero, BitVec.sshiftRight_zero, bne_self_eq_false, Bool.and_false]
        simp

/-- `shl nuw nsw x, w - 1` refines 0 at a width over 1: `nuw` leaves `x` only 0 or 1, and `nsw` rules out 1, which
would shift into the sign bit. `IS.simplifyShlInst.L1430`. -/
theorem shl_nuw_nsw_of_toNat_eq_refines (a : Val w) {c : BitVec w} (hc : c.toNat = w - 1) (hw : 1 < w) :
    Refines (Val.shl a (some c) true true) (some 0#w) := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    simp only [Val.shl, Bool.true_and, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', hc]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next hu =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hu
        have hlt := (Generic.shl_lshr_eq_iff x (k := w - 1) (by omega)).1 hu
        have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        have hx2 : x.toNat < 2 := by
          rw [hpow] at hlt
          exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).1 hlt
        split
        · exact Or.inl rfl
        · next hs =>
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hs
          right
          rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
          · have : x = 0#w := BitVec.eq_of_toNat_eq (by simp [h])
            subst this
            simp
          · exfalso
            have := (Generic.shl_sshr_eq_iff x (k := w - 1) (by omega)).1 hs
            have hi : x.toInt = 1 := by
              rw [BitVec.toInt_eq_toNat_cond, h]
              have h2 : 2 * 1 < 2 ^ w := by
                simpa using Nat.pow_lt_pow_right (a := 2) (by decide) hw
              simp [h2]
            have h1 := this.2
            rw [hi, Int.one_mul] at h1
            exact Int.lt_irrefl _ h1

/-! ### Shifting there and back -/

/-- `lshr (or (shl nuw x, c), y), c` refines `x` if `y` is under `2 ^ c`, whatever the other flags: `y` is in the low
bits the `shl` cleared, and `nuw` says the shift back loses nothing. `IS.simplifyLShrInst.L1466`. -/
theorem lshr_or_shl_nuw_refines (a : Val w) {y c : BitVec w} (hy : y.toNat < 2 ^ c.toNat) (nsw disjoint exact : Bool) :
    Refines (Val.lshr (Val.or (Val.shl a (some c) true nsw) (some y) disjoint) (some c) exact) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    have hy0 : y >>> c = 0#w := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hy]
    simp only [Val.shl, Bool.true_and]
    split
    · simp [Val.or, Val.lshr]
    · next hc =>
      split
      · simp [Val.or, Val.lshr]
      · next hu =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hu
        have hr : (x <<< c ||| y) >>> c = x := by
          rw [BitVec.ushiftRight_eq', BitVec.ushiftRight_or_distrib, ← BitVec.ushiftRight_eq',
            ← BitVec.ushiftRight_eq', hu, hy0, BitVec.or_zero]
        split
        · simp [Val.or, Val.lshr]
        · simp only [Val.or]
          split
          · simp [Val.lshr]
          · simp only [Val.lshr, hc, hr, Bool.false_eq_true, ↓reduceIte]
            exact ite_none_or

/-! ### All ones, and values that are all sign bits -/

/-- All ones shifted right arithmetically is all ones. -/
theorem allOnes_sshiftRight (n : Nat) : (BitVec.allOnes w).sshiftRight n = BitVec.allOnes w := by
  ext i hi
  simp [BitVec.getElem_sshiftRight, BitVec.msb_allOnes, show 0 < w by omega]

/-- `ashr -1, y` refines -1, with or without `exact`. `IS.simplifyAShrInst.L1490`. -/
theorem ashr_allOnes_refines (b : Val w) (exact : Bool) :
    Refines (Val.ashr (some (BitVec.allOnes w)) b exact) (some (BitVec.allOnes w)) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.ashr, BitVec.sshiftRight_eq', allOnes_sshiftRight]
    split
    · exact Or.inl rfl
    · split <;> simp

/-- `ashr (shl -1, y), y` refines -1, whatever the flags: the shift left keeps the sign bit, which the shift back
copies into the bits it cleared. `IS.simplifyAShrInst.L1490`. -/
theorem ashr_shl_allOnes_refines (b : Val w) (nuw nsw exact : Bool) :
    Refines (Val.ashr (Val.shl (some (BitVec.allOnes w)) b nuw nsw) b exact) (some (BitVec.allOnes w)) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.shl]
    split
    · exact Or.inl rfl
    · next hy =>
      have hlt : y.toNat < w := by simpa [Generic.shiftOk_iff] using hy
      have hs : (BitVec.allOnes w <<< y.toNat).sshiftRight y.toNat = BitVec.allOnes w := by
        ext i hi
        simp only [BitVec.getElem_sshiftRight, BitVec.getElem_allOnes]
        split
        · simp [BitVec.getElem_shiftLeft]
        · simp [BitVec.msb_shiftLeft, BitVec.getMsbD_allOnes, hlt]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · simp only [Val.ashr, hy, BitVec.sshiftRight_eq', BitVec.shiftLeft_eq', hs]
          split <;> simp

/-- A value whose every bit, from the top, is its sign bit has each bit, from the bottom, its sign bit too. -/
theorem getLsbD_eq_msb {x : BitVec w} (hx : ∀ i, i < w → x.getMsbD i = x.msb) {i : Nat} (hi : i < w) :
    x.getLsbD i = x.msb := by
  have := hx (w - 1 - i) (by omega)
  rw [BitVec.getMsbD_eq_getLsbD] at this
  simp only [show w - 1 - i < w by omega, decide_true, Bool.true_and, show w - 1 - (w - 1 - i) = i by omega] at this
  exact this

/-- A value that's all sign bits, 0 or -1, is its own arithmetic shift. -/
theorem sshiftRight_of_getMsbD (x : BitVec w) (hx : ∀ i, i < w → x.getMsbD i = x.msb) (n : Nat) :
    x.sshiftRight n = x := by
  ext i hi
  rw [BitVec.getElem_sshiftRight]
  split
  · rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, getLsbD_eq_msb hx (by omega), getLsbD_eq_msb hx hi]
  · rw [← BitVec.getLsbD_eq_getElem, getLsbD_eq_msb hx hi]

/-- `ashr x, y` refines `x` if every bit of `x` is its sign bit, with or without `exact`. `IS.simplifyAShrInst.L1500`,
where `ComputeNumSignBits(x)` is the width. -/
theorem ashr_of_getMsbD_refines (x : BitVec w) (hx : ∀ i, i < w → x.getMsbD i = x.msb) (b : Val w) (exact : Bool) :
    Refines (Val.ashr (some x) b exact) (some x) := by
  cases b with
  | none => exact Refine.val_none _
  | some y =>
    refine refines_of_eq_or_none ?_
    simp only [Val.ashr, BitVec.sshiftRight_eq', sshiftRight_of_getMsbD x hx]
    split
    · exact Or.inl rfl
    · split <;> simp

/-- A `sext` of an `i1` is 0 or all ones. `IS.simplifyShift.L1322`: a shift by it is a shift by 0, or poison. -/
theorem signExtend_of_width_one (x : BitVec 1) (w : Nat) :
    x.signExtend w = 0#w ∨ x.signExtend w = BitVec.allOnes w := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
  · left
    have : x = 0#1 := BitVec.eq_of_toNat_eq (by simp [h])
    subst this
    ext i hi
    simp [BitVec.getElem_signExtend]
  · right
    have : x = 1#1 := BitVec.eq_of_toNat_eq (by simp [h])
    subst this
    ext i hi
    simp [BitVec.getElem_signExtend]

/-! ### Casts there and back -/

/-- `trunc (zext x to m)` back to the width of `x` refines `x`, whatever the flags, where the `zext` widens, as valid IR
has it. `IS.simplifyCastInst.L5653`. -/
theorem trunc_zext_refines (a : Val w) {m : Nat} (hm : w ≤ m) (nneg nuw nsw : Bool) :
    Refines (Val.trunc w (Val.zext m a nneg) nuw nsw) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    have hx : (x.setWidth m).setWidth w = x := by
      rw [BitVec.setWidth_setWidth_of_le _ hm, BitVec.setWidth_eq]
    simp only [Val.zext]
    split
    · simp [Val.trunc]
    · simp only [Val.trunc, hx]
      split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl

/-- `trunc (sext x to m)` back to the width of `x` refines `x`, whatever the flags, where the `sext` widens.
`IS.simplifyCastInst.L5653`. -/
theorem trunc_sext_refines (a : Val w) {m : Nat} (hm : w ≤ m) (nuw nsw : Bool) :
    Refines (Val.trunc w (Val.sext m a) nuw nsw) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    have hx : (x.signExtend m).setWidth w = x := by
      ext i hi
      simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend, hi, show i < m by omega]
    simp only [Val.sext, Val.map₁, Val.trunc, hx]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- `zext (trunc nuw x to m)` back to the width of `x` refines `x`, whatever the other flags: `nuw` says the dropped
bits were 0. `IS.simplifyCastInst.L5678`. -/
theorem zext_trunc_nuw_refines (a : Val w) (m : Nat) (nsw nneg : Bool) :
    Refines (Val.zext w (Val.trunc m a true nsw) nneg) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    simp only [Val.trunc, Bool.true_and]
    split
    · exact Or.inl rfl
    · next hu =>
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hu
      split
      · exact Or.inl rfl
      · simp only [Val.zext, hu]
        exact ite_none_or

/-- `sext (trunc nsw x to m)` back to the width of `x` refines `x`, whatever the other flag: `nsw` says the dropped
bits were copies of the sign bit. `IS.simplifyCastInst.L5678`. -/
theorem sext_trunc_nsw_refines (a : Val w) (m : Nat) (nuw : Bool) :
    Refines (Val.sext w (Val.trunc m a nuw true)) a := by
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    refine refines_of_eq_or_none ?_
    simp only [Val.trunc, Bool.true_and]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · next hs =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hs
        simp [Val.sext, Val.map₁, hs]

end Peephole.Lemmas

/-! ### Counterexamples, and witnesses -/

namespace LemmaStore.Counter

open IRLean

/-- A source that's the value `x` only allows `x`. -/
private theorem refines_ne {w : Nat} {a b : Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) :
    ¬ Refines a b := by
  subst ha; exact fun r => hb ((Refine.val_some x b).1 r)

/-- `shl 1, 0` is 1. -/
theorem Peephole.Lemmas.shl_of_le_toNat.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) {y : BitVec w} (nuw nsw : Bool), Val.shl a (some y) nuw nsw = none :=
  fun h => absurd (@h 1 (some 1#1) 0#1 false false) (by decide)

theorem Peephole.Lemmas.shl_of_le_toNat.sat : ∃ (w : Nat) (_ : Val w) (y : BitVec w) (_ _ : Bool), w ≤ y.toNat :=
  ⟨0, none, 0#0, false, false, Nat.le_refl _⟩

theorem Peephole.Lemmas.lshr_of_le_toNat.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) {y : BitVec w} (exact : Bool), Val.lshr a (some y) exact = none :=
  fun h => absurd (@h 1 (some 1#1) 0#1 false) (by decide)

theorem Peephole.Lemmas.lshr_of_le_toNat.sat : ∃ (w : Nat) (_ : Val w) (y : BitVec w) (_ : Bool), w ≤ y.toNat :=
  ⟨0, none, 0#0, false, Nat.le_refl _⟩

theorem Peephole.Lemmas.ashr_of_le_toNat.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) {y : BitVec w} (exact : Bool), Val.ashr a (some y) exact = none :=
  fun h => absurd (@h 1 (some 1#1) 0#1 false) (by decide)

theorem Peephole.Lemmas.ashr_of_le_toNat.sat : ∃ (w : Nat) (_ : Val w) (y : BitVec w) (_ : Bool), w ≤ y.toNat :=
  ⟨0, none, 0#0, false, Nat.le_refl _⟩

/-- `1` in `i1` has its sign bit set. -/
theorem Peephole.Lemmas.msb_eq_false_of_toNat_lt.drop_h : ¬ ∀ {w : Nat} {x : BitVec w}, x.msb = false :=
  fun h => absurd (@h 1 1#1) (by decide)

theorem Peephole.Lemmas.msb_eq_false_of_toNat_lt.sat : ∃ (w : Nat) (x : BitVec w), x.toNat < w :=
  ⟨1, 0#1, Nat.one_pos⟩

/-- At `n = 0` nothing is shifted in. -/
theorem Peephole.Lemmas.getLsbD_zero_shiftLeft.drop_hn :
    ¬ ∀ {w : Nat} {x : BitVec w} {n : Nat}, (x <<< n).getLsbD 0 = false :=
  fun h => absurd (@h 1 1#1 0) (by decide)

theorem Peephole.Lemmas.getLsbD_zero_shiftLeft.sat : ∃ (w : Nat) (_ : BitVec w) (n : Nat), n ≠ 0 :=
  ⟨0, 0#0, 1, Nat.one_ne_zero⟩

/-- `lshr exact i2 2, 1` is 1: no set bit is dropped. -/
theorem Peephole.Lemmas.lshr_exact_of_getLsbD_refines.drop_hx :
    ¬ ∀ {w : Nat} (x : BitVec w) (b : Val w), Refines (Val.lshr (some x) b true) (some x) :=
  fun h => refines_ne 1#2 (by decide) (by decide) (@h 2 2#2 (some 1#2))

theorem Peephole.Lemmas.lshr_exact_of_getLsbD_refines.sat :
    ∃ (w : Nat) (x : BitVec w) (_ : Val w), x.getLsbD 0 = true :=
  ⟨1, 1#1, none, by decide⟩

/-- `ashr exact i2 -2, 1` is -1. -/
theorem Peephole.Lemmas.ashr_exact_of_getLsbD_refines.drop_hx :
    ¬ ∀ {w : Nat} (x : BitVec w) (b : Val w), Refines (Val.ashr (some x) b true) (some x) :=
  fun h => refines_ne 3#2 (by decide) (by decide) (@h 2 2#2 (some 1#2))

theorem Peephole.Lemmas.ashr_exact_of_getLsbD_refines.sat :
    ∃ (w : Nat) (x : BitVec w) (_ : Val w), x.getLsbD 0 = true :=
  ⟨1, 1#1, none, by decide⟩

/-- `shl nuw i2 1, 1` is 2. -/
theorem Peephole.Lemmas.shl_nuw_of_msb_refines.drop_hx :
    ¬ ∀ {w : Nat} (x : BitVec w) (b : Val w) (nsw : Bool), Refines (Val.shl (some x) b true nsw) (some x) :=
  fun h => refines_ne 2#2 (by decide) (by decide) (@h 2 1#2 (some 1#2) false)

theorem Peephole.Lemmas.shl_nuw_of_msb_refines.sat : ∃ (w : Nat) (x : BitVec w) (_ : Val w) (_ : Bool), x.msb = true :=
  ⟨1, 1#1, none, false, by decide⟩

/-- `shl nuw nsw i2 1, 0` is 1. -/
theorem Peephole.Lemmas.shl_nuw_nsw_of_toNat_eq_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w}, 1 < w → Refines (Val.shl a (some c) true true) (some 0#w) :=
  fun h => refines_ne 1#2 (by decide) (by decide) (@h 2 (some 1#2) 0#2 (by decide))

/-- In `i1`, `w - 1` is 0, and `shl nuw nsw 1, 0` is 1. -/
theorem Peephole.Lemmas.shl_nuw_nsw_of_toNat_eq_refines.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w}, c.toNat = w - 1 → Refines (Val.shl a (some c) true true) (some 0#w) :=
  fun h => refines_ne 1#1 (by decide) (by decide) (@h 1 (some 1#1) 0#1 (by decide))

theorem Peephole.Lemmas.shl_nuw_nsw_of_toNat_eq_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w), c.toNat = w - 1 ∧ 1 < w :=
  ⟨2, none, 1#2, by decide, by decide⟩

/-- `lshr (or (shl nuw i2 0, 0), 1), 0` is 1. -/
theorem Peephole.Lemmas.lshr_or_shl_nuw_refines.drop_hy :
    ¬ ∀ {w : Nat} (a : Val w) {y c : BitVec w} (nsw disjoint exact : Bool),
      Refines (Val.lshr (Val.or (Val.shl a (some c) true nsw) (some y) disjoint) (some c) exact) a :=
  fun h => refines_ne 1#2 (by decide) (by decide) (@h 2 (some 0#2) 1#2 0#2 false false false)

theorem Peephole.Lemmas.lshr_or_shl_nuw_refines.sat :
    ∃ (w : Nat) (_ : Val w) (y c : BitVec w) (_ _ _ : Bool), y.toNat < 2 ^ c.toNat :=
  ⟨1, none, 0#1, 0#1, false, false, false, by decide⟩

/-- `ashr i2 1, 1` is 0. -/
theorem Peephole.Lemmas.getLsbD_eq_msb.drop_hx :
    ¬ ∀ {w : Nat} {x : BitVec w} {i : Nat}, i < w → x.getLsbD i = x.msb :=
  fun h => absurd (@h 2 1#2 0 (by decide)) (by decide)

/-- Bit 2 of an `i2` doesn't exist, and reads as 0. -/
theorem Peephole.Lemmas.getLsbD_eq_msb.drop_hi :
    ¬ ∀ {w : Nat} {x : BitVec w}, (∀ i, i < w → x.getMsbD i = x.msb) → ∀ {i : Nat}, x.getLsbD i = x.msb :=
  fun h => absurd (@h 2 3#2 (by decide) 2) (by decide)

theorem Peephole.Lemmas.getLsbD_eq_msb.sat :
    ∃ (w : Nat) (x : BitVec w) (i : Nat), (∀ i, i < w → x.getMsbD i = x.msb) ∧ i < w :=
  ⟨1, 0#1, 0, by decide, Nat.one_pos⟩

theorem Peephole.Lemmas.sshiftRight_of_getMsbD.drop_hx :
    ¬ ∀ {w : Nat} (x : BitVec w) (n : Nat), x.sshiftRight n = x :=
  fun h => absurd (@h 2 1#2 1) (by decide)

theorem Peephole.Lemmas.sshiftRight_of_getMsbD.sat :
    ∃ (w : Nat) (x : BitVec w) (_ : Nat), ∀ i, i < w → x.getMsbD i = x.msb :=
  ⟨1, 0#1, 0, by decide⟩

theorem Peephole.Lemmas.ashr_of_getMsbD_refines.drop_hx :
    ¬ ∀ {w : Nat} (x : BitVec w) (b : Val w) (exact : Bool), Refines (Val.ashr (some x) b exact) (some x) :=
  fun h => refines_ne 0#2 (by decide) (by decide) (@h 2 1#2 (some 1#2) false)

theorem Peephole.Lemmas.ashr_of_getMsbD_refines.sat :
    ∃ (w : Nat) (x : BitVec w) (_ : Val w) (_ : Bool), ∀ i, i < w → x.getMsbD i = x.msb :=
  ⟨1, 0#1, none, false, by decide⟩

/-- `zext i2 2 to i1` is 0, and `trunc` of that to `i2` is 0. -/
theorem Peephole.Lemmas.trunc_zext_refines.drop_hm :
    ¬ ∀ {w : Nat} (a : Val w) {m : Nat} (nneg nuw nsw : Bool), Refines (Val.trunc w (Val.zext m a nneg) nuw nsw) a :=
  fun h => refines_ne 0#2 (by decide) (by decide) (@h 2 (some 2#2) 1 false false false)

theorem Peephole.Lemmas.trunc_zext_refines.sat : ∃ (w : Nat) (_ : Val w) (m : Nat) (_ _ _ : Bool), w ≤ m :=
  ⟨0, none, 0, false, false, false, Nat.le_refl 0⟩

/-- `sext i2 2 to i1` is 0, and `trunc` of that to `i2` is 0. -/
theorem Peephole.Lemmas.trunc_sext_refines.drop_hm :
    ¬ ∀ {w : Nat} (a : Val w) {m : Nat} (nuw nsw : Bool), Refines (Val.trunc w (Val.sext m a) nuw nsw) a :=
  fun h => refines_ne 0#2 (by decide) (by decide) (@h 2 (some 2#2) 1 false false)

theorem Peephole.Lemmas.trunc_sext_refines.sat : ∃ (w : Nat) (_ : Val w) (m : Nat) (_ _ : Bool), w ≤ m :=
  ⟨0, none, 0, false, false, Nat.le_refl 0⟩

end LemmaStore.Counter
