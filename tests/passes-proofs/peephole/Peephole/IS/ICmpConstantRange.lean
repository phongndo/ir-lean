import Peephole.IS.ICmpBase

/-! # LLVM's `ConstantRange`, as far as `simplifyICmpInst` uses it

`llvm/lib/IR/ConstantRange.cpp` at `llvmorg-23.1.3`: the functions `simplifyICmpWithConstant` and `simplifyICmpInst`
call, each as the C++ computes it on `Lower` and `Upper`, and what each says about the values a range contains.

- `makeExactICmpRegion p c` contains exactly the `x` with `icmp p x, c` true: `makeExact_contains`.
- `containsRange r o`, `ConstantRange::contains(const ConstantRange &)`, means every value `o` contains, `r` does:
  `containsRange_sound`.
- `inverse r` contains no value `r` does: `inverse_contains`.
- `icmp r p o`, `ConstantRange::icmp`, means `icmp p x, y` holds for every `x` in `r` and `y` in `o`: `icmp_sound`.

Each holds at a positive width. LLVM's integer types have at least one bit; at width 0, where `Term` can still be,
the full and the empty set are the same pair, so the models only read a range at a positive width. -/

namespace Peephole.IS.ICmp

open IRLean Peephole.Lemmas

variable {w : Nat}

namespace CR

/-! ### The functions, as `ConstantRange.cpp` has them -/

/-- `ConstantRange(APInt V)`: the one value `V`, `[V, V + 1)`. -/
def ofAPInt (c : BitVec w) : CR w := ⟨c, c + 1#w⟩

/-- `ConstantRange::getEmpty`. -/
def empty : CR w := ⟨0#w, 0#w⟩

/-- `ConstantRange::getNonEmpty(Lower, Upper)`: the full set if they're equal. -/
def nonEmpty (l u : BitVec w) : CR w := if l == u then full else ⟨l, u⟩

/-- `ConstantRange::isWrappedSet`. -/
def isWrappedSet (r : CR w) : Bool := BitVec.ult r.upper r.lower && r.upper != 0#w

/-- `ConstantRange::isUpperSignWrapped`. -/
def isUpperSignWrapped (r : CR w) : Bool := BitVec.slt r.upper r.lower

/-- `ConstantRange::isSignWrappedSet`. -/
def isSignWrappedSet (r : CR w) : Bool := BitVec.slt r.upper r.lower && r.upper != BitVec.intMin w

/-- `ConstantRange::getUnsignedMax`. -/
def getUnsignedMax (r : CR w) : BitVec w :=
  if r.isFullSet || r.isUpperWrapped then BitVec.allOnes w else r.upper - 1#w

/-- `ConstantRange::getUnsignedMin`. -/
def getUnsignedMin (r : CR w) : BitVec w :=
  if r.isFullSet || r.isWrappedSet then 0#w else r.lower

/-- `ConstantRange::getSignedMax`. -/
def getSignedMax (r : CR w) : BitVec w :=
  if r.isFullSet || r.isUpperSignWrapped then BitVec.intMax w else r.upper - 1#w

/-- `ConstantRange::getSignedMin`. -/
def getSignedMin (r : CR w) : BitVec w :=
  if r.isFullSet || r.isSignWrappedSet then BitVec.intMin w else r.lower

/-- `ConstantRange::getSingleElement`. -/
def getSingleElement (r : CR w) : Option (BitVec w) :=
  if r.upper == r.lower + 1#w then some r.lower else none

/-- `ConstantRange::isSingleElement`. -/
def isSingleElement (r : CR w) : Bool := r.getSingleElement.isSome

/-- `ConstantRange::inverse`. -/
def inverse (r : CR w) : CR w :=
  if r.isFullSet then empty
  else if r.isEmptySet then full
  else ⟨r.upper, r.lower⟩

/-- `ConstantRange::contains(const ConstantRange &Other)`. -/
def containsRange (r o : CR w) : Bool :=
  if r.isFullSet || o.isEmptySet then true
  else if r.isEmptySet || o.isFullSet then false
  else if !r.isUpperWrapped then
    if o.isUpperWrapped then false
    else BitVec.ule r.lower o.lower && BitVec.ule o.upper r.upper
  else if !o.isUpperWrapped then BitVec.ule o.upper r.upper || BitVec.ule r.lower o.lower
  else BitVec.ule o.upper r.upper && BitVec.ule r.lower o.lower

/-- `ConstantRange::makeAllowedICmpRegion(CmpInst::Predicate, const ConstantRange &)`. -/
def makeAllowedICmpRegion (p : Pred) (cr : CR w) : CR w :=
  if cr.isEmptySet then cr
  else
    match p with
    | .eq => cr
    | .ne => if cr.isSingleElement then ⟨cr.upper, cr.lower⟩ else full
    | .ult => if cr.getUnsignedMax == 0#w then empty else ⟨0#w, cr.getUnsignedMax⟩
    | .slt => if cr.getSignedMax == BitVec.intMin w then empty else ⟨BitVec.intMin w, cr.getSignedMax⟩
    | .ule => nonEmpty 0#w (cr.getUnsignedMax + 1#w)
    | .sle => nonEmpty (BitVec.intMin w) (cr.getSignedMax + 1#w)
    | .ugt => if cr.getUnsignedMin == BitVec.allOnes w then empty else ⟨cr.getUnsignedMin + 1#w, 0#w⟩
    | .sgt => if cr.getSignedMin == BitVec.intMax w then empty else ⟨cr.getSignedMin + 1#w, BitVec.intMin w⟩
    | .uge => nonEmpty cr.getUnsignedMin 0#w
    | .sge => nonEmpty cr.getSignedMin (BitVec.intMin w)

/-- `ConstantRange::makeExactICmpRegion(CmpInst::Predicate, const APInt &)`: `makeAllowedICmpRegion` of the single
value. -/
def makeExactICmpRegion (p : Pred) (c : BitVec w) : CR w := makeAllowedICmpRegion p (ofAPInt c)

/-- `ConstantRange::icmp(CmpInst::Predicate, const ConstantRange &Other)`: whether `icmp p` holds for every pair of
values in `r` and `o`. -/
def icmp (r : CR w) (p : Pred) (o : CR w) : Bool :=
  if r.isEmptySet || o.isEmptySet then true
  else
    match p with
    | .eq =>
      match r.getSingleElement, o.getSingleElement with
      | some l, some r' => l == r'
      | _, _ => false
    | .ne => r.inverse.containsRange o
    | .ult => BitVec.ult r.getUnsignedMax o.getUnsignedMin
    | .ule => BitVec.ule r.getUnsignedMax o.getUnsignedMin
    | .ugt => BitVec.ult o.getUnsignedMax r.getUnsignedMin
    | .uge => BitVec.ule o.getUnsignedMax r.getUnsignedMin
    | .slt => BitVec.slt r.getSignedMax o.getSignedMin
    | .sle => BitVec.sle r.getSignedMax o.getSignedMin
    | .sgt => BitVec.slt o.getSignedMax r.getSignedMin
    | .sge => BitVec.sle o.getSignedMax r.getSignedMin

/-! ### On `toNat`s -/

theorem isFullSet_iff (r : CR w) :
    r.isFullSet = true ↔ r.lower.toNat = r.upper.toNat ∧ r.lower.toNat = 2 ^ w - 1 := by
  simp [isFullSet, BitVec.toNat_eq]

theorem isEmptySet_iff (r : CR w) : r.isEmptySet = true ↔ r.lower.toNat = r.upper.toNat ∧ r.lower.toNat = 0 := by
  simp [isEmptySet, BitVec.toNat_eq]

theorem isUpperWrapped_iff (r : CR w) : r.isUpperWrapped = true ↔ r.upper.toNat < r.lower.toNat := by
  simp [isUpperWrapped, BitVec.ult_eq_decide]

theorem contains_iff (r : CR w) (x : BitVec w) :
    r.contains x = true ↔
      (r.lower.toNat = r.upper.toNat ∧ r.lower.toNat = 2 ^ w - 1) ∨
      (r.lower.toNat ≠ r.upper.toNat ∧ r.lower.toNat ≤ r.upper.toNat ∧ r.lower.toNat ≤ x.toNat ∧
        x.toNat < r.upper.toNat) ∨
      (r.upper.toNat < r.lower.toNat ∧ (r.lower.toNat ≤ x.toNat ∨ x.toNat < r.upper.toNat)) := by
  unfold CR.contains
  by_cases h : r.lower = r.upper
  · have h' : r.lower.toNat = r.upper.toNat := by rw [h]
    have hb : (r.lower == r.upper) = true := by simp [h]
    simp only [hb, ↓reduceIte, isFullSet_iff]
    omega
  · have h' : r.lower.toNat ≠ r.upper.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [beq_iff_eq, h, ite_false]
    split
    · next hw =>
      simp only [Bool.not_eq_true', isUpperWrapped, BitVec.ult_eq_decide, decide_eq_false_iff_not,
        Nat.not_lt] at hw
      simp only [Bool.and_eq_true, BitVec.ule_eq_decide, BitVec.ult_eq_decide, decide_eq_true_eq]
      omega
    · next hw =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, isUpperWrapped, BitVec.ult_eq_decide,
        decide_eq_true_eq] at hw
      simp only [Bool.or_eq_true, BitVec.ule_eq_decide, BitVec.ult_eq_decide, decide_eq_true_eq]
      omega

/-! ### What each function says about the values a range contains -/

theorem isEmptySet_contains (hw : 0 < w) {r : CR w} (h : r.isEmptySet = true) (x : BitVec w) :
    r.contains x = false := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  rw [isEmptySet_iff] at h
  apply Bool.eq_false_iff.2
  rw [Ne, contains_iff]
  omega

theorem empty_contains (hw : 0 < w) (x : BitVec w) : (empty : CR w).contains x = false :=
  isEmptySet_contains hw (by simp [isEmptySet, empty]) x

theorem isFullSet_contains {r : CR w} (h : r.isFullSet = true) (x : BitVec w) : r.contains x = true := by
  rw [isFullSet_iff] at h
  rw [contains_iff]
  omega

theorem nonEmpty_contains (l u x : BitVec w) :
    (nonEmpty l u).contains x = if l = u then true else (CR.mk l u).contains x := by
  unfold nonEmpty
  by_cases h : l = u
  · simp [h, full_contains]
  · simp [h]

/-- Every value `o` contains, `r` does, if `containsRange r o`. -/
theorem containsRange_sound (hw : 0 < w) {r o : CR w} (h : r.containsRange o = true) {x : BitVec w}
    (hx : o.contains x = true) : r.contains x = true := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  have := r.lower.isLt
  have := r.upper.isLt
  have := o.lower.isLt
  have := o.upper.isLt
  have := x.isLt
  rw [contains_iff] at hx ⊢
  unfold containsRange at h
  split at h
  · next hc =>
    simp only [Bool.or_eq_true, isFullSet_iff, isEmptySet_iff] at hc
    omega
  · next hc =>
    simp only [Bool.or_eq_true, isFullSet_iff, isEmptySet_iff, not_or] at hc
    split at h
    · cases h
    · next hc' =>
      simp only [Bool.or_eq_true, isFullSet_iff, isEmptySet_iff, not_or] at hc'
      split at h
      · next hrw =>
        simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, isUpperWrapped_iff] at hrw
        split at h
        · cases h
        · next how =>
          simp only [isUpperWrapped_iff] at how
          simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at h
          omega
      · next hrw =>
        simp only [Bool.not_eq_true', Bool.not_eq_false, isUpperWrapped_iff] at hrw
        split at h
        · next how =>
          simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, isUpperWrapped_iff] at how
          simp only [Bool.or_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at h
          omega
        · next how =>
          simp only [Bool.not_eq_true', Bool.not_eq_false, isUpperWrapped_iff] at how
          simp only [Bool.and_eq_true, BitVec.ule_eq_decide, decide_eq_true_eq] at h
          omega

/-- `inverse r` contains no value `r` does. -/
theorem inverse_contains (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.inverse.contains x = true) :
    r.contains x = false := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  have := r.lower.isLt
  have := r.upper.isLt
  have := x.isLt
  apply Bool.eq_false_iff.2
  rw [Ne, contains_iff]
  unfold inverse at h
  split at h
  · rw [empty_contains hw] at h; cases h
  · next hf =>
    split at h
    · next he =>
      rw [isEmptySet_iff] at he
      omega
    · next he =>
      rw [Bool.not_eq_true, ← Bool.not_eq_true, isFullSet_iff] at hf
      rw [Bool.not_eq_true, ← Bool.not_eq_true, isEmptySet_iff] at he
      rw [contains_iff] at h
      simp only at h
      omega

/-- No value `r` contains is in `inverse r`. -/
theorem contains_inverse (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.contains x = true) :
    r.inverse.contains x = false := by
  cases hc : r.inverse.contains x
  · rfl
  · rw [inverse_contains hw hc] at h; cases h

/-! ### The single value -/

theorem ofAPInt_lower_ne (hw : 0 < w) (c : BitVec w) : c ≠ c + 1#w := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  intro h
  have h' := congrArg BitVec.toNat h
  rcases toNat_add_one_or c hw with ⟨-, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem ofAPInt_isEmptySet (hw : 0 < w) (c : BitVec w) : (ofAPInt c).isEmptySet = false := by
  simp [isEmptySet, ofAPInt, ofAPInt_lower_ne hw c]

theorem ofAPInt_isFullSet (hw : 0 < w) (c : BitVec w) : (ofAPInt c).isFullSet = false := by
  simp [isFullSet, ofAPInt, ofAPInt_lower_ne hw c]

theorem ofAPInt_getUnsignedMax (hw : 0 < w) (c : BitVec w) : (ofAPInt c).getUnsignedMax = c := by
  have := c.isLt
  unfold getUnsignedMax
  rw [ofAPInt_isFullSet hw, Bool.false_or]
  split
  · next h =>
    simp only [isUpperWrapped, ofAPInt, BitVec.ult_eq_decide, decide_eq_true_eq] at h
    apply BitVec.eq_of_toNat_eq
    rcases toNat_add_one_or c hw with ⟨-, h2⟩ | ⟨h1, h2⟩ <;> simp only [BitVec.toNat_allOnes] <;> omega
  · simp only [ofAPInt, BitVec.add_sub_cancel]

theorem ofAPInt_getUnsignedMin (hw : 0 < w) (c : BitVec w) : (ofAPInt c).getUnsignedMin = c := by
  unfold getUnsignedMin
  rw [ofAPInt_isFullSet hw, Bool.false_or]
  split
  · next h =>
    simp only [isWrappedSet, ofAPInt, Bool.and_eq_true, BitVec.ult_eq_decide, decide_eq_true_eq, bne_iff_ne,
      ne_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod] at h
    rcases toNat_add_one_or c hw with ⟨-, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rfl

theorem ofAPInt_getSignedMax (hw : 0 < w) (c : BitVec w) : (ofAPInt c).getSignedMax = c := by
  have := c.isLt
  have hp := two_pow_pred hw
  unfold getSignedMax
  rw [ofAPInt_isFullSet hw, Bool.false_or]
  split
  · next h =>
    simp only [isUpperSignWrapped, ofAPInt, slt_eq_sub_intMin _ _ hw, decide_eq_true_eq] at h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_intMax]
    have := toNat_sub_intMin_or c hw
    have := toNat_sub_intMin_or (c + 1#w) hw
    rcases toNat_add_one_or c hw with ⟨-, h2⟩ | ⟨h1, h2⟩ <;> omega
  · simp only [ofAPInt, BitVec.add_sub_cancel]

theorem ofAPInt_getSignedMin (hw : 0 < w) (c : BitVec w) : (ofAPInt c).getSignedMin = c := by
  have := c.isLt
  have hp := two_pow_pred hw
  unfold getSignedMin
  rw [ofAPInt_isFullSet hw, Bool.false_or]
  split
  · next h =>
    simp only [isSignWrappedSet, ofAPInt, Bool.and_eq_true, slt_eq_sub_intMin _ _ hw, decide_eq_true_eq,
      bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_intMin_of_pos hw] at h
    have := toNat_sub_intMin_or c hw
    have := toNat_sub_intMin_or (c + 1#w) hw
    rcases toNat_add_one_or c hw with ⟨-, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rfl

theorem ofAPInt_isSingleElement (c : BitVec w) : (ofAPInt c).isSingleElement = true := by
  simp [isSingleElement, getSingleElement, ofAPInt]

/-! ### `makeExactICmpRegion`, one predicate at a time -/

section makeExact

variable (hw : 0 < w) (c x : BitVec w)
include hw

theorem makeExact_eq : (makeExactICmpRegion .eq c).contains x = test .eq x c := by
  have hc1 := toNat_add_one_or c hw
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte]
  rw [Bool.eq_iff_iff, contains_iff]
  simp only [ofAPInt, test, beq_iff_eq, BitVec.toNat_eq]
  omega

theorem makeExact_ne : (makeExactICmpRegion .ne c).contains x = test .ne x c := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  have hc1 := toNat_add_one_or c hw
  have := c.isLt
  have := x.isLt
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_isSingleElement]
  rw [Bool.eq_iff_iff, contains_iff]
  simp only [ofAPInt, test, bne_iff_ne, ne_eq, BitVec.toNat_eq]
  constructor <;> intro hh <;> omega

theorem makeExact_ult : (makeExactICmpRegion .ult c).contains x = test .ult x c := by
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getUnsignedMax hw]
  by_cases h : c = 0#w
  · have hb : (c == 0#w) = true := by simp [h]
    simp only [h, beq_self_eq_true, ↓reduceIte, empty_contains hw, test, BitVec.ult_eq_decide,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.not_lt_zero, decide_false]
  · have hb : (c == 0#w) = false := by simp [h]
    have h' : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.zero_mod]
    omega

theorem makeExact_ule : (makeExactICmpRegion .ule c).contains x = test .ule x c := by
  have hc1 := toNat_add_one_or c hw
  have := c.isLt
  have := x.isLt
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getUnsignedMax hw, nonEmpty_contains]
  by_cases h : (0#w : BitVec w) = c + 1#w
  · have h' := congrArg BitVec.toNat h
    simp only [h, ↓reduceIte, test, BitVec.ule_eq_decide]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h'
    symm
    rw [decide_eq_true_iff]
    omega
  · have h' : (0#w : BitVec w).toNat ≠ (c + 1#w).toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.zero_mod] at h' ⊢
    omega

theorem makeExact_ugt : (makeExactICmpRegion .ugt c).contains x = test .ugt x c := by
  have := c.isLt
  have := x.isLt
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getUnsignedMin hw]
  have hc1 := toNat_add_one_or c hw
  by_cases h : c = BitVec.allOnes w
  · have hb : (c == BitVec.allOnes w) = true := by simp [h]
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_allOnes] at h'
    simp only [hb, ↓reduceIte, empty_contains hw, test, BitVec.ult_eq_decide]
    symm
    rw [decide_eq_false_iff_not]
    omega
  · have hb : (c == BitVec.allOnes w) = false := by simp [h]
    have h' : c.toNat ≠ 2 ^ w - 1 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.zero_mod]
    omega

theorem makeExact_uge : (makeExactICmpRegion .uge c).contains x = test .uge x c := by
  have := c.isLt
  have := x.isLt
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getUnsignedMin hw, nonEmpty_contains]
  by_cases h : c = 0#w
  · simp only [h, ↓reduceIte, test, BitVec.ule_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_le,
      decide_true]
  · have h' : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [h, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.zero_mod]
    omega

/-- The signed facts each signed case needs, on `toNat`s after subtracting `intMin`. -/
theorem signed_facts :
    (BitVec.intMin w).toNat = 2 ^ (w - 1) ∧ (BitVec.intMax w).toNat = 2 ^ (w - 1) - 1 ∧
      (BitVec.intMin w - BitVec.intMin w).toNat = 0 ∧ 2 ^ w = 2 * 2 ^ (w - 1) :=
  ⟨BitVec.toNat_intMin_of_pos hw, BitVec.toNat_intMax, by simp, two_pow_pred hw⟩

theorem makeExact_slt : (makeExactICmpRegion .slt c).contains x = test .slt x c := by
  have := c.isLt
  have := x.isLt
  have hf := signed_facts hw
  have := toNat_sub_intMin_or c hw
  have := toNat_sub_intMin_or x hw
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getSignedMax hw]
  by_cases h : c = BitVec.intMin w
  · have hb : (c == BitVec.intMin w) = true := by simp [h]
    have h' := congrArg BitVec.toNat h
    simp only [hb, ↓reduceIte, empty_contains hw, test, slt_eq_sub_intMin _ _ hw]
    symm
    rw [decide_eq_false_iff_not]
    omega
  · have hb : (c == BitVec.intMin w) = false := by simp [h]
    have h' : c.toNat ≠ (BitVec.intMin w).toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, slt_eq_sub_intMin _ _ hw, decide_eq_true_eq]
    omega

theorem makeExact_sle : (makeExactICmpRegion .sle c).contains x = test .sle x c := by
  have := c.isLt
  have := x.isLt
  have hf := signed_facts hw
  have := toNat_sub_intMin_or c hw
  have := toNat_sub_intMin_or x hw
  have := toNat_add_one_or c hw
  have := toNat_sub_intMin_or (c + 1#w) hw
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getSignedMax hw, nonEmpty_contains]
  by_cases h : BitVec.intMin w = c + 1#w
  · have h' := congrArg BitVec.toNat h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [test, sle_eq_sub_intMin _ _ hw]
    symm
    rw [decide_eq_true_iff]
    omega
  · have h' : (BitVec.intMin w).toNat ≠ (c + 1#w).toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]
    omega

theorem makeExact_sgt : (makeExactICmpRegion .sgt c).contains x = test .sgt x c := by
  have := c.isLt
  have := x.isLt
  have hf := signed_facts hw
  have := toNat_sub_intMin_or c hw
  have := toNat_sub_intMin_or x hw
  have := toNat_add_one_or c hw
  have := toNat_sub_intMin_or (c + 1#w) hw
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getSignedMin hw]
  by_cases h : c = BitVec.intMax w
  · have hb : (c == BitVec.intMax w) = true := by simp [h]
    have h' := congrArg BitVec.toNat h
    simp only [hb, ↓reduceIte, empty_contains hw, test, slt_eq_sub_intMin _ _ hw]
    symm
    rw [decide_eq_false_iff_not]
    omega
  · have hb : (c == BitVec.intMax w) = false := by simp [h]
    have h' : c.toNat ≠ (BitVec.intMax w).toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, slt_eq_sub_intMin _ _ hw, decide_eq_true_eq]
    omega

theorem makeExact_sge : (makeExactICmpRegion .sge c).contains x = test .sge x c := by
  have := c.isLt
  have := x.isLt
  have hf := signed_facts hw
  have := toNat_sub_intMin_or c hw
  have := toNat_sub_intMin_or x hw
  simp only [makeExactICmpRegion, makeAllowedICmpRegion, ofAPInt_isEmptySet hw, Bool.false_eq_true, ↓reduceIte,
    ofAPInt_getSignedMin hw, nonEmpty_contains]
  by_cases h : c = BitVec.intMin w
  · have h' := congrArg BitVec.toNat h
    simp only [h, ↓reduceIte, test, sle_eq_sub_intMin _ _ hw]
    symm
    rw [decide_eq_true_iff]
    omega
  · have h' : c.toNat ≠ (BitVec.intMin w).toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [h, ↓reduceIte]
    rw [Bool.eq_iff_iff, contains_iff]
    simp only [test, sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]
    omega

end makeExact

/-- `makeExactICmpRegion p c` contains exactly the values `x` with `icmp p x, c` true. -/
theorem makeExact_contains (hw : 0 < w) (p : Pred) (c x : BitVec w) :
    (makeExactICmpRegion p c).contains x = test p x c := by
  cases p
  · exact makeExact_eq hw c x
  · exact makeExact_ne hw c x
  · exact makeExact_ugt hw c x
  · exact makeExact_uge hw c x
  · exact makeExact_ult hw c x
  · exact makeExact_ule hw c x
  · exact makeExact_sgt hw c x
  · exact makeExact_sge hw c x
  · exact makeExact_slt hw c x
  · exact makeExact_sle hw c x

/-! ### The bounds of a range -/

theorem le_getUnsignedMax (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.contains x = true) :
    BitVec.ule x r.getUnsignedMax = true := by
  have := x.isLt
  have := r.lower.isLt
  rw [contains_iff] at h
  unfold getUnsignedMax
  split
  · simp [BitVec.ule_eq_decide]; omega
  · next hc =>
    simp only [Bool.or_eq_true, isFullSet_iff, isUpperWrapped_iff, not_or] at hc
    have := toNat_sub_one_or r.upper hw
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    omega

theorem getUnsignedMin_le {r : CR w} {x : BitVec w} (h : r.contains x = true) :
    BitVec.ule r.getUnsignedMin x = true := by
  have := x.isLt
  rw [contains_iff] at h
  unfold getUnsignedMin
  split
  · simp [BitVec.ule_eq_decide]
  · next hc =>
    simp only [Bool.or_eq_true, isFullSet_iff, isWrappedSet, Bool.and_eq_true, BitVec.ult_eq_decide,
      decide_eq_true_eq, bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod, not_or,
      not_and] at hc
    simp only [BitVec.ule_eq_decide, decide_eq_true_eq]
    omega

/-- In signed terms, after subtracting `intMin`, a range is the same range of the shifted values. -/
theorem contains_sub_intMin (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.contains x = true)
    (hne : r.lower ≠ r.upper) :
    ((r.lower - BitVec.intMin w).toNat ≤ (r.upper - BitVec.intMin w).toNat ∧
        (r.lower - BitVec.intMin w).toNat ≤ (x - BitVec.intMin w).toNat ∧
        (x - BitVec.intMin w).toNat < (r.upper - BitVec.intMin w).toNat) ∨
      ((r.upper - BitVec.intMin w).toNat < (r.lower - BitVec.intMin w).toNat ∧
        ((r.lower - BitVec.intMin w).toNat ≤ (x - BitVec.intMin w).toNat ∨
          (x - BitVec.intMin w).toNat < (r.upper - BitVec.intMin w).toNat)) := by
  have hne' : r.lower.toNat ≠ r.upper.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  have hp := two_pow_pred hw
  have := x.isLt
  have := r.lower.isLt
  have := r.upper.isLt
  have := toNat_sub_intMin_or x hw
  have := toNat_sub_intMin_or r.lower hw
  have := toNat_sub_intMin_or r.upper hw
  rw [contains_iff] at h
  omega

theorem le_getSignedMax (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.contains x = true) :
    BitVec.sle x r.getSignedMax = true := by
  have hp := two_pow_pred hw
  have := x.isLt
  have := toNat_sub_intMin_or x hw
  have := toNat_sub_intMin_or (BitVec.intMax w) hw
  have := BitVec.toNat_intMax (w := w)
  unfold getSignedMax
  split
  · simp only [sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]; omega
  · next hc =>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, isUpperSignWrapped, slt_eq_sub_intMin _ _ hw,
      decide_eq_false_iff_not, Nat.not_lt] at hc
    by_cases hne : r.lower = r.upper
    · have := isFullSet_contains (r := r)
      rw [contains_iff] at h
      have : r.isFullSet = true := by rw [isFullSet_iff]; have := congrArg BitVec.toNat hne; omega
      rw [this] at hc; cases hc.1
    · have := contains_sub_intMin hw h hne
      have := toNat_sub_one_or r.upper hw
      have := toNat_sub_intMin_or r.upper hw
      have := toNat_sub_intMin_or (r.upper - 1#w) hw
      simp only [sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]
      omega

theorem getSignedMin_le (hw : 0 < w) {r : CR w} {x : BitVec w} (h : r.contains x = true) :
    BitVec.sle r.getSignedMin x = true := by
  have hp := two_pow_pred hw
  have := x.isLt
  have := toNat_sub_intMin_or x hw
  have := BitVec.toNat_intMin_of_pos hw
  have := toNat_sub_intMin_or (BitVec.intMin w) hw
  unfold getSignedMin
  split
  · simp only [sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]; omega
  · next hc =>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, isSignWrappedSet, Bool.and_eq_false_iff,
      slt_eq_sub_intMin _ _ hw, decide_eq_false_iff_not, Nat.not_lt, bne_eq_false_iff_eq] at hc
    by_cases hne : r.lower = r.upper
    · rw [contains_iff] at h
      have : r.isFullSet = true := by rw [isFullSet_iff]; have := congrArg BitVec.toNat hne; omega
      rw [this] at hc; cases hc.1
    · have := contains_sub_intMin hw h hne
      have := toNat_sub_intMin_or r.upper hw
      have := toNat_sub_intMin_or r.lower hw
      have hu : r.upper = BitVec.intMin w → r.upper.toNat = 2 ^ (w - 1) := fun e => by
        rw [e]; exact BitVec.toNat_intMin_of_pos hw
      simp only [sle_eq_sub_intMin _ _ hw, decide_eq_true_eq]
      rcases hc.2 with hc2 | hc2
      · omega
      · have := hu hc2; omega

theorem getSingleElement_eq (hw : 0 < w) {r : CR w} {l x : BitVec w} (hs : r.getSingleElement = some l)
    (h : r.contains x = true) : x = l := by
  have := Nat.one_lt_two_pow_iff.2 (by omega : w ≠ 0)
  have := x.isLt
  unfold getSingleElement at hs
  split at hs
  · next hu =>
    cases hs
    simp only [beq_iff_eq] at hu
    have hu' := congrArg BitVec.toNat hu
    have := toNat_add_one_or r.lower hw
    rw [contains_iff] at h
    apply BitVec.eq_of_toNat_eq
    omega
  · cases hs

/-- `icmp r p o`: `icmp p x, y` holds for every `x` in `r` and `y` in `o`. -/
theorem icmp_sound (hw : 0 < w) {r o : CR w} {p : Pred} (h : r.icmp p o = true) {x y : BitVec w}
    (hx : r.contains x = true) (hy : o.contains y = true) : test p x y = true := by
  unfold icmp at h
  split at h
  · next he =>
    simp only [Bool.or_eq_true] at he
    rcases he with he | he
    · rw [isEmptySet_contains hw he] at hx; cases hx
    · rw [isEmptySet_contains hw he] at hy; cases hy
  · have h1 := le_getUnsignedMax hw hx
    have h2 := getUnsignedMin_le hx
    have h3 := le_getSignedMax hw hx
    have h4 := getSignedMin_le hw hx
    have h5 := le_getUnsignedMax hw hy
    have h6 := getUnsignedMin_le hy
    have h7 := le_getSignedMax hw hy
    have h8 := getSignedMin_le hw hy
    simp only [BitVec.ule_eq_decide, BitVec.sle_eq_decide, decide_eq_true_eq] at h1 h2 h3 h4 h5 h6 h7 h8
    cases p with
    | eq =>
      simp only at h
      split at h
      · next l r' hl hr =>
        simp only [beq_iff_eq] at h
        subst h
        simp [test, getSingleElement_eq hw hl hx, getSingleElement_eq hw hr hy]
      · cases h
    | ne =>
      simp only [test, bne_iff_ne, ne_eq]
      intro he
      subst he
      have := containsRange_sound hw h hy
      rw [contains_inverse hw hx] at this
      cases this
    | ult => simp only [test, BitVec.ult_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | ule => simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | ugt => simp only [test, BitVec.ult_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | uge => simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | slt => simp only [test, BitVec.slt_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | sle => simp only [test, BitVec.sle_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | sgt => simp only [test, BitVec.slt_eq_decide, decide_eq_true_eq] at h ⊢; omega
    | sge => simp only [test, BitVec.sle_eq_decide, decide_eq_true_eq] at h ⊢; omega

end CR

end Peephole.IS.ICmp
