import IRLean.Contract.Poison

/-! # Counterexamples for LangRef's integer contracts

For each hypothesis of a lemma from `IRLean.Contract.Poison`, the lemma without it is false: `drop_<hypothesis>` gives
one input where it fails, and `sat` gives one where its hypotheses all hold. `tools/store/store.py check` checks each
states exactly what it has to. -/

namespace LemmaStore.Counter

open IRLean IRLean.Contract

/-! ### Poison in, poison out, given a poison operand -/

/-- With every operand a value, the result is a value. -/
theorem IRLean.Contract.fshl_strict.drop_h : ¬ ∀ {w : Nat} (a b c : Val w), Val.fshl a b c = none :=
  fun h => absurd (@h 1 (some 0#1) (some 0#1) (some 0#1)) (by simp [Val.fshl])

theorem IRLean.Contract.fshl_strict.sat : ∃ (w : Nat) (a b c : Val w), a = none ∨ b = none ∨ c = none :=
  ⟨1, none, none, none, .inl rfl⟩

theorem IRLean.Contract.fshr_strict.drop_h : ¬ ∀ {w : Nat} (a b c : Val w), Val.fshr a b c = none :=
  fun h => absurd (@h 1 (some 0#1) (some 0#1) (some 0#1)) (by simp [Val.fshr])

theorem IRLean.Contract.fshr_strict.sat : ∃ (w : Nat) (a b c : Val w), a = none ∨ b = none ∨ c = none :=
  ⟨1, none, none, none, .inl rfl⟩

theorem IRLean.Contract.withOverflow_strict.drop_h :
    ¬ ∀ {w : Nat} (f : BitVec w → BitVec w → BitVec w) (o : BitVec w → BitVec w → Bool) (a b : Val w),
      Val.withOverflow f o a b = (none, none) :=
  fun h => absurd (@h 1 (fun x _ => x) (fun _ _ => false) (some 0#1) (some 0#1)) (by simp [Val.withOverflow])

theorem IRLean.Contract.withOverflow_strict.sat :
    ∃ (w : Nat) (_ : BitVec w → BitVec w → BitVec w) (_ : BitVec w → BitVec w → Bool) (a b : Val w),
      a = none ∨ b = none :=
  ⟨1, fun x _ => x, fun _ _ => false, none, none, .inl rfl⟩

/-! ### Division gives a value where it isn't undefined: dividing by zero is -/

theorem IRLean.Contract.udiv_noPoison.drop_h :
    ¬ ∀ {w : Nat} (x y : BitVec w), ∃ r, Val.udiv (some x) (some y) = Outcome.ok (some r) := fun h =>
  let ⟨r, hr⟩ := @h 1 0#1 0#1
  not_isUB_ok (some r) (hr ▸ (udiv_isUB_iff 0#1 0#1 false).2 rfl)

theorem IRLean.Contract.udiv_noPoison.sat :
    ∃ (w : Nat) (x y : BitVec w), ¬ IsUB (Val.udiv (some x) (some y)) :=
  ⟨1, 0#1, 1#1, fun hu => absurd ((udiv_isUB_iff 0#1 1#1 false).1 hu) (by decide)⟩

theorem IRLean.Contract.sdiv_noPoison.drop_h :
    ¬ ∀ {w : Nat} (x y : BitVec w), ∃ r, Val.sdiv (some x) (some y) = Outcome.ok (some r) := fun h =>
  let ⟨r, hr⟩ := @h 1 0#1 0#1
  not_isUB_ok (some r) (hr ▸ (sdiv_isUB_iff 0#1 0#1 false).2 (.inl rfl))

theorem IRLean.Contract.sdiv_noPoison.sat :
    ∃ (w : Nat) (x y : BitVec w), ¬ IsUB (Val.sdiv (some x) (some y)) :=
  ⟨1, 0#1, 1#1, fun hu => absurd ((sdiv_isUB_iff 0#1 1#1 false).1 hu) (by decide)⟩

theorem IRLean.Contract.urem_noPoison.drop_h :
    ¬ ∀ {w : Nat} (x y : BitVec w), ∃ r, Val.urem (some x) (some y) = Outcome.ok (some r) := fun h =>
  let ⟨r, hr⟩ := @h 1 0#1 0#1
  not_isUB_ok (some r) (hr ▸ (urem_isUB_iff 0#1 0#1).2 rfl)

theorem IRLean.Contract.urem_noPoison.sat :
    ∃ (w : Nat) (x y : BitVec w), ¬ IsUB (Val.urem (some x) (some y)) :=
  ⟨1, 0#1, 1#1, fun hu => absurd ((urem_isUB_iff 0#1 1#1).1 hu) (by decide)⟩

theorem IRLean.Contract.srem_noPoison.drop_h :
    ¬ ∀ {w : Nat} (x y : BitVec w), ∃ r, Val.srem (some x) (some y) = Outcome.ok (some r) := fun h =>
  let ⟨r, hr⟩ := @h 1 0#1 0#1
  not_isUB_ok (some r) (hr ▸ (srem_isUB_iff 0#1 0#1).2 (.inl rfl))

theorem IRLean.Contract.srem_noPoison.sat :
    ∃ (w : Nat) (x y : BitVec w), ¬ IsUB (Val.srem (some x) (some y)) :=
  ⟨1, 0#1, 1#1, fun hu => absurd ((srem_isUB_iff 0#1 1#1).1 hu) (by decide)⟩

/-! ### A flag only makes poison, given the other side has every flag this side has

Each counterexample adds a flag on the right that the left doesn't have, and gives the operands where the left is a
value and the right is poison. -/

/-- `add i1 1, 1` is `0`, and with `nuw` it's poison. -/
theorem IRLean.Contract.add_onlyPoisons.drop_h1 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nsw' = true → nsw = true) →
      OnlyPoisons₂ (w := w) (Val.add · · nuw nsw) (Val.add · · nuw' nsw') :=
  fun h => absurd (@h 1 false false true false id (some 1#1) (some 1#1) 0#1 (by decide)) (by decide)

/-- `add i1 -1, -1` is `0`, and with `nsw` it's poison. -/
theorem IRLean.Contract.add_onlyPoisons.drop_h2 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nuw' = true → nuw = true) →
      OnlyPoisons₂ (w := w) (Val.add · · nuw nsw) (Val.add · · nuw' nsw') :=
  fun h => absurd (@h 1 false false false true id (some 1#1) (some 1#1) 0#1 (by decide)) (by decide)

theorem IRLean.Contract.add_onlyPoisons.sat :
    ∃ (_ : Nat) (nuw nsw nuw' nsw' : Bool), (nuw' = true → nuw = true) ∧ (nsw' = true → nsw = true) :=
  ⟨0, false, false, false, false, id, id⟩

/-- `sub i1 0, 1` is `1`, and with `nuw` it's poison. -/
theorem IRLean.Contract.sub_onlyPoisons.drop_h1 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nsw' = true → nsw = true) →
      OnlyPoisons₂ (w := w) (Val.sub · · nuw nsw) (Val.sub · · nuw' nsw') :=
  fun h => absurd (@h 1 false false true false id (some 0#1) (some 1#1) 1#1 (by decide)) (by decide)

/-- `sub i1 0, -1` is `1`, which doesn't fit, so with `nsw` it's poison. -/
theorem IRLean.Contract.sub_onlyPoisons.drop_h2 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nuw' = true → nuw = true) →
      OnlyPoisons₂ (w := w) (Val.sub · · nuw nsw) (Val.sub · · nuw' nsw') :=
  fun h => absurd (@h 1 false false false true id (some 0#1) (some 1#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.sub_onlyPoisons.sat :
    ∃ (_ : Nat) (nuw nsw nuw' nsw' : Bool), (nuw' = true → nuw = true) ∧ (nsw' = true → nsw = true) :=
  ⟨0, false, false, false, false, id, id⟩

/-- `mul i2 2, 2` is `0`, and overflows both ways. -/
theorem IRLean.Contract.mul_onlyPoisons.drop_h1 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nsw' = true → nsw = true) →
      OnlyPoisons₂ (w := w) (Val.mul · · nuw nsw) (Val.mul · · nuw' nsw') :=
  fun h => absurd (@h 2 false false true false id (some 2#2) (some 2#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.mul_onlyPoisons.drop_h2 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nuw' = true → nuw = true) →
      OnlyPoisons₂ (w := w) (Val.mul · · nuw nsw) (Val.mul · · nuw' nsw') :=
  fun h => absurd (@h 2 false false false true id (some 2#2) (some 2#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.mul_onlyPoisons.sat :
    ∃ (_ : Nat) (nuw nsw nuw' nsw' : Bool), (nuw' = true → nuw = true) ∧ (nsw' = true → nsw = true) :=
  ⟨0, false, false, false, false, id, id⟩

/-- `shl i2 2, 1` is `0`, and loses a bit both ways. -/
theorem IRLean.Contract.shl_onlyPoisons.drop_h1 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nsw' = true → nsw = true) →
      OnlyPoisons₂ (w := w) (Val.shl · · nuw nsw) (Val.shl · · nuw' nsw') :=
  fun h => absurd (@h 2 false false true false id (some 2#2) (some 1#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.shl_onlyPoisons.drop_h2 :
    ¬ ∀ {w : Nat} {nuw nsw nuw' nsw' : Bool}, (nuw' = true → nuw = true) →
      OnlyPoisons₂ (w := w) (Val.shl · · nuw nsw) (Val.shl · · nuw' nsw') :=
  fun h => absurd (@h 2 false false false true id (some 2#2) (some 1#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.shl_onlyPoisons.sat :
    ∃ (_ : Nat) (nuw nsw nuw' nsw' : Bool), (nuw' = true → nuw = true) ∧ (nsw' = true → nsw = true) :=
  ⟨0, false, false, false, false, id, id⟩

/-- `lshr i2 1, 1` is `0`, and loses a bit, so with `exact` it's poison. -/
theorem IRLean.Contract.lshr_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {exact exact' : Bool}, OnlyPoisons₂ (w := w) (Val.lshr · · exact) (Val.lshr · · exact') :=
  fun h => absurd (@h 2 false true (some 1#2) (some 1#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.lshr_onlyPoisons.sat : ∃ (_ : Nat) (exact exact' : Bool), exact' = true → exact = true :=
  ⟨0, false, false, id⟩

theorem IRLean.Contract.ashr_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {exact exact' : Bool}, OnlyPoisons₂ (w := w) (Val.ashr · · exact) (Val.ashr · · exact') :=
  fun h => absurd (@h 2 false true (some 1#2) (some 1#2) 0#2 (by decide)) (by decide)

theorem IRLean.Contract.ashr_onlyPoisons.sat : ∃ (_ : Nat) (exact exact' : Bool), exact' = true → exact = true :=
  ⟨0, false, false, id⟩

/-- `or i1 1, 1` is `1`, and its operands share a bit, so with `disjoint` it's poison. -/
theorem IRLean.Contract.or_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {disjoint disjoint' : Bool}, OnlyPoisons₂ (w := w) (Val.or · · disjoint) (Val.or · · disjoint') :=
  fun h => absurd (@h 1 false true (some 1#1) (some 1#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.or_onlyPoisons.sat :
    ∃ (_ : Nat) (disjoint disjoint' : Bool), disjoint' = true → disjoint = true :=
  ⟨0, false, false, id⟩

/-- `0` and `-1` in `i1` have different signs, so with `samesign` any comparison of them is poison. -/
theorem IRLean.Contract.icmp_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} (p : BitVec w → BitVec w → Bool) {samesign samesign' : Bool},
      OnlyPoisons₂ (w := w) (Val.icmp p · · samesign) (Val.icmp p · · samesign') :=
  fun h => absurd (@h 1 (fun _ _ => true) false true (some 0#1) (some 1#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.icmp_onlyPoisons.sat :
    ∃ (w : Nat) (_ : BitVec w → BitVec w → Bool) (samesign samesign' : Bool), samesign' = true → samesign = true :=
  ⟨0, fun _ _ => true, false, false, id⟩

/-- `-1` in `i1` is negative, so with `nneg` extending it is poison. -/
theorem IRLean.Contract.zext_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} (v : Nat) {nneg nneg' : Bool}, OnlyPoisons₁ (w := w) (Val.zext v · nneg) (Val.zext v · nneg') :=
  fun h => absurd (@h 1 2 false true (some 1#1) 1#2 (by decide)) (by decide)

theorem IRLean.Contract.zext_onlyPoisons.sat : ∃ (_ _ : Nat) (nneg nneg' : Bool), nneg' = true → nneg = true :=
  ⟨0, 0, false, false, id⟩

/-- `2` in `i2` doesn't fit in `i1` unsigned. -/
theorem IRLean.Contract.trunc_onlyPoisons.drop_h1 :
    ¬ ∀ {w : Nat} (v : Nat) {nuw nsw nuw' nsw' : Bool}, (nsw' = true → nsw = true) →
      OnlyPoisons₁ (w := w) (Val.trunc v · nuw nsw) (Val.trunc v · nuw' nsw') :=
  fun h => absurd (@h 2 1 false false true false id (some 2#2) 0#1 (by decide)) (by decide)

/-- `1` in `i2` doesn't fit in `i1` signed, where `1` is `-1`. -/
theorem IRLean.Contract.trunc_onlyPoisons.drop_h2 :
    ¬ ∀ {w : Nat} (v : Nat) {nuw nsw nuw' nsw' : Bool}, (nuw' = true → nuw = true) →
      OnlyPoisons₁ (w := w) (Val.trunc v · nuw nsw) (Val.trunc v · nuw' nsw') :=
  fun h => absurd (@h 2 1 false false false true id (some 1#2) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.trunc_onlyPoisons.sat :
    ∃ (_ _ : Nat) (nuw nsw nuw' nsw' : Bool), (nuw' = true → nuw = true) ∧ (nsw' = true → nsw = true) :=
  ⟨0, 0, false, false, false, false, id, id⟩

/-- `abs i1 -1` is `-1`, the minimum, so with `int_min_poison` it's poison. -/
theorem IRLean.Contract.abs_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {p p' : Bool}, OnlyPoisons₁ (w := w) (Val.abs · p) (Val.abs · p') :=
  fun h => absurd (@h 1 false true (some 1#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.abs_onlyPoisons.sat : ∃ (_ : Nat) (p p' : Bool), p' = true → p = true :=
  ⟨0, false, false, id⟩

/-- `ctlz i1 0` is `1`, and with `is_zero_poison` it's poison. -/
theorem IRLean.Contract.ctlz_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {p p' : Bool}, OnlyPoisons₁ (w := w) (Val.ctlz · p) (Val.ctlz · p') :=
  fun h => absurd (@h 1 false true (some 0#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.ctlz_onlyPoisons.sat : ∃ (_ : Nat) (p p' : Bool), p' = true → p = true :=
  ⟨0, false, false, id⟩

theorem IRLean.Contract.cttz_onlyPoisons.drop_h :
    ¬ ∀ {w : Nat} {p p' : Bool}, OnlyPoisons₁ (w := w) (Val.cttz · p) (Val.cttz · p') :=
  fun h => absurd (@h 1 false true (some 0#1) 1#1 (by decide)) (by decide)

theorem IRLean.Contract.cttz_onlyPoisons.sat : ∃ (_ : Nat) (p p' : Bool), p' = true → p = true :=
  ⟨0, false, false, id⟩

end LemmaStore.Counter
