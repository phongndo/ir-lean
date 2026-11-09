import IRLean.Int

/-! # Contracts for poison, flags and undefined behavior in integer operations

LangRef states a few rules once for every instruction. This states them once as Lean predicates, and proves the model's
integer operations meet them at every width. `docs/llvm-semantic-contracts.md` says where each comes from, what it
covers, and what it leaves out. Nothing here changes the model, and `IRLean.lean` doesn't import it.

LangRef here is `llvm/docs/LangRef.md` at llvmorg-23.1.3, the `LLVM_PROJECT_SRC` of the dev shell, with sha256
`d05da7672c07beb53a01d77361b2c1a96f4fbd46aa30893cc40542a8a7c1ab2b`.

- `Strict₁`, `Strict₂`: poison in, poison out. Poison Values: "Most instructions return '`poison`' when one of their
  arguments is '`poison`'."
- `NoPoison₁`, `NoPoison₂`: without flags, values give a value. Each operation's Semantics section gives a value, and
  poison only through a flag, an argument like `is_zero_poison`, or a shift amount at least the width.
- `OnlyPoisons₁`, `OnlyPoisons₂`, `OnlyPoisonsUB`: a poison-generating flag only turns a result into poison, never into
  another value, and never into undefined behavior. Each flag's own section says so: "If the `nuw` keyword is present,
  the result value of the `add` is a poison value if unsigned overflow occurs."
- `PoisonUB`: poison in a position some value makes undefined is undefined, and otherwise gives poison. Poison Values:
  "immediate undefined behavior occurs if a poison value is used as an instruction operand that has any values that
  trigger undefined behavior". The other direction, that poison isn't undefined where no value is, is the first rule.

`tests/opcheck.py` checks each operation against Alive2 at small widths. These hold at every width, and say which rule
each result follows. -/

namespace IRLean.Contract

open IRLean

/-- Immediate undefined behavior, for any reason. -/
def IsUB {α : Type} (o : Outcome α) : Prop := ∃ r, o = Outcome.ub r

/-- Gives an answer: undefined, or a result. Never a model stop, and always finishes. -/
def Answers {α : Type} (o : Outcome α) : Prop := IsUB o ∨ ∃ x, o = Outcome.ok x

theorem not_isUB_ok {α : Type} (x : α) : ¬ IsUB (Outcome.ok x) := by
  rintro ⟨r, h⟩
  simp [Outcome.ok, Outcome.ub] at h

theorem isUB_ub {α : Type} (r : UB) : IsUB (Outcome.ub r : Outcome α) := ⟨r, rfl⟩

/-! ### The contracts -/

/-- Poison in gives poison. -/
def Strict₁ (f : Val w → Val v) : Prop := f none = none

/-- Poison in either operand gives poison. -/
structure Strict₂ (f : Val w → Val u → Val v) : Prop where
  left : ∀ b, f none b = none
  right : ∀ a, f a none = none

/-- Values in give a value: the operation adds no poison of its own. -/
def NoPoison₁ (f : Val w → Val v) : Prop := ∀ x, ∃ r, f (some x) = some r

/-- The same, for two operands. -/
def NoPoison₂ (f : Val w → Val u → Val v) : Prop := ∀ x y, ∃ r, f (some x) (some y) = some r

/-- `f` is `g` with flags that can only make the result poison: wherever `f` gives a value, `g` gives the same one. -/
def OnlyPoisons₁ (f g : Val w → Val v) : Prop := ∀ a x, f a = some x → g a = some x

/-- The same, for two operands. -/
def OnlyPoisons₂ (f g : Val w → Val u → Val v) : Prop := ∀ a b x, f a b = some x → g a b = some x

/-- The same, for an operation that can be undefined: the flags don't change when it is, and wherever `f` returns a
value, `g` returns the same one. -/
structure OnlyPoisonsUB (f g : Val w → Val w → Outcome (Val w)) : Prop where
  ub : ∀ a b, IsUB (f a b) ↔ IsUB (g a b)
  value : ∀ a b x, f a b = Outcome.ok (some x) → g a b = Outcome.ok (some x)

/-- LangRef's rule for poison operands of an operation that can be undefined. Poison in a position is undefined
exactly when some value in that position would be, and otherwise the result is poison. -/
structure PoisonUB (f : Val w → Val w → Outcome (Val w)) : Prop where
  left : ∀ b, IsUB (f none b) ↔ ∃ x, IsUB (f (some x) b)
  right : ∀ a, IsUB (f a none) ↔ ∃ y, IsUB (f a (some y))
  leftPoison : ∀ b, ¬ IsUB (f none b) → f none b = Outcome.ok none
  rightPoison : ∀ a, ¬ IsUB (f a none) → f a none = Outcome.ok none

/-! ### Division: which values are undefined -/

section Division

variable {w : Nat} (x y : BitVec w) (exact : Bool)

theorem udiv_isUB_iff : IsUB (Val.udiv (some x) (some y) exact) ↔ y = 0#w := by
  by_cases h : y = 0#w
  · subst h; simp [Val.udiv, isUB_ub]
  · simp [Val.udiv, h, not_isUB_ok]

theorem urem_isUB_iff : IsUB (Val.urem (some x) (some y)) ↔ y = 0#w := by
  by_cases h : y = 0#w
  · subst h; simp [Val.urem, isUB_ub]
  · simp [Val.urem, h, not_isUB_ok]

/-- Signed division is undefined for a zero divisor, and for the one quotient that doesn't fit: the minimum divided by
minus one. -/
theorem sdiv_isUB_iff :
    IsUB (Val.sdiv (some x) (some y) exact) ↔ y = 0#w ∨ (x = BitVec.intMin w ∧ y = BitVec.allOnes w) := by
  have ho := BitVec.sdivOverflow_eq x y
  simp only [Val.sdiv, Val.divOverflows]
  by_cases h : y = 0#w
  · simp [h, isUB_ub]
  · have hc : (y == 0#w) = false := by simpa using h
    simp only [hc, Bool.false_eq_true, ite_false, ho]
    by_cases hw : 0 < w
    · by_cases hxy : x = BitVec.intMin w ∧ y = BitVec.allOnes w
      · have hd : (decide (0 < w) && decide (x = BitVec.intMin w) && decide (y = BitVec.allOnes w)) = true := by
          simp [hw, hxy]
        simp only [hd, ite_true]
        exact iff_of_true (isUB_ub _) (.inr hxy)
      · have hd : (decide (0 < w) && decide (x = BitVec.intMin w) && decide (y = BitVec.allOnes w)) = false := by
          simpa [hw] using hxy
        simp only [hd, Bool.false_eq_true, ite_false]
        exact iff_of_false (not_isUB_ok _) (by simp [h, hxy])
    · have : w = 0 := by omega
      subst this
      exact absurd BitVec.of_length_zero h

theorem srem_isUB_iff :
    IsUB (Val.srem (some x) (some y)) ↔ y = 0#w ∨ (x = BitVec.intMin w ∧ y = BitVec.allOnes w) := by
  have ho := BitVec.sdivOverflow_eq x y
  simp only [Val.srem, Val.divOverflows]
  by_cases h : y = 0#w
  · simp [h, isUB_ub]
  · have hc : (y == 0#w) = false := by simpa using h
    simp only [hc, Bool.false_eq_true, ite_false, ho]
    by_cases hw : 0 < w
    · by_cases hxy : x = BitVec.intMin w ∧ y = BitVec.allOnes w
      · have hd : (decide (0 < w) && decide (x = BitVec.intMin w) && decide (y = BitVec.allOnes w)) = true := by
          simp [hw, hxy]
        simp only [hd, ite_true]
        exact iff_of_true (isUB_ub _) (.inr hxy)
      · have hd : (decide (0 < w) && decide (x = BitVec.intMin w) && decide (y = BitVec.allOnes w)) = false := by
          simpa [hw] using hxy
        simp only [hd, Bool.false_eq_true, ite_false]
        exact iff_of_false (not_isUB_ok _) (by simp [h, hxy])
    · have : w = 0 := by omega
      subst this
      exact absurd BitVec.of_length_zero h

end Division

/-! ### Division meets `PoisonUB`

A poison divisor is undefined, since zero is. A poison dividend is undefined for a signed division by minus one, since
the minimum is, and otherwise gives poison. -/

/-- What a division does on a poison dividend, by divisor. -/
private theorem poison_dividend {f : Val w → Val w → Outcome (Val w)}
    (hnone : ∀ a, IsUB (f a none))
    (hval : ∀ y, (IsUB (f none (some y)) ↔ ∃ x, IsUB (f (some x) (some y))) ∧
      (¬ IsUB (f none (some y)) → f none (some y) = Outcome.ok none))
    (hzero : ∀ a, IsUB (f a (some 0#w))) : PoisonUB f where
  left b := by
    cases b with
    | none => exact iff_of_true (hnone none) ⟨0#w, hnone _⟩
    | some y => exact (hval y).1
  right a := iff_of_true (hnone a) ⟨0#w, hzero a⟩
  leftPoison b := by
    cases b with
    | none => exact fun h => absurd (hnone none) h
    | some y => exact (hval y).2
  rightPoison a h := absurd (hnone a) h

theorem udiv_poisonUB (exact : Bool) : PoisonUB (w := w) (Val.udiv · · exact) :=
  poison_dividend (fun _ => ⟨_, rfl⟩)
    (fun y => by
      by_cases h : y = 0#w
      · subst h; exact ⟨iff_of_true (isUB_ub _) ⟨0#w, isUB_ub _⟩, fun hn => absurd (isUB_ub _) hn⟩
      · refine ⟨iff_of_false ?_ ?_, fun _ => ?_⟩
        · simp [Val.udiv, h, not_isUB_ok]
        · rintro ⟨x, hx⟩; exact h ((udiv_isUB_iff x y exact).1 hx)
        · simp [Val.udiv, h])
    (fun a => by cases a <;> simp [Val.udiv, isUB_ub])

theorem urem_poisonUB : PoisonUB (w := w) Val.urem :=
  poison_dividend (fun _ => ⟨_, rfl⟩)
    (fun y => by
      by_cases h : y = 0#w
      · subst h; exact ⟨iff_of_true (isUB_ub _) ⟨0#w, isUB_ub _⟩, fun hn => absurd (isUB_ub _) hn⟩
      · refine ⟨iff_of_false ?_ ?_, fun _ => ?_⟩
        · simp [Val.urem, h, not_isUB_ok]
        · rintro ⟨x, hx⟩; exact h ((urem_isUB_iff x y).1 hx)
        · simp [Val.urem, h])
    (fun a => by cases a <;> simp [Val.urem, isUB_ub])

theorem sdiv_poisonUB (exact : Bool) : PoisonUB (w := w) (Val.sdiv · · exact) :=
  poison_dividend (fun _ => ⟨_, rfl⟩)
    (fun y => by
      by_cases h : y = 0#w
      · subst h; exact ⟨iff_of_true (isUB_ub _) ⟨0#w, isUB_ub _⟩, fun hn => absurd (isUB_ub _) hn⟩
      · have some_iff : (∃ x, IsUB (Val.sdiv (some x) (some y) exact)) ↔ y = BitVec.allOnes w := by
          simp only [sdiv_isUB_iff, h, false_or]
          exact ⟨fun ⟨_, _, hy⟩ => hy, fun hy => ⟨_, rfl, hy⟩⟩
        by_cases hy : y = BitVec.allOnes w
        · have : IsUB (Val.sdiv none (some y) exact) := by
            have hc : (y == 0#w) = false := by simpa using h
            have hd : Val.divOverflows none y = true := by simp [Val.divOverflows, hy]
            simp only [Val.sdiv, hc, hd, Bool.false_eq_true, ite_false, ite_true]
            exact isUB_ub _
          exact ⟨iff_of_true this (some_iff.2 hy), fun hn => absurd this hn⟩
        · have : Val.sdiv none (some y) exact = Outcome.ok none := by
            simp [Val.sdiv, Val.divOverflows, h, hy]
          rw [this, some_iff]
          exact ⟨iff_of_false (not_isUB_ok _) hy, fun _ => rfl⟩)
    (fun a => by cases a <;> simp [Val.sdiv, isUB_ub])

theorem srem_poisonUB : PoisonUB (w := w) Val.srem :=
  poison_dividend (fun _ => ⟨_, rfl⟩)
    (fun y => by
      by_cases h : y = 0#w
      · subst h; exact ⟨iff_of_true (isUB_ub _) ⟨0#w, isUB_ub _⟩, fun hn => absurd (isUB_ub _) hn⟩
      · have some_iff : (∃ x, IsUB (Val.srem (some x) (some y))) ↔ y = BitVec.allOnes w := by
          simp only [srem_isUB_iff, h, false_or]
          exact ⟨fun ⟨_, _, hy⟩ => hy, fun hy => ⟨_, rfl, hy⟩⟩
        by_cases hy : y = BitVec.allOnes w
        · have : IsUB (Val.srem none (some y)) := by
            have hc : (y == 0#w) = false := by simpa using h
            have hd : Val.divOverflows none y = true := by simp [Val.divOverflows, hy]
            simp only [Val.srem, hc, hd, Bool.false_eq_true, ite_false, ite_true]
            exact isUB_ub _
          exact ⟨iff_of_true this (some_iff.2 hy), fun hn => absurd this hn⟩
        · have : Val.srem none (some y) = Outcome.ok none := by
            simp [Val.srem, Val.divOverflows, h, hy]
          rw [this, some_iff]
          exact ⟨iff_of_false (not_isUB_ok _) hy, fun _ => rfl⟩)
    (fun a => by cases a <;> simp [Val.srem, isUB_ub])

/-- Division always gives an answer: undefined, or a result. -/
theorem udiv_answers (a b : Val w) (exact : Bool) : Answers (Val.udiv a b exact) := by
  unfold Answers IsUB
  cases b with
  | none => exact .inl ⟨_, rfl⟩
  | some y =>
    simp only [Val.udiv]
    split
    · exact .inl ⟨_, rfl⟩
    · cases a <;> exact .inr ⟨_, rfl⟩

theorem sdiv_answers (a b : Val w) (exact : Bool) : Answers (Val.sdiv a b exact) := by
  unfold Answers IsUB
  cases b with
  | none => exact .inl ⟨_, rfl⟩
  | some y =>
    simp only [Val.sdiv]
    split
    · exact .inl ⟨_, rfl⟩
    · split
      · exact .inl ⟨_, rfl⟩
      · cases a <;> exact .inr ⟨_, rfl⟩

theorem urem_answers (a b : Val w) : Answers (Val.urem a b) := by
  unfold Answers IsUB
  cases b with
  | none => exact .inl ⟨_, rfl⟩
  | some y =>
    simp only [Val.urem]
    split
    · exact .inl ⟨_, rfl⟩
    · cases a <;> exact .inr ⟨_, rfl⟩

theorem srem_answers (a b : Val w) : Answers (Val.srem a b) := by
  unfold Answers IsUB
  cases b with
  | none => exact .inl ⟨_, rfl⟩
  | some y =>
    simp only [Val.srem]
    split
    · exact .inl ⟨_, rfl⟩
    · split
      · exact .inl ⟨_, rfl⟩
      · cases a <;> exact .inr ⟨_, rfl⟩

/-! ### `exact` on division only makes poison -/

theorem udiv_exact_onlyPoisons (exact : Bool) :
    OnlyPoisonsUB (w := w) (Val.udiv · · exact) (Val.udiv · · false) where
  ub a b := by
    cases b with
    | none => simp [Val.udiv]
    | some y =>
      by_cases h : y = 0#w
      · simp [Val.udiv, h]
      · cases a <;> simp [Val.udiv, h, not_isUB_ok]
  value a b x hx := by
    cases b with
    | none => simp [Val.udiv, Outcome.ub, Outcome.ok] at hx
    | some y =>
      by_cases h : y = 0#w
      · simp [Val.udiv, h, Outcome.ub, Outcome.ok] at hx
      · cases a with
        | none => simp [Val.udiv, h, Outcome.ok] at hx
        | some a =>
          simp only [Val.udiv, h, beq_iff_eq, ite_false, Outcome.ok, Option.some.injEq, Except.ok.injEq] at hx ⊢
          split at hx
          · simp at hx
          · simpa using hx

theorem sdiv_exact_onlyPoisons (exact : Bool) :
    OnlyPoisonsUB (w := w) (Val.sdiv · · exact) (Val.sdiv · · false) where
  ub a b := by
    cases b with
    | none => simp [Val.sdiv]
    | some y =>
      by_cases h : y = 0#w
      · simp [Val.sdiv, h]
      · by_cases ho : Val.divOverflows a y = true
        · simp [Val.sdiv, h, ho]
        · cases a <;> simp_all [Val.sdiv, not_isUB_ok]
  value a b x hx := by
    cases b with
    | none => simp [Val.sdiv, Outcome.ub, Outcome.ok] at hx
    | some y =>
      by_cases h : y = 0#w
      · simp [Val.sdiv, h, Outcome.ub, Outcome.ok] at hx
      · by_cases ho : Val.divOverflows a y = true
        · simp [Val.sdiv, h, ho, Outcome.ub, Outcome.ok] at hx
        · cases a with
          | none => simp_all [Val.sdiv, Outcome.ok]
          | some a =>
            simp only [Val.sdiv, h, ho, beq_iff_eq, ite_false, Bool.false_eq_true, Outcome.ok, Option.some.injEq,
              Except.ok.injEq] at hx ⊢
            split at hx
            · simp at hx
            · simpa using hx

/-! ### Poison in, poison out -/

section Strict

variable {w : Nat}

theorem add_strict (nuw nsw : Bool) : Strict₂ (w := w) (Val.add · · nuw nsw) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem sub_strict (nuw nsw : Bool) : Strict₂ (w := w) (Val.sub · · nuw nsw) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem mul_strict (nuw nsw : Bool) : Strict₂ (w := w) (Val.mul · · nuw nsw) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem and_strict : Strict₂ (w := w) Val.and :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem xor_strict : Strict₂ (w := w) Val.xor :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem or_strict (disjoint : Bool) : Strict₂ (w := w) (Val.or · · disjoint) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem shl_strict (nuw nsw : Bool) : Strict₂ (w := w) (Val.shl · · nuw nsw) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem lshr_strict (exact : Bool) : Strict₂ (w := w) (Val.lshr · · exact) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem ashr_strict (exact : Bool) : Strict₂ (w := w) (Val.ashr · · exact) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem icmp_strict (p : BitVec w → BitVec w → Bool) (samesign : Bool) :
    Strict₂ (Val.icmp p · · samesign) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem umin_strict : Strict₂ (w := w) Val.umin := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem umax_strict : Strict₂ (w := w) Val.umax := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem smin_strict : Strict₂ (w := w) Val.smin := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem smax_strict : Strict₂ (w := w) Val.smax := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem uaddSat_strict : Strict₂ (w := w) Val.uaddSat := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem usubSat_strict : Strict₂ (w := w) Val.usubSat := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem saddSat_strict : Strict₂ (w := w) Val.saddSat := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem ssubSat_strict : Strict₂ (w := w) Val.ssubSat := ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem ucmp_strict (v : Nat) : Strict₂ (w := w) (Val.ucmp v) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩
theorem scmp_strict (v : Nat) : Strict₂ (w := w) (Val.scmp v) :=
  ⟨fun b => by cases b <;> rfl, fun a => by cases a <;> rfl⟩

theorem fshl_strict (a b c : Val w) (h : a = none ∨ b = none ∨ c = none) : Val.fshl a b c = none := by
  cases a <;> cases b <;> cases c <;> simp_all [Val.fshl]
theorem fshr_strict (a b c : Val w) (h : a = none ∨ b = none ∨ c = none) : Val.fshr a b c = none := by
  cases a <;> cases b <;> cases c <;> simp_all [Val.fshr]

/-- `*.with.overflow` gives poison in both fields. -/
theorem withOverflow_strict (f : BitVec w → BitVec w → BitVec w) (o : BitVec w → BitVec w → Bool) (a b : Val w)
    (h : a = none ∨ b = none) : Val.withOverflow f o a b = (none, none) := by
  cases a <;> cases b <;> simp_all [Val.withOverflow]

theorem zext_strict (v : Nat) (nneg : Bool) : Strict₁ (w := w) (Val.zext v · nneg) := rfl
theorem sext_strict (v : Nat) : Strict₁ (w := w) (Val.sext v) := rfl
theorem trunc_strict (v : Nat) (nuw nsw : Bool) : Strict₁ (w := w) (Val.trunc v · nuw nsw) := rfl
theorem abs_strict (intMinPoison : Bool) : Strict₁ (w := w) (Val.abs · intMinPoison) := rfl
theorem ctpop_strict : Strict₁ (w := w) Val.ctpop := rfl
theorem bitreverse_strict : Strict₁ (w := w) Val.bitreverse := rfl
theorem bswap_strict : Strict₁ (w := w) Val.bswap := rfl
theorem ctlz_strict (zeroPoison : Bool) : Strict₁ (w := w) (Val.ctlz · zeroPoison) := rfl
theorem cttz_strict (zeroPoison : Bool) : Strict₁ (w := w) (Val.cttz · zeroPoison) := rfl
theorem range_strict (lo hi : BitVec w) : Strict₁ (Val.range lo hi) := rfl

end Strict

/-! ### Without flags, values give values

Shifts are left out: LangRef makes a shift by at least the width poison, with or without flags. -/

section NoPoison

variable {w : Nat}

theorem add_noPoison : NoPoison₂ (w := w) (Val.add · ·) := fun x y => ⟨x + y, by simp [Val.add]⟩
theorem sub_noPoison : NoPoison₂ (w := w) (Val.sub · ·) := fun x y => ⟨x - y, by simp [Val.sub]⟩
theorem mul_noPoison : NoPoison₂ (w := w) (Val.mul · ·) := fun x y => ⟨x * y, by simp [Val.mul]⟩
theorem and_noPoison : NoPoison₂ (w := w) Val.and := fun _ _ => ⟨_, rfl⟩
theorem xor_noPoison : NoPoison₂ (w := w) Val.xor := fun _ _ => ⟨_, rfl⟩
theorem or_noPoison : NoPoison₂ (w := w) (Val.or · ·) := fun x y => ⟨x ||| y, by simp [Val.or]⟩
theorem icmp_noPoison (p : BitVec w → BitVec w → Bool) : NoPoison₂ (Val.icmp p · ·) :=
  fun x y => ⟨BitVec.ofBool (p x y), by simp [Val.icmp]⟩
theorem umin_noPoison : NoPoison₂ (w := w) Val.umin := fun _ _ => ⟨_, rfl⟩
theorem umax_noPoison : NoPoison₂ (w := w) Val.umax := fun _ _ => ⟨_, rfl⟩
theorem smin_noPoison : NoPoison₂ (w := w) Val.smin := fun _ _ => ⟨_, rfl⟩
theorem smax_noPoison : NoPoison₂ (w := w) Val.smax := fun _ _ => ⟨_, rfl⟩
theorem uaddSat_noPoison : NoPoison₂ (w := w) Val.uaddSat := fun _ _ => ⟨_, rfl⟩
theorem usubSat_noPoison : NoPoison₂ (w := w) Val.usubSat := fun _ _ => ⟨_, rfl⟩
theorem saddSat_noPoison : NoPoison₂ (w := w) Val.saddSat := fun _ _ => ⟨_, rfl⟩
theorem ssubSat_noPoison : NoPoison₂ (w := w) Val.ssubSat := fun _ _ => ⟨_, rfl⟩
theorem ucmp_noPoison (v : Nat) : NoPoison₂ (w := w) (Val.ucmp v) := fun _ _ => ⟨_, rfl⟩
theorem scmp_noPoison (v : Nat) : NoPoison₂ (w := w) (Val.scmp v) := fun _ _ => ⟨_, rfl⟩
theorem fshl_noPoison (x y s : BitVec w) : ∃ r, Val.fshl (some x) (some y) (some s) = some r := ⟨_, rfl⟩
theorem fshr_noPoison (x y s : BitVec w) : ∃ r, Val.fshr (some x) (some y) (some s) = some r := ⟨_, rfl⟩
theorem withOverflow_noPoison (f : BitVec w → BitVec w → BitVec w) (o : BitVec w → BitVec w → Bool) (x y : BitVec w) :
    ∃ r c, Val.withOverflow f o (some x) (some y) = (some r, some c) := ⟨_, _, rfl⟩

theorem zext_noPoison (v : Nat) : NoPoison₁ (w := w) (Val.zext v ·) := fun x => ⟨x.setWidth v, by simp [Val.zext]⟩
theorem sext_noPoison (v : Nat) : NoPoison₁ (w := w) (Val.sext v) := fun _ => ⟨_, rfl⟩
theorem trunc_noPoison (v : Nat) : NoPoison₁ (w := w) (Val.trunc v ·) := fun x => ⟨x.setWidth v, by simp [Val.trunc]⟩
theorem abs_noPoison : NoPoison₁ (w := w) (Val.abs · false) := fun x => ⟨if x.msb then -x else x, by simp [Val.abs]⟩
theorem ctpop_noPoison : NoPoison₁ (w := w) Val.ctpop := fun _ => ⟨_, rfl⟩
theorem bitreverse_noPoison : NoPoison₁ (w := w) Val.bitreverse := fun _ => ⟨_, rfl⟩
theorem bswap_noPoison : NoPoison₁ (w := w) Val.bswap := fun _ => ⟨_, rfl⟩
theorem ctlz_noPoison : NoPoison₁ (w := w) (Val.ctlz · false) := fun x => ⟨x.clz, by simp [Val.ctlz]⟩
theorem cttz_noPoison : NoPoison₁ (w := w) (Val.cttz · false) := fun x => ⟨x.ctz, by simp [Val.cttz]⟩

/-- Division without `exact`, where it isn't undefined, gives a value. -/
theorem udiv_noPoison (x y : BitVec w) (h : ¬ IsUB (Val.udiv (some x) (some y))) :
    ∃ r, Val.udiv (some x) (some y) = Outcome.ok (some r) := by
  have hy : y ≠ 0#w := fun e => h ((udiv_isUB_iff x y false).2 e)
  exact ⟨_, by simp [Val.udiv, hy]; rfl⟩

theorem sdiv_noPoison (x y : BitVec w) (h : ¬ IsUB (Val.sdiv (some x) (some y))) :
    ∃ r, Val.sdiv (some x) (some y) = Outcome.ok (some r) := by
  rcases sdiv_answers (some x) (some y) false with hu | ⟨r, hr⟩
  · exact absurd hu h
  · refine ⟨x.sdiv y, ?_⟩
    rw [hr]
    revert hr
    simp only [Val.sdiv]
    split
    · simp [Outcome.ub, Outcome.ok]
    · split
      · simp [Outcome.ub, Outcome.ok]
      · simp [Outcome.ok, eq_comm]

theorem urem_noPoison (x y : BitVec w) (h : ¬ IsUB (Val.urem (some x) (some y))) :
    ∃ r, Val.urem (some x) (some y) = Outcome.ok (some r) := by
  have hy : y ≠ 0#w := fun e => h ((urem_isUB_iff x y).2 e)
  exact ⟨_, by simp [Val.urem, hy]; rfl⟩

theorem srem_noPoison (x y : BitVec w) (h : ¬ IsUB (Val.srem (some x) (some y))) :
    ∃ r, Val.srem (some x) (some y) = Outcome.ok (some r) := by
  rcases srem_answers (some x) (some y) with hu | ⟨r, hr⟩
  · exact absurd hu h
  · refine ⟨x.srem y, ?_⟩
    rw [hr]
    revert hr
    simp only [Val.srem]
    split
    · simp [Outcome.ub, Outcome.ok]
    · split
      · simp [Outcome.ub, Outcome.ok]
      · simp [Outcome.ok, eq_comm]

end NoPoison

/-! ### Flags only make poison

Each flag can be dropped, alone or with others, and what was a value stays that value. A hypothesis
`nuw' = true → nuw = true` says the new instruction has no flag the old one didn't. -/

section Flags

variable {w : Nat}

theorem add_onlyPoisons {nuw nsw nuw' nsw' : Bool} (h1 : nuw' = true → nuw = true) (h2 : nsw' = true → nsw = true) :
    OnlyPoisons₂ (w := w) (Val.add · · nuw nsw) (Val.add · · nuw' nsw') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.add, reduceCtorEq] at hx ⊢
  revert hx h1 h2
  cases nuw <;> cases nsw <;> cases nuw' <;> cases nsw' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem sub_onlyPoisons {nuw nsw nuw' nsw' : Bool} (h1 : nuw' = true → nuw = true) (h2 : nsw' = true → nsw = true) :
    OnlyPoisons₂ (w := w) (Val.sub · · nuw nsw) (Val.sub · · nuw' nsw') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.sub, reduceCtorEq] at hx ⊢
  revert hx h1 h2
  cases nuw <;> cases nsw <;> cases nuw' <;> cases nsw' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem mul_onlyPoisons {nuw nsw nuw' nsw' : Bool} (h1 : nuw' = true → nuw = true) (h2 : nsw' = true → nsw = true) :
    OnlyPoisons₂ (w := w) (Val.mul · · nuw nsw) (Val.mul · · nuw' nsw') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.mul, reduceCtorEq] at hx ⊢
  revert hx h1 h2
  cases nuw <;> cases nsw <;> cases nuw' <;> cases nsw' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem shl_onlyPoisons {nuw nsw nuw' nsw' : Bool} (h1 : nuw' = true → nuw = true) (h2 : nsw' = true → nsw = true) :
    OnlyPoisons₂ (w := w) (Val.shl · · nuw nsw) (Val.shl · · nuw' nsw') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.shl, reduceCtorEq] at hx ⊢
  revert hx h1 h2
  cases nuw <;> cases nsw <;> cases nuw' <;> cases nsw' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem lshr_onlyPoisons {exact exact' : Bool} (h : exact' = true → exact = true) :
    OnlyPoisons₂ (w := w) (Val.lshr · · exact) (Val.lshr · · exact') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.lshr, reduceCtorEq] at hx ⊢
  revert hx h
  cases exact <;> cases exact' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem ashr_onlyPoisons {exact exact' : Bool} (h : exact' = true → exact = true) :
    OnlyPoisons₂ (w := w) (Val.ashr · · exact) (Val.ashr · · exact') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.ashr, reduceCtorEq] at hx ⊢
  revert hx h
  cases exact <;> cases exact' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem or_onlyPoisons {disjoint disjoint' : Bool} (h : disjoint' = true → disjoint = true) :
    OnlyPoisons₂ (w := w) (Val.or · · disjoint) (Val.or · · disjoint') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.or, reduceCtorEq] at hx ⊢
  revert hx h
  cases disjoint <;> cases disjoint' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem icmp_onlyPoisons (p : BitVec w → BitVec w → Bool) {samesign samesign' : Bool} (h : samesign' = true → samesign = true) :
    OnlyPoisons₂ (Val.icmp p · · samesign) (Val.icmp p · · samesign') := by
  intro a b x hx
  cases a <;> cases b <;> simp only [Val.icmp, reduceCtorEq] at hx ⊢
  revert hx h
  cases samesign <;> cases samesign' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem zext_onlyPoisons (v : Nat) {nneg nneg' : Bool} (h : nneg' = true → nneg = true) :
    OnlyPoisons₁ (w := w) (Val.zext v · nneg) (Val.zext v · nneg') := by
  intro a x hx
  cases a <;> simp only [Val.zext, reduceCtorEq] at hx ⊢
  revert hx h
  cases nneg <;> cases nneg' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem trunc_onlyPoisons (v : Nat) {nuw nsw nuw' nsw' : Bool} (h1 : nuw' = true → nuw = true) (h2 : nsw' = true → nsw = true) :
    OnlyPoisons₁ (w := w) (Val.trunc v · nuw nsw) (Val.trunc v · nuw' nsw') := by
  intro a x hx
  cases a <;> simp only [Val.trunc, reduceCtorEq] at hx ⊢
  revert hx h1 h2
  cases nuw <;> cases nsw <;> cases nuw' <;> cases nsw' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem abs_onlyPoisons {p p' : Bool} (h : p' = true → p = true) : OnlyPoisons₁ (w := w) (Val.abs · p) (Val.abs · p') := by
  intro a x hx
  cases a <;> simp only [Val.abs, reduceCtorEq] at hx ⊢
  revert hx h
  cases p <;> cases p' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem ctlz_onlyPoisons {p p' : Bool} (h : p' = true → p = true) : OnlyPoisons₁ (w := w) (Val.ctlz · p) (Val.ctlz · p') := by
  intro a x hx
  cases a <;> simp only [Val.ctlz, reduceCtorEq] at hx ⊢
  revert hx h
  cases p <;> cases p' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

theorem cttz_onlyPoisons {p p' : Bool} (h : p' = true → p = true) : OnlyPoisons₁ (w := w) (Val.cttz · p) (Val.cttz · p') := by
  intro a x hx
  cases a <;> simp only [Val.cttz, reduceCtorEq] at hx ⊢
  revert hx h
  cases p <;> cases p' <;> simp <;> (repeat' split) <;> intros <;> subst_vars <;> simp_all

end Flags

/-! ### `select` and `freeze` -/

/-- LangRef, `select`: "If the condition evaluates to `poison`, the instruction returns `poison`." Otherwise only the
chosen arm matters, so poison in the other doesn't reach the result. -/
theorem select_poison [HasPoison α] (t e : α) : select none t e = HasPoison.poison := rfl
theorem select_true [HasPoison α] (t e : α) : select (some 1#1) t e = t := rfl
theorem select_false [HasPoison α] (t e : α) : select (some 0#1) t e = e := rfl

/-- `freeze` of a value is that value, whatever the run chose. LangRef: "Otherwise, this instruction is a no-op and
returns the input argument." -/
theorem freeze_some (n : Nat) (x : BitVec w) : Val.freeze n (some x) = some x := rfl

/-- `freeze` of poison is the value the run chose for it. LangRef: "If the argument is `undef` or `poison`, `freeze`
returns an arbitrary, but fixed, value of type `ty`." -/
theorem freeze_none (n : Nat) : Val.freeze n (none : Val w) = some (BitVec.ofNat w n) := rfl

/-- `freeze` never gives poison. -/
theorem freeze_ne_none (n : Nat) (a : Val w) : ¬ Val.freeze n a = none := by
  cases a <;> simp [Val.freeze]

/-- Every value of the type is one some choice makes of poison, so the model's `freeze` is LangRef's arbitrary value,
not some narrower one. -/
theorem freeze_none_any (x : BitVec w) : ∃ n, Val.freeze n (none : Val w) = some x :=
  ⟨x.toNat, by simp [Val.freeze]⟩

end IRLean.Contract
