import IRLean.Contract.Poison

/-! Tests for `IRLean.Contract.Poison`, run by `tests/contracts.sh`.

The positive half checks LangRef's own examples against the model. The negative half writes down semantics a plausible
change to the model could introduce, each wrong in a way LangRef rules out, and proves the contract rejects it. So a
contract here isn't true of everything, and would catch that change. -/

namespace IRLean.Contract.Test

open IRLean IRLean.Contract

/-! ### LangRef's examples

From the Poison Values section of LangRef, at `i32`. -/

/-- `%poison = sub nuw i32 0, 1`: "Results in a poison value." -/
example : Val.sub (some 0#32) (some 1#32) (nuw := true) = none := by decide
/-- Without the flag it's a value. -/
example : Val.sub (some 0#32) (some 1#32) = some (BitVec.allOnes 32) := by decide
/-- `%poison2 = sub i32 poison, 1`: "Also results in a poison value." -/
example : Val.sub (none : Val 32) (some 1#32) = none := rfl
/-- `%still_poison = and i32 %poison, 0`: "0, but also poison." -/
example : Val.and (none : Val 32) (some 0#32) = none := rfl
/-- `%cmp = icmp slt i32 %poison, 0`: "Returns a poison value." -/
example : Val.icmpSlt (none : Val 32) (some 0#32) = none := rfl
/-- `br i1 %cmp, ...` on poison: "undefined behavior". -/
example : IsUB (br (β := Unit) (ρ := Unit) none () ()) := isUB_ub _

/-! Division, from the `udiv`, `sdiv`, `urem` and `srem` sections and the poison rule. -/

/-- A poison divisor is undefined. -/
example : IsUB (Val.udiv (some 1#32) none) := isUB_ub _
/-- A poison dividend of `udiv` gives poison, since no dividend is undefined. -/
example : Val.udiv (none : Val 32) (some 2#32) = Outcome.ok none := rfl
/-- `sdiv` of the minimum by minus one overflows: "a 32-bit division of -2147483648 by -1". -/
example : IsUB (Val.sdiv (some (BitVec.intMin 32)) (some (BitVec.allOnes 32)))  :=
  (sdiv_isUB_iff _ _ false).2 (.inr ⟨rfl, rfl⟩)
/-- So a poison dividend of a signed division by minus one is undefined, since it could be the minimum. -/
example : IsUB (Val.sdiv (none : Val 32) (some (BitVec.allOnes 32))) :=
  ((sdiv_poisonUB false).left _).2 ⟨_, (sdiv_isUB_iff _ _ false).2 (.inr ⟨rfl, rfl⟩)⟩
/-- And by two it's poison, since no dividend overflows. -/
example : Val.sdiv (none : Val 32) (some 2#32) = Outcome.ok none := rfl
/-- The same for `srem`, which LangRef says is undefined on overflow although the remainder fits. -/
example : IsUB (Val.srem (none : Val 32) (some (BitVec.allOnes 32))) :=
  (srem_poisonUB.left _).2 ⟨_, (srem_isUB_iff _ _).2 (.inr ⟨rfl, rfl⟩)⟩
/-- `exact`: "the result value of the `udiv` is a poison value if `%op1` is not a multiple of `%op2`". -/
example : Val.udiv (some 7#32) (some 2#32) (exact := true) = Outcome.ok none := rfl
example : Val.udiv (some 7#32) (some 2#32) = Outcome.ok (some 3#32) := rfl

/-! `select` and `freeze`. -/

/-- Poison in the arm not chosen doesn't matter. -/
example : select (some 1#1) (some 5#32) (none : Val 32) = some 5#32 := rfl
/-- A poison condition gives poison. -/
example : select (none : Val 1) (some 5#32) (some 5#32) = none := rfl
/-- `freeze poison` is the value the run chose, modulo `2 ^ 32`, and `freeze` of a value is the value. -/
example : Val.freeze 7 (none : Val 32) = some 7#32 := rfl
example : Val.freeze (2 ^ 32 + 7) (none : Val 32) = some 7#32 := rfl
example : Val.freeze 7 (some 5#32) = some 5#32 := rfl
/-- Every value is one some choice gives. -/
example : ∃ n, Val.freeze n (none : Val 32) = some 0xdeadbeef#32 := freeze_none_any _

/-! The contracts, used together: dropping `nsw` from `add` keeps any value it had, at `i8`. -/
example (a b : Val 8) (x : BitVec 8) (h : Val.add a b (nsw := true) = some x) : Val.add a b = some x :=
  add_onlyPoisons (nuw := false) (nsw := true) (nuw' := false) (nsw' := false) (fun h => h) (fun _ => rfl) a b x h

/-! ### Semantics the contracts reject -/

/-- `and` where zero absorbs poison: the mistake LangRef's `%still_poison` example is there to rule out. -/
def andAbsorbs (a b : Val w) : Val w :=
  match b with
  | some y => if y == 0#w then some 0#w else Val.and a b
  | none => none

theorem andAbsorbs_not_strict : ¬ Strict₂ (andAbsorbs (w := 8)) := fun h => by
  have := h.left (some 0#8)
  simp [andAbsorbs] at this

/-- `add` without flags that gives poison on unsigned overflow, as if it always had `nuw`. -/
def addAlwaysNuw (a b : Val w) : Val w := Val.add a b (nuw := true)

theorem addAlwaysNuw_poisons : ¬ NoPoison₂ (w := 8) addAlwaysNuw := fun h => by
  obtain ⟨r, hr⟩ := h 255#8 1#8
  have : addAlwaysNuw (some 255#8) (some 1#8) = none := by decide
  rw [this] at hr
  exact absurd hr (by simp)

/-- `add nsw` that saturates on overflow, where LangRef gives poison: a flag changing a value. -/
def addNswSaturates (a b : Val w) : Val w :=
  match a, b with
  | some x, some y => some (if x.saddOverflow y then Val.signedLimit x else x + y)
  | _, _ => none

theorem addNswSaturates_changes_value : ¬ OnlyPoisons₂ (w := 8) addNswSaturates (Val.add · ·) := fun h => by
  have := h (some 127#8) (some 1#8) _ rfl
  revert this
  decide

/-- `sdiv` where a poison dividend is never undefined: less undefined behavior than LangRef, since the minimum
dividend overflows. A refinement whose source used this could certify a target that traps. -/
def sdivLax (a b : Val w) : Outcome (Val w) :=
  match a, b with
  | none, some y => if y == 0#w then Outcome.ub .divByZero else Outcome.ok none
  | _, _ => Val.sdiv a b

theorem sdivLax_not_poisonUB : ¬ PoisonUB (w := 8) sdivLax := fun h => by
  have hub := (h.left (some (BitVec.allOnes 8))).2
    ⟨BitVec.intMin 8, (sdiv_isUB_iff (BitVec.intMin 8) (BitVec.allOnes 8) false).2 (.inr ⟨rfl, rfl⟩)⟩
  have hok : sdivLax (none : Val 8) (some (BitVec.allOnes 8)) = Outcome.ok none := rfl
  rw [hok] at hub
  exact not_isUB_ok _ hub

/-- `udiv` where a poison dividend is always undefined: more undefined behavior than LangRef. A safety proof would be
fine with it, and a refinement whose target used it would reject a correct target. -/
def udivStrict (a b : Val w) : Outcome (Val w) :=
  match a with
  | none => Outcome.ub .divByPoison
  | some _ => Val.udiv a b

theorem udivStrict_not_poisonUB : ¬ PoisonUB (w := 8) udivStrict := fun h => by
  obtain ⟨x, hx⟩ := (h.left (some 1#8)).1 (isUB_ub _)
  have := (udiv_isUB_iff x 1#8 false).1 hx
  revert this
  decide

/-- `udiv` where a poison divisor gives poison, where LangRef lists it as undefined. -/
def udivPoisonDivisor (a b : Val w) : Outcome (Val w) :=
  match b with
  | none => Outcome.ok none
  | some _ => Val.udiv a b

theorem udivPoisonDivisor_not_poisonUB : ¬ PoisonUB (w := 8) udivPoisonDivisor := fun h => by
  have hub := (h.right (some 1#8)).2 ⟨0#8, isUB_ub _⟩
  exact not_isUB_ok _ hub

/-- `exact` that gives undefined behavior instead of poison, as if it were a promise and not a flag. -/
def udivExactTraps (a b : Val w) : Outcome (Val w) :=
  match a, b with
  | some x, some y => if y != 0#w && x % y != 0#w then Outcome.ub .divByZero else Val.udiv a b
  | _, _ => Val.udiv a b

theorem udivExactTraps_not_onlyPoisons : ¬ OnlyPoisonsUB (w := 8) udivExactTraps (Val.udiv · · false) := fun h => by
  have := (h.ub (some 7#8) (some 2#8)).1 (isUB_ub _)
  rw [(udiv_isUB_iff 7#8 2#8 false)] at this
  revert this
  decide

end IRLean.Contract.Test
