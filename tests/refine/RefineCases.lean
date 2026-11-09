import IRLean.Lemmas
import IRLean.Promise
import IRLean.Refine
import IRLean.Vec

/-! The refinement contract's cases, as theorems about `IRLean.Refines`. Rewrites that are right in LLVM refine, and
known-wrong ones provably don't: each `¬ Refines` names the input where the target does what the source doesn't allow.
`tests/refine.sh` builds this with warnings as errors, checks it rests on the standard axioms, and replays it.

The functions are written by hand in the shape ir-lean emits for code without memory, from the model's own operations.
They aren't generated from IR, so these say what the relation does, not what any pass did. -/

namespace RefineCases

open IRLean

/-! ### Right rewrites refine -/

/-- `add i8 %x, 0` to `%x`. -/
def addZeroSrc (x : Val 8) : Outcome (Val 8) := Outcome.ok (Val.add x (some 0#8))
def addZeroTgt (x : Val 8) : Outcome (Val 8) := Outcome.ok x

theorem addZero : Refines addZeroSrc addZeroTgt := by
  intro x
  cases x <;> simp [addZeroSrc, addZeroTgt, Refine.outcome_ok_ok, Val.add, Refine.val_none, Refine.val_some]

/-- Dropping `nuw` refines, though the two aren't equal: the source is poison where the target has a value. -/
def addNuw (x y : Val 8) : Outcome (Val 8) := Outcome.ok (Val.add x y (nuw := true))
def addPlain (x y : Val 8) : Outcome (Val 8) := Outcome.ok (Val.add x y)

theorem dropNuw : Refines addNuw addPlain := by
  intro x y
  rw [addNuw, addPlain, Refine.outcome_ok_ok]
  cases x <;> cases y <;> simp only [Val.add, Bool.true_and, Bool.false_and, Bool.or_false]
  · exact Refine.val_none _
  · exact Refine.val_none _
  · exact Refine.val_none _
  · split
    · exact Refine.val_none _
    · exact Refine.refl_val _

theorem dropNuw_not_eq : addNuw ≠ addPlain := fun h => by
  have := congrFun (congrFun h (some 255#8)) (some 1#8)
  simp [addNuw, addPlain, Val.add, Outcome.ok] at this
  exact absurd this (by decide)

/-- Poison may become a value. -/
theorem poisonToValue : Refines (Outcome.ok (none : Val 8)) (Outcome.ok (some 0#8)) :=
  (Refine.outcome_ok_ok _ _).2 (Refine.val_none _)

/-- Undefined behavior in the source allows anything: `udiv %x, 0` to `%x`. -/
def divZero (x : Val 8) : Outcome (Val 8) := Val.udiv x (some 0#8)

theorem removeUB : Refines divZero addZeroTgt := fun _ => Refine.outcome_ub .divByZero _

/-- A poison lane allows a value there, and the other lane keeps its own. -/
def keepLane0 (v : Vec 2 8) : Outcome (Vec 2 8) := Outcome.ok (Vec.shuffle 2 v v #[some 0, none])
def identity (v : Vec 2 8) : Outcome (Vec 2 8) := Outcome.ok v

theorem poisonLane : Refines keepLane0 identity := by
  intro v
  refine (Refine.outcome_ok_ok _ _).2 fun i => ?_
  match i with
  | ⟨0, _⟩ => simp [Vec.shuffle, Vec.lane]; exact Refine.refl_val _
  | ⟨1, _⟩ => simp [Vec.shuffle]; exact Refine.val_none _

/-! ### Wrong rewrites don't -/

/-- A wrong constant: `add i8 %x, 0` to `add i8 %x, 1`. -/
def addOne (x : Val 8) : Outcome (Val 8) := Outcome.ok (Val.add x (some 1#8))

theorem wrongConstant : ¬ Refines addZeroSrc addOne := fun h => by
  have := (Refine.outcome_ok_ok _ _).1 (h (some 0#8))
  simp [Val.add, Refine.val_some] at this

/-- An added `nuw`: the target is poison where the source has a value. -/
theorem addedNuw : ¬ Refines addPlain addNuw := fun h => by
  have := (Refine.outcome_ok_ok _ _).1 (h (some 255#8) (some 1#8))
  simp [Val.add, Refine.val_some] at this
  exact absurd this (by decide)

/-- Poison where there was a value. -/
theorem valueToPoison : ¬ Refines (Outcome.ok (some 0#8 : Val 8)) (Outcome.ok none) := fun h =>
  nomatch (Refine.val_some _ _).1 ((Refine.outcome_ok_ok _ _).1 h)

/-- `freeze` of poison is a model stop, and a model stop in the source allows nothing: `freeze %x` to `%x` would make
poison of the value `freeze` chose. -/
def frozen (x : Val 8) : Outcome (Val 8) := Val.freeze x

theorem freezeToPoison : ¬ Refines frozen addZeroTgt := fun h =>
  Refine.outcome_stop .freezePoison _ (h none)

/-- Duplicating a `freeze`: one frozen value subtracted from itself is 0, and two `freeze`s of poison may differ. The
two are equal in the model, since both stop at poison, and still don't refine, since the source stops. -/
def freezeOnce (x : Val 8) : Outcome (Val 8) :=
  andThen (Val.freeze x) fun f => Outcome.ok (Val.sub f f)
def freezeTwice (x : Val 8) : Outcome (Val 8) :=
  andThen (Val.freeze x) fun f => andThen (Val.freeze x) fun g => Outcome.ok (Val.sub f g)

theorem freezeDuplicated_eq : freezeOnce = freezeTwice := by
  funext x
  cases x <;> rfl

theorem freezeDuplicated : ¬ Refines freezeOnce freezeTwice := fun h =>
  Refine.outcome_stop .freezePoison _ (h none)

/-- Added undefined behavior: `%x` to a `udiv %x, %x` whose result is unused, undefined at 0. -/
def divSelf (x : Val 8) : Outcome (Val 8) := andThen (Val.udiv x x) fun _ => Outcome.ok x

theorem addedUB : ¬ Refines addZeroTgt divSelf := fun h => by
  obtain ⟨_, hb, _⟩ := h (some 0#8)
  simp [divSelf, Val.udiv, andThen, Outcome.ub] at hb

/-- Swapped lanes. -/
def swapLanes (v : Vec 2 8) : Outcome (Vec 2 8) := Outcome.ok (Vec.shuffle 2 v v #[some 1, some 0])

theorem swappedLanes : ¬ Refines identity swapLanes := fun h => by
  have := (Refine.outcome_ok_ok _ _).1 (h #v[some 0#8, some 1#8]) ⟨0, by decide⟩
  simp [Vec.shuffle, Vec.lane, Refine.val_some] at this

/-- A target that never finishes, for a source that returns. -/
def spin (_ : Val 8) : Outcome (Val 8) := none

theorem spinTarget : ¬ Refines addZeroTgt spin := fun h => by
  obtain ⟨_, hb, _⟩ := h none
  simp [spin] at hb

/-- A source that never finishes needs a target that doesn't either. Under a promise to progress it isn't `none` but
undefined, which allows anything: see `loopDeletedUnderPromise`. -/
theorem spinSource : ¬ Refines spin addZeroTgt := fun h => by
  have : addZeroTgt none = none := h none
  simp [addZeroTgt, Outcome.ok] at this

/-! ### Promises to progress

A loop counting up from 0 by 2 until it reaches `n`, whose result nothing uses, as `loop-deletion` finds it. It never
ends for an odd `n`. In a function marked `mustprogress` that's undefined, so deleting the loop is right, and without
the promise it isn't. Adding the promise is wrong, and dropping it is right. -/

inductive Count where
  | entry (n : Val 8)
  | loop (i n : Val 8)
  | exit

def countStep : Count → Outcome (Next Count (Val 8))
  | .entry n => jump (.loop (some 0#8) n)
  | .loop i n => br (Val.icmpEq i n) .exit (.loop (Val.add i (some 2#8)) n)
  | .exit => ret (some 0#8)

/-- The loop in a function without the promise. -/
def countFree (n : Val 8) : Outcome (Val 8) := noundef n <| run countStep (.entry n)

/-- The same loop in a function marked `mustprogress`, as ir-lean emits it. -/
def countPromised (n : Val 8) : Outcome (Val 8) :=
  noundef n <| promised (run countStep (.entry n)) fun _ => runPromised (fun _ => true) countStep (.entry n)

/-- The loop deleted. -/
def countDeleted (n : Val 8) : Outcome (Val 8) := noundef n <| Outcome.ok (some 0#8)

theorem count_even (n : BitVec 8) (k : Nat) : ∀ i : BitVec 8, i.toNat ≤ n.toNat → n.toNat - i.toNat = 2 * k →
    run countStep (.loop (some i) (some n)) = Outcome.ok (some 0#8) := by
  induction k with
  | zero =>
    intro i hle hk
    have : i = n := BitVec.eq_of_toNat_eq (by omega)
    subst this
    rw [run_jump _ (show countStep _ = jump .exit by simp [countStep, llvm_val, br])]
    exact run_ret _ rfl
  | succ k ih =>
    intro i hle hk
    have hne : i ≠ n := by rintro rfl; omega
    rw [run_jump _ (show countStep _ = jump (.loop (some (i + 2#8)) (some n)) by simp [countStep, llvm_val, hne])]
    have h2 : (i + 2#8).toNat = i.toNat + 2 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := n.isLt; omega
    exact ih _ (by omega) (by omega)

/-- The loop's states for an odd `n`: `i` stays even, so it never reaches `n`. -/
def oddStates (n : BitVec 8) (b : Count) : Prop := ∃ i : BitVec 8, i.toNat % 2 = 0 ∧ b = .loop (some i) (some n)

theorem odd_next (n : BitVec 8) (hn : n.toNat % 2 = 1) :
    ∀ b, oddStates n b → ∃ b', countStep b = jump b' ∧ (fun _ => true) b' = true ∧ oddStates n b' := by
  rintro b ⟨i, hi, rfl⟩
  have hne : i ≠ n := by rintro rfl; omega
  refine ⟨.loop (some (i + 2#8)) (some n), by simp [countStep, llvm_val, hne], rfl, i + 2#8, ?_, rfl⟩
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem count_entry (n : BitVec 8) : countStep (.entry (some n)) = jump (.loop (some 0#8) (some n)) := rfl

theorem countFree_odd (n : BitVec 8) (hn : n.toNat % 2 = 1) : countFree (some n) = none := by
  rw [countFree, noundef_some, run_jump _ (count_entry n)]
  exact run_forever (oddStates n) (fun b hb => let ⟨b', h, _, h'⟩ := odd_next n hn b hb; ⟨b', h, h'⟩) ⟨0#8, rfl, rfl⟩

/-- A promise broken on some inputs: undefined exactly where the loop never ends, and the loop's result elsewhere. -/
theorem countPromised_odd (n : BitVec 8) (hn : n.toNat % 2 = 1) : countPromised (some n) = Outcome.ub .noProgress := by
  have spins : run countStep (.entry (some n)) = none := by
    have := countFree_odd n hn
    rwa [countFree, noundef_some] at this
  rw [countPromised, noundef_some, spins, promised_none, runPromised_jump (count_entry n), runPromised,
    stay_forever (oddStates n) (odd_next n hn) ⟨0#8, rfl, rfl⟩]

theorem countPromised_even (n : BitVec 8) (hn : n.toNat % 2 = 0) : countPromised (some n) = Outcome.ok (some 0#8) := by
  rw [countPromised, noundef_some, run_jump _ (count_entry n),
    count_even n (n.toNat / 2) 0#8 (by simp) (by simp; omega)]
  rfl

theorem countFree_even (n : BitVec 8) (hn : n.toNat % 2 = 0) : countFree (some n) = Outcome.ok (some 0#8) := by
  rw [countFree, noundef_some, run_jump _ (count_entry n), count_even n (n.toNat / 2) 0#8 (by simp) (by simp; omega)]

theorem promiseBrokenOnSomeInput :
    countPromised (some 1#8) = Outcome.ub .noProgress ∧ countPromised (some 2#8) = Outcome.ok (some 0#8) :=
  ⟨countPromised_odd _ (by decide), countPromised_even _ (by decide)⟩

/-- Deleting the loop under the promise: where it never ends, the source is undefined. -/
theorem loopDeletedUnderPromise : Refines countPromised countDeleted := by
  intro n
  cases n with
  | none => exact Refine.outcome_ub _ _
  | some n =>
    by_cases hn : n.toNat % 2 = 0
    · rw [countPromised_even n hn]; exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)
    · rw [countPromised_odd n (by omega)]; exact Refine.outcome_ub _ _

/-- Deleting it without the promise: at `n = 1` the source never finishes, and the target returns. -/
theorem loopDeletedWithoutPromise : ¬ Refines countFree countDeleted := fun h => by
  have h1 := h (some 1#8)
  rw [countFree_odd 1#8 (by decide)] at h1
  have : countDeleted (some 1#8) = none := (Refine.outcome_none _).1 h1
  simp [countDeleted, noundef_some, Outcome.ok] at this

/-- Adding the promise: at `n = 1` the source never finishes, which LLVM allows, and the target is undefined. -/
theorem promiseAdded : ¬ Refines countFree countPromised := fun h => by
  have h1 := h (some 1#8)
  rw [countFree_odd 1#8 (by decide)] at h1
  have : countPromised (some 1#8) = none := (Refine.outcome_none _).1 h1
  rw [countPromised_odd 1#8 (by decide)] at this
  simp [Outcome.ub] at this

/-- Dropping the promise: the target never finishes only where the source is undefined. -/
theorem promiseDropped : Refines countPromised countFree := by
  intro n
  cases n with
  | none => exact Refine.outcome_ub _ _
  | some n =>
    by_cases hn : n.toNat % 2 = 0
    · rw [countPromised_even n hn, countFree_even n hn]; exact (Refine.outcome_ok_ok _ _).2 (Refine.refl_val _)
    · rw [countPromised_odd n (by omega)]; exact Refine.outcome_ub _ _

/-! ### What the model can't certify

Each of these is right in LLVM, and provably not a refinement in the model. That's a limit of the model, not a
counterexample: `¬ Refines` never says a rewrite is wrong in LLVM. -/

/-- Inserting `freeze`: `%x` to `freeze %x`. Right in LLVM, since a frozen poison is some value, which poison allows.
The model stops at `freeze` of poison, and a target that stops refines nothing. -/
theorem freezeInserted : ¬ Refines addZeroTgt frozen := fun h => by
  obtain ⟨_, hb, _⟩ := h none
  simp [frozen, Val.freeze, Outcome.stop] at hb

/-! ### What the model certifies and LLVM doesn't

An argument is a value or poison, never `undef`, so this holds only where no caller passes `undef`. -/

/-- `and i8 %x, 0` to `xor i8 %x, %x`. Both are 0 for a value and poison for poison, so this refines in the model. In
LLVM, `xor` of an `undef` with itself may be any value, where `and` with 0 is 0, so it's wrong there unless `%x` is
`noundef`. `tools/binding.py` refuses a function with such an argument as `undef_argument`. -/
def andZero (x : Val 8) : Outcome (Val 8) := Outcome.ok (Val.and x (some 0#8))
def xorSelf (x : Val 8) : Outcome (Val 8) := Outcome.ok (Val.xor x x)

theorem undefArgument : Refines andZero xorSelf := by
  intro x
  cases x <;> simp [andZero, xorSelf, Refine.outcome_ok_ok, Val.and, Val.xor, Val.map₂, Refine.val_none,
    Refine.val_some]

/-! ### Laws -/

/-- Refinements compose: `add nuw %x, 0` to `add %x, 0` to `%x`. -/
def addZeroNuw (x : Val 8) : Outcome (Val 8) := addNuw x (some 0#8)

theorem dropNuwZero : Refines addZeroNuw addZeroSrc := fun x => dropNuw x (some 0#8)

theorem chain : Refines addZeroNuw addZeroTgt := Refines.trans dropNuwZero addZero

/-- A run refines itself exactly when it never stops the model. -/
theorem addZeroSrc_self : Refines addZeroSrc addZeroSrc :=
  (Refines.self_iff _).2 fun x s => by cases x <;> simp [addZeroSrc, Outcome.ok, Outcome.stop]

theorem frozen_not_self : ¬ Refines frozen frozen := fun h =>
  (Refines.self_iff _).1 h none .freezePoison rfl

/-- The shape of `tools/binding.py`'s `ir_instance_equivalence` claim implies refinement. -/
theorem of_equivalence {src tgt : Val 8 → Outcome (Val 8)} (h : src = tgt)
    (never : ∀ (x : Val 8) (s : ModelStop), src x ≠ some (.error (.model s))) : Refines src tgt :=
  Refines.of_eq h ((Refines.self_iff src).2 never)

/-- A refinement in a context: the rest of a function, if it keeps refinement, keeps one of its parts. -/
def square (r : Val 8) : Outcome (Val 8) := Outcome.ok (Val.mul r r)

theorem inContext (x : Val 8) : Refine.le (andThen (addZeroSrc x) square) (andThen (addZeroTgt x) square) :=
  Refine.andThen_mono (addZero x) fun a b hab =>
    (Refine.outcome_ok_ok _ _).2 (Refine.val_map₂_mono (f := fun a b => Val.mul a b)
      (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) hab hab)

end RefineCases
