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

/-- A source that never finishes needs a target that doesn't either. LLVM would let a `mustprogress` source do
anything here, so this is stricter than LLVM. -/
theorem spinSource : ¬ Refines spin addZeroTgt := fun h => by
  have : addZeroTgt none = none := h none
  simp [addZeroTgt, Outcome.ok] at this

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
