import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.IS.Add
import Peephole.Lemmas.Intrinsic
import IRLean.Contract.Poison

/-! # What the models of InstSimplify's intrinsic folds share

`simplifyCall` hands a call to an intrinsic to `simplifyIntrinsic`, which first folds a call that propagates poison and
has a poison operand, then dispatches on how many operands it has: `simplifyUnaryIntrinsic`,
`simplifyBinaryIntrinsic`, or a case of its own for `fshl` and `fshr`. The calls to integer intrinsics `Term` holds
are the ones these see here:

- `ctpop`, `bitreverse` and `bswap`, of one operand, `Term.un`;
- `abs`, `ctlz` and `cttz`, whose second operand is their flag, an `i1` constant that `Term.un` keeps as a `Bool` and
  that no fold here reads;
- `umin`, `umax`, `smin`, `smax` and the four saturating ones, `Term.bi`;
- `fshl` and `fshr`, `Term.fsh`.

The case for `umin`, `umax`, `smin` and `smax` asks `isICmpTrue`, which calls `simplifyICmpInst`. A model here takes
that call as a parameter, `Recur`, as the arithmetic family's do, and a theorem holds for every `Recur` that's
`Recur.Sound` in the run. `Recur.unknown` answers that the model doesn't say, which is sound, and is what `onInst` runs
with, so the comparison with `opt` never takes an answer the model didn't compute.

A fold that returns another's answer whole, as `return simplifyUnaryIntrinsic(...)`, has the step `tail (g.steps ...)`.
One that returns it only when there is one, as `if (Value *V = g(...)) return V;`, has the step
`forward (g.steps ...)`. Both fire what `g` fires, under `g`'s site, so a rewrite keeps its own ID. -/

namespace Peephole.IS.Intrinsic

open IRLean

variable {w : Nat}

/-- `RecursionLimit` in `InstructionSimplify.cpp`: the `MaxRecurse` an instruction starts with, and what
`simplifyBinaryIntrinsic` passes `isICmpTrue`. -/
def recursionLimit : Nat := 3

/-! ### Recursive calls -/

/-- What a recursive call answers: a value, `nullptr`, or what the model doesn't say. InstSimplify builds no
instruction, so a value it answers is one that exists, or a constant: a `Term`. -/
inductive Ans (w : Nat) where
  | val (t : Term w)
  | null
  | unknown

/-- The recursive calls into InstSimplify these folds make, with their `MaxRecurse` first. -/
structure Recur where
  /-- `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse)`. -/
  icmp : Nat → {w : Nat} → Pred → Term w → Term w → Ans 1

/-- Every value a `Recur` answers is right in the run `ρ`: for operands consistent with it and with no `undef`, the
answer refines the comparison, which has no `samesign`. -/
structure Recur.Sound (r : Recur) (ρ : Env) : Prop where
  icmp : ∀ (n : Nat) {w : Nat} (p : Pred) (a b : Term w) (t : Term 1), r.icmp n p a b = .val t →
    a.Consistent ρ → b.Consistent ρ → a.hasUndef = false → b.hasUndef = false →
    Refines (p.eval (a.denote ρ) (b.denote ρ) false) (t.denote ρ)

/-- The calls the model doesn't say anything about. -/
def Recur.unknown : Recur where
  icmp _ _ _ _ _ := .unknown

theorem Recur.unknown_sound (ρ : Env) : Recur.unknown.Sound ρ where
  icmp _ _ _ _ _ _ h := by simp [Recur.unknown] at h

/-- `isICmpTrue(Pred, LHS, RHS, Q, MaxRecurse)`: whether `simplifyICmpInst` answers a constant with every bit set,
`dyn_cast_or_null<Constant>(V)` and `C->isAllOnesValue()`. `none` where the `Recur` doesn't say. -/
def isICmpTrue (r : Recur) (n : Nat) (p : Pred) (a b : Term w) : Option Bool :=
  match r.icmp n p a b with
  | .val t => some (allOnes t)
  | .null => some false
  | .unknown => none

/-- A comparison of two values, with no `samesign`, is a value. -/
theorem pred_eval_some (p : Pred) (x y : BitVec w) : ∃ v, p.eval (some x) (some y) false = some v := by
  cases p <;> exact ⟨_, rfl⟩

/-- When `isICmpTrue` says yes, the comparison holds of the operands' values, if they aren't poison. -/
theorem isICmpTrue_sound {r : Recur} {ρ : Env} (hr : r.Sound ρ) {n : Nat} {p : Pred} {a b : Term w}
    (h : isICmpTrue r n p a b = some true) (ca : a.Consistent ρ) (cb : b.Consistent ρ)
    (ua : a.hasUndef = false) (ub : b.hasUndef = false) {x y : BitVec w} (hx : a.denote ρ = some x)
    (hy : b.denote ρ = some y) : p.eval (some x) (some y) false = some 1#1 := by
  unfold isICmpTrue at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq] at h
    have href := hr.icmp n p a b t ht ca cb ua ub
    rw [hx, hy, cst_eq h] at href
    obtain ⟨v, hv⟩ := pred_eval_some p x y
    rw [hv] at href ⊢
    exact href.symm
  · simp at h
  · simp at h

/-! ### Forwarding to a fold modelled here -/

/-- `if (Value *V = g(...)) return V;`, as one step: what `g`'s first step that doesn't fall through does, with a
decline falling through instead. -/
def forward : List (Step w) → Step w
  | [] => .next
  | .next :: rest => forward rest
  | .fire s r :: _ => .fire s r
  | .decline :: _ => .next
  | .delegate c :: _ => .delegate c

theorem forward_fire {steps : List (Step w)} {s : String} {r : Repl w} (h : forward steps = .fire s r) :
    Step.fire s r ∈ steps := by
  induction steps with
  | nil => simp [forward] at h
  | cons st rest ih =>
    cases st with
    | next => exact List.mem_cons_of_mem _ (ih h)
    | fire s' r' =>
      simp only [forward, Step.fire.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.mem_cons_self
    | decline => simp [forward] at h
    | delegate c => simp [forward] at h

/-- `return g(...);`, as one step: what `g` answers, `nullptr` included. -/
def tail (steps : List (Step w)) : Step w :=
  match forward steps with
  | .next => .decline
  | s => s

theorem tail_fire {steps : List (Step w)} {s : String} {r : Repl w} (h : tail steps = .fire s r) :
    Step.fire s r ∈ steps := by
  unfold tail at h
  split at h
  · cases h
  · exact forward_fire h

/-! ### The intrinsics' operands and poison -/

theorem un_eval (ρ : Env) (f : UnIntr) (a : Term w) :
    (Repl.un f (.old a)).eval ρ = Outcome.ok (f.eval (a.denote ρ)) := rfl

theorem bi_eval (ρ : Env) (f : BinIntr) (a b : Term w) :
    (Repl.bi f (.old a) (.old b)).eval ρ = Outcome.ok (f.eval (a.denote ρ) (b.denote ρ)) := rfl

theorem fsh_eval (ρ : Env) (l : Bool) (a b c : Term w) :
    (Repl.fsh l (.old a) (.old b) (.old c)).eval ρ =
      Outcome.ok ((if l then Val.fshl else Val.fshr) (a.denote ρ) (b.denote ρ) (c.denote ρ)) := rfl

/-- Each intrinsic of one operand gives poison for poison, as LangRef has it: `IRLean.Contract`'s `_strict`. -/
theorem UnIntr.eval_none (f : UnIntr) : f.eval (none : Val w) = none := by
  cases f with
  | ctpop => exact Contract.ctpop_strict
  | bitreverse => exact Contract.bitreverse_strict
  | bswap => exact Contract.bswap_strict
  | ctlz z => exact Contract.ctlz_strict z
  | cttz z => exact Contract.cttz_strict z
  | abs p => exact Contract.abs_strict p

/-- Each intrinsic of two operands gives poison if either is. -/
theorem BinIntr.eval_none_left (f : BinIntr) (b : Val w) : f.eval none b = none := by
  cases f
  · exact Contract.umin_strict.left b
  · exact Contract.umax_strict.left b
  · exact Contract.smin_strict.left b
  · exact Contract.smax_strict.left b
  · exact Contract.uaddSat_strict.left b
  · exact Contract.usubSat_strict.left b
  · exact Contract.saddSat_strict.left b
  · exact Contract.ssubSat_strict.left b

theorem BinIntr.eval_none_right (f : BinIntr) (a : Val w) : f.eval a none = none := by
  cases f
  · exact Contract.umin_strict.right a
  · exact Contract.umax_strict.right a
  · exact Contract.smin_strict.right a
  · exact Contract.smax_strict.right a
  · exact Contract.uaddSat_strict.right a
  · exact Contract.usubSat_strict.right a
  · exact Contract.saddSat_strict.right a
  · exact Contract.ssubSat_strict.right a

theorem fsh_none (l : Bool) (a b c : Val w) (h : a = none ∨ b = none ∨ c = none) :
    (if l then Val.fshl else Val.fshr) a b c = none := by
  cases l
  · exact Contract.fshr_strict a b c h
  · exact Contract.fshl_strict a b c h

/-- Poison refines to anything. -/
theorem none_refines (r : Outcome (Val w)) (h : r = Outcome.ok none) (t : Outcome (Val w)) (ht : ∃ v, t = .ok v) :
    Refines r t := by
  obtain ⟨v, rfl⟩ := ht
  subst h
  exact refines_ok (Refine.val_none _)

/-! ### `umin`, `umax`, `smin` and `smax`, as `MinMaxIntrinsic` sees them -/

/-- Whether the intrinsic is `umin`, `umax`, `smin` or `smax`: what `MinMaxIntrinsic` is. -/
def isMinMax : BinIntr → Bool
  | .umin | .umax | .smin | .smax => true
  | _ => false

/-- `MinMaxIntrinsic::getSaturationPoint(IID, BitWidth)`: the value it can't pass. Not a min or max, it's unreachable
in the C++, and 0 here. -/
def satPoint : BinIntr → (w : Nat) → BitVec w
  | .umin, w => 0#w
  | .umax, w => BitVec.allOnes w
  | .smin, w => BitVec.intMin w
  | .smax, w => BitVec.intMax w
  | _, w => 0#w

/-- `getInverseMinMaxIntrinsic(IID)`. Not a min or max, it's unreachable in the C++, and the intrinsic itself here. -/
def inverse : BinIntr → BinIntr
  | .umin => .umax
  | .umax => .umin
  | .smin => .smax
  | .smax => .smin
  | f => f

/-- `ICmpInst::getNonStrictPredicate(MinMaxIntrinsic::getPredicate(IID))`: `uge` for `umax` and so on. Not a min or
max, it's unreachable in the C++, and `eq` here. -/
def nonStrictPred : BinIntr → Pred
  | .umin => .ule
  | .umax => .uge
  | .smin => .sle
  | .smax => .sge
  | _ => .eq

/-- `ICmpInst::compare(LHS, RHS, Pred)`: the comparison of two constants. -/
def compare (p : Pred) (a b : BitVec w) : Bool := p.eval (some a) (some b) false == some 1#1

theorem minMax_self {f : BinIntr} (hf : isMinMax f = true) (a : Val w) : f.eval a a = a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_self a
  · exact Lemmas.umax_self a
  · exact Lemmas.smin_self a
  · exact Lemmas.smax_self a

theorem minMax_comm {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) : f.eval a b = f.eval b a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_comm a b
  · exact Lemmas.umax_comm a b
  · exact Lemmas.smin_comm a b
  · exact Lemmas.smax_comm a b

/-- A min or max with its saturation point is that point. -/
theorem minMax_satPoint {f : BinIntr} (hf : isMinMax f = true) (a : Val w) :
    Refines (f.eval a (some (satPoint f w))) (some (satPoint f w)) := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, satPoint]
  · exact Lemmas.umin_zero_refines a
  · exact Lemmas.umax_allOnes_refines a
  · exact Lemmas.smin_intMin_refines a
  · exact Lemmas.smax_intMax_refines a

/-- A min or max with its inverse's saturation point is the other operand. -/
theorem minMax_inverse_satPoint {f : BinIntr} (hf : isMinMax f = true) (a : Val w) :
    f.eval a (some (satPoint (inverse f) w)) = a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, satPoint, inverse]
  · exact Lemmas.umin_allOnes a
  · exact Lemmas.umax_zero a
  · exact Lemmas.smin_intMax a
  · exact Lemmas.smax_intMin a

/-- `max(max(x, c), d)` is `max(x, c)` if `c ≥ d`, by the non-strict predicate. -/
theorem minMax_nested {f : BinIntr} (hf : isMinMax f = true) (a : Val w) {c d : BitVec w}
    (h : compare (nonStrictPred f) c d = true) : f.eval (f.eval a (some c)) (some d) = f.eval a (some c) := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [compare, nonStrictPred, Pred.eval, Val.icmpUle, Val.icmpUge, Val.icmpSle, Val.icmpSge, Val.icmp,
      Bool.false_and, Bool.false_eq_true, ite_false, beq_iff_eq, Option.some.injEq] at h <;>
    simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_of_ule a (by cases hc : c.ule d <;> simp_all)
  · exact Lemmas.umax_umax_of_ule a (by cases hc : d.ule c <;> simp_all)
  · exact Lemmas.smin_smin_of_sle a (by cases hc : c.sle d <;> simp_all)
  · exact Lemmas.smax_smax_of_sle a (by cases hc : d.sle c <;> simp_all)

theorem minMax_left {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) : f.eval (f.eval a b) a = f.eval a b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_left a b
  · exact Lemmas.umax_umax_left a b
  · exact Lemmas.smin_smin_left a b
  · exact Lemmas.smax_smax_left a b

theorem minMax_right {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) : f.eval (f.eval a b) b = f.eval a b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_right a b
  · exact Lemmas.umax_umax_right a b
  · exact Lemmas.smin_smin_right a b
  · exact Lemmas.smax_smax_right a b

/-- `max(min(x, y), x)` refines `x`. -/
theorem minMax_inverse_left {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    Refines (f.eval ((inverse f).eval a b) a) a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, inverse]
  · exact Lemmas.umin_umax_left_refines a b
  · exact Lemmas.umax_umin_left_refines a b
  · exact Lemmas.smin_smax_left_refines a b
  · exact Lemmas.smax_smin_left_refines a b

theorem minMax_inverse_right {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    Refines (f.eval ((inverse f).eval a b) b) b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, inverse]
  · exact Lemmas.umin_umax_right_refines a b
  · exact Lemmas.umax_umin_right_refines a b
  · exact Lemmas.smin_smax_right_refines a b
  · exact Lemmas.smax_smin_right_refines a b

/-- A min or max of two values is one of them. -/
theorem minMax_some_mem {f : BinIntr} (hf : isMinMax f = true) (x y : BitVec w) :
    f.eval (some x) (some y) = some x ∨ f.eval (some x) (some y) = some y := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [BinIntr.eval, Val.umin, Val.umax, Val.smin, Val.smax, Val.map₂] <;> split <;> simp

/-- A min or max of two values whose non-strict predicate holds of them is the first. -/
theorem minMax_of_pred {f : BinIntr} (hf : isMinMax f = true) {x y : BitVec w}
    (h : (nonStrictPred f).eval (some x) (some y) false = some 1#1) : f.eval (some x) (some y) = some x := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [nonStrictPred, Pred.eval, Val.icmpUle, Val.icmpUge, Val.icmpSle, Val.icmpSge, Val.icmp,
      Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq] at h <;>
    simp only [BinIntr.eval]
  · exact Lemmas.umin_of_ule (by cases hc : x.ule y <;> simp_all)
  · exact Lemmas.umax_of_ule (by cases hc : y.ule x <;> simp_all)
  · exact Lemmas.smin_of_sle (by cases hc : x.sle y <;> simp_all)
  · exact Lemmas.smax_of_sle (by cases hc : y.sle x <;> simp_all)

end Peephole.IS.Intrinsic
