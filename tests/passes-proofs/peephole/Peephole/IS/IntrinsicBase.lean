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

theorem _root_.Peephole.IS.un_denote {ρ : Env} {id : Nat} {f : UnIntr} {x : Term w}
    (c : (Term.un id f x).Consistent ρ) :
    (Term.un id f x).denote ρ = f.eval (x.denote ρ) :=
  c.2.symm

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

end Peephole.IS.Intrinsic
