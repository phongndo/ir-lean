import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.Lemmas.ICmp

/-! # What InstSimplify's `icmp` folds share

`simplifyICmpInst` and its helpers in `llvm/lib/Analysis/InstructionSimplify.cpp` at `llvmorg-23.1.3` read an
`icmp`'s predicate, as `CmpInst` has it, and answer with a constant or a value that's already there. This module has
what their models share:

- `CmpInst`'s functions on predicates (`swap`, `inverse`, `unsigned`, `isEquality` and the rest), and `test`, what
  `icmp p x y` answers on two values.
- `src`, the `icmp` a fold replaces, and the lemmas that reduce a rewrite of it to a fact about `test`. `samesign`
  only makes the source poison in more runs, which a replacement may refine in any way, so every rewrite here holds
  for both values of it.
- `fwd`, a call to another fold modelled here as one step.
- `Ext`, the analyses `simplifyICmpInst` asks that the core `Oracle` doesn't have: `isImpliedByDomCondition`,
  `getRange` and `computeConstantRange`, with `Ext.Sound`, what a sound answer means. The ranges are LLVM's
  `ConstantRange`, `CR` here. -/

namespace Peephole.IS.ICmp

open IRLean

variable {w v : Nat}

/-! ### Predicates, as `CmpInst` has them -/

/-- `CmpInst::getSwappedPredicate`: the predicate with the operands the other way round. It drops `samesign`. -/
def swap : Pred → Pred
  | .eq => .eq | .ne => .ne
  | .ugt => .ult | .uge => .ule | .ult => .ugt | .ule => .uge
  | .sgt => .slt | .sge => .sle | .slt => .sgt | .sle => .sge

/-- `CmpInst::getInversePredicate`: the predicate that's false where this one is true. -/
def inverse : Pred → Pred
  | .eq => .ne | .ne => .eq
  | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

/-- `ICmpInst::getUnsignedPredicate`. -/
def unsigned : Pred → Pred
  | .sgt => .ugt | .sge => .uge | .slt => .ult | .sle => .ule
  | p => p

/-- `ICmpInst::isEquality`. -/
def isEquality : Pred → Bool
  | .eq | .ne => true
  | _ => false

/-- `ICmpInst::isUnsigned`. -/
def isUnsigned : Pred → Bool
  | .ugt | .uge | .ult | .ule => true
  | _ => false

/-- `ICmpInst::isSigned`. -/
def isSigned : Pred → Bool
  | .sgt | .sge | .slt | .sle => true
  | _ => false

/-- `CmpInst::isTrueWhenEqual`. -/
def isTrueWhenEqual : Pred → Bool
  | .eq | .uge | .ule | .sge | .sle => true
  | _ => false

/-- What `icmp p x y` answers on two values, without `samesign`: `IRLean.Val.icmp`'s comparison for each
predicate. -/
def test : Pred → BitVec w → BitVec w → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .ugt, x, y => BitVec.ult y x
  | .uge, x, y => BitVec.ule y x
  | .ult, x, y => BitVec.ult x y
  | .ule, x, y => BitVec.ule x y
  | .sgt, x, y => BitVec.slt y x
  | .sge, x, y => BitVec.sle y x
  | .slt, x, y => BitVec.slt x y
  | .sle, x, y => BitVec.sle x y

theorem eval_some (p : Pred) (x y : BitVec w) (s : Bool) :
    p.eval (some x) (some y) s = if s && x.msb != y.msb then none else some (BitVec.ofBool (test p x y)) := by
  cases p <;> rfl

theorem eval_none_left (p : Pred) (b : Val w) (s : Bool) : p.eval none b s = none := by
  cases p <;> rfl

theorem eval_none_right (p : Pred) (a : Val w) (s : Bool) : p.eval a none s = none := by
  cases p <;> cases a <;> rfl

theorem test_swap (p : Pred) (x y : BitVec w) : test (swap p) y x = test p x y := by
  cases p <;> simp only [test, swap, BEq.comm, bne_comm]

theorem eval_swap (p : Pred) (a b : Val w) (s : Bool) : (swap p).eval b a s = p.eval a b s := by
  cases a with
  | none => rw [eval_none_right, eval_none_left]
  | some x =>
  cases b with
  | none => rw [eval_none_right, eval_none_left]
  | some y => rw [eval_some, eval_some, test_swap, bne_comm]

theorem test_inverse (p : Pred) (x y : BitVec w) : test (inverse p) x y = !test p x y := by
  cases p <;> simp only [test, inverse, bne, Bool.not_not, BitVec.ule_eq_not_ult, BitVec.sle_eq_not_slt]

theorem test_self (p : Pred) (x : BitVec w) : test p x x = isTrueWhenEqual p := by
  cases p <;> simp [test, isTrueWhenEqual, BitVec.ult_eq_decide, BitVec.ule_eq_decide, BitVec.slt_eq_decide,
    BitVec.sle_eq_decide]

/-! ### The source, and what a rewrite of it has to show -/

/-- `icmp p a b`, with `samesign` if `s`: what `simplifyICmpInst` replaces. -/
def src (p : Pred) (s : Bool) (a b : Term w) : Repl 1 := .icmp p s (.old a) (.old b)

@[simp] theorem src_eval (ρ : Env) (p : Pred) (s : Bool) (a b : Term w) :
    (src p s a b).eval ρ = Outcome.ok (p.eval (a.denote ρ) (b.denote ρ) s) := rfl

theorem refines_ok {a b : Val v} (h : Refines a b) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok a b).2 h

/-- An `icmp` refines `t` if `t` is what it computes whenever neither operand is poison. `samesign` makes it poison
in more runs, which allows anything. -/
theorem eval_refines {p : Pred} {a b : Val w} {s : Bool} {t : Val 1}
    (h : ∀ x y, a = some x → b = some y → t = some (BitVec.ofBool (test p x y))) : Refines (p.eval a b s) t := by
  cases a with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some x =>
  cases b with
  | none => rw [eval_none_right]; exact Refine.val_none _
  | some y =>
  rw [eval_some, h x y rfl rfl]
  split
  · exact Refine.val_none _
  · exact Refine.refl_val _

/-- An `icmp` refines the constant `c` if it's `c` whenever neither operand is poison. -/
theorem eval_refines_ofBool {p : Pred} {a b : Val w} {s c : Bool}
    (h : ∀ x y, a = some x → b = some y → test p x y = c) : Refines (p.eval a b s) (some (BitVec.ofBool c)) :=
  eval_refines fun x y hx hy => by rw [h x y hx hy]

/-- An `icmp` with a poison operand is poison, which anything refines. -/
theorem eval_refines_of_left_none {p : Pred} {a b : Val w} {s : Bool} (t : Val 1) (h : a = none) :
    Refines (p.eval a b s) t := by
  rw [h, eval_none_left]; exact Refine.val_none _

theorem eval_refines_of_right_none {p : Pred} {a b : Val w} {s : Bool} (t : Val 1) (h : b = none) :
    Refines (p.eval a b s) t := by
  rw [h, eval_none_right]; exact Refine.val_none _

/-- Refining the `icmp` the other way round, with the swapped predicate, is refining this one. -/
theorem src_swap (ρ : Env) (p : Pred) (s : Bool) (a b : Term w) :
    (src (swap p) s b a).eval ρ = (src p s a b).eval ρ := by
  rw [src_eval, src_eval, eval_swap]

/-- What `m_Zero`, `m_One`, `m_AllOnes` and the like say: the operand is that constant. -/
theorem cst_eq {ρ : Env} {t : Term w} {c : BitVec w} (h : cst (· == c) t = true) : t.denote ρ = some c := by
  obtain ⟨c', hc', hd⟩ := cst_denote (ρ := ρ) h
  simp only [beq_iff_eq] at hc'
  rw [hd, hc']

/-! ### Constants of type `i1` -/

/-- `getTrue(Ty)` and `ConstantInt::getTrue(Ty)`, for an `i1`. -/
def getTrue : Repl 1 := .const 1#1

/-- `getFalse(Ty)` and `ConstantInt::getFalse(Ty)`, for an `i1`. -/
def getFalse : Repl 1 := .const 0#1

/-- `ConstantInt::get(Ty, B)` and `ConstantInt::getBool(Ty, B)`, for an `i1`. -/
def getBool (b : Bool) : Repl 1 := .const (BitVec.ofBool b)

@[simp] theorem getTrue_eval (ρ : Env) : getTrue.eval ρ = Outcome.ok (some (BitVec.ofBool true)) := rfl
@[simp] theorem getFalse_eval (ρ : Env) : getFalse.eval ρ = Outcome.ok (some (BitVec.ofBool false)) := rfl
@[simp] theorem getBool_eval (ρ : Env) (b : Bool) : (getBool b).eval ρ = Outcome.ok (some (BitVec.ofBool b)) := rfl

/-- An `icmp` refines the constant `c` if it's `c` whenever neither operand is poison: the form each rewrite to a
constant takes. -/
theorem src_refines_const {ρ : Env} {p : Pred} {s c : Bool} {a b : Term w}
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y → test p x y = c) :
    Refines ((src p s a b).eval ρ) (Outcome.ok (some (BitVec.ofBool c))) :=
  refines_ok (eval_refines_ofBool h)

/-! ### Steps -/

/-- A call to a fold modelled here, as one step: its answer, under the site it came from, or the next step on
`nullptr`. -/
def fwd (steps : List (Step w)) : Step w :=
  match run steps with
  | .value r => .fire ((firedSite steps).getD "") r
  | .null => .next
  | .delegated c => .delegate c

theorem fwd_fire {steps : List (Step w)} {s : String} {r : Repl w} (h : fwd steps = .fire s r) :
    run steps = .value r := by
  unfold fwd at h
  split at h
  · next r' hr => simp only [Step.fire.injEq] at h; rw [hr, h.2]
  · cases h
  · cases h

/-- `t` as an operand of width `v`, if that's its width. `m_Specific` between values of different types never
matches: they're different `Value *`s. -/
def sameWidth {v v' : Nat} (t : Term v') : Option (Term v) := if h : v' = v then some (h ▸ t) else none

theorem sameWidth_eq {v v' : Nat} {t : Term v'} {t' : Term v} (h : sameWidth t = some t') :
    ∃ e : v' = v, e ▸ t = t' := by
  unfold sameWidth at h
  split at h
  · next e => exact ⟨e, Option.some.inj h⟩
  · cases h

/-! ### `ConstantRange` -/

/-- `ConstantRange`, as LLVM keeps it: the values from `lower` up to but not including `upper`, wrapping past the
maximum when `lower >u upper`. `lower = upper` is the full set if both are all ones, and the empty set if both are 0;
LLVM never makes one equal to anything else. -/
structure CR (w : Nat) where
  lower : BitVec w
  upper : BitVec w

/-- `ConstantRange::isFullSet`. -/
def CR.isFullSet (r : CR w) : Bool := r.lower == r.upper && r.lower == BitVec.allOnes w

/-- `ConstantRange::isEmptySet`. -/
def CR.isEmptySet (r : CR w) : Bool := r.lower == r.upper && r.lower == 0#w

/-- `ConstantRange::isUpperWrapped`. -/
def CR.isUpperWrapped (r : CR w) : Bool := BitVec.ult r.upper r.lower

/-- `ConstantRange::contains(const APInt &)`. -/
def CR.contains (r : CR w) (x : BitVec w) : Bool :=
  if r.lower == r.upper then r.isFullSet
  else if !r.isUpperWrapped then BitVec.ule r.lower x && BitVec.ult x r.upper
  else BitVec.ule r.lower x || BitVec.ult x r.upper

/-- `ConstantRange::getFull`. -/
def CR.full : CR w := ⟨BitVec.allOnes w, BitVec.allOnes w⟩

theorem CR.full_contains (x : BitVec w) : (CR.full : CR w).contains x = true := by
  simp [CR.full, CR.contains, CR.isFullSet]

/-! ### Analyses the core `Oracle` doesn't have -/

/-- Answers to the analyses `simplifyICmpInst` and its helpers ask that the core `Oracle` doesn't have. -/
structure Ext where
  /-- `isImpliedByDomCondition(Pred, LHS, RHS, CxtI, DL)`: `some b` if a condition that dominates the instruction
  being folded says `icmp Pred LHS, RHS` is `b`. -/
  domCond : {w : Nat} → Pred → Term w → Term w → Option Bool
  /-- `getRange(V, IIQ)`: the range a `!range` metadata or a `range` attribute gives `V`. -/
  getRange : {w : Nat} → Term w → Option (CR w)
  /-- `computeConstantRange(V, ForSigned, Q)`. -/
  constRange : {w : Nat} → Bool → Term w → CR w

/-- Every answer `e` gives is true in the run `ρ`. As for the core `Oracle`, an answer is about operands that aren't
poison: a value outside its `!range` is poison, and a dominating branch on poison would have been undefined. -/
structure Ext.Sound (e : Ext) (ρ : Env) : Prop where
  domCond : ∀ {w} (p : Pred) (a b : Term w) (r : Bool) (x y : BitVec w), e.domCond p a b = some r →
    a.denote ρ = some x → b.denote ρ = some y → test p x y = r
  getRange : ∀ {w} (t : Term w) (r : CR w) (x : BitVec w), e.getRange t = some r → t.denote ρ = some x →
    r.contains x = true
  constRange : ∀ {w} (signed : Bool) (t : Term w) (x : BitVec w), t.denote ρ = some x →
    (e.constRange signed t).contains x = true

/-- The extension that knows nothing: no dominating condition, no range metadata, and every range full. -/
def Ext.none : Ext where
  domCond _ _ _ := Option.none
  getRange _ := Option.none
  constRange _ _ := CR.full

theorem Ext.none_sound (ρ : Env) : Ext.none.Sound ρ where
  domCond _ _ _ _ _ _ h := by simp [Ext.none] at h
  getRange _ _ _ h := by simp [Ext.none] at h
  constRange _ _ x _ := CR.full_contains x

end Peephole.IS.ICmp
