import Peephole.IS.ICmpOfBools
import Peephole.IS.ICmpWithZero
import Peephole.IS.ICmpWithConstant
import Peephole.IS.ICmpMonotonic

/-! # InstSimplify's `simplifyICmpInst`, its integer half, and its rewrites for every input

`simplifyICmpInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3863-4169` at `llvmorg-23.1.3`. InstSimplify calls
it on every `icmp`, with the instruction's `CmpPredicate` and `MaxRecurse` at `RecursionLimit`, 3. This is its model
on `Peephole.Term`, step by step in the C++'s order.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpInst.L3869` | two constants: the constant folder's answer, not modelled |
| `IS.simplifyICmpInst.L3881` | `icmp X, poison` to poison |
| `IS.simplifyICmpInst.L3887` | `icmp eq/ne X, undef` to `undef`; without `undef`, about poison only |
| `IS.simplifyICmpInst.L3892` | `icmp X, X` to whether the predicate holds on equal values |
| `IS.simplifyICmpInst.L3910` | `icmp X, Y` to true, where their `!range`s say so |
| `IS.simplifyICmpInst.L3913` | `icmp X, Y` to false, where their `!range`s say so |
| `IS.simplifyICmpInst.L3959` | `zext X <=u sext X` and `zext X >=s sext X` to true |
| `IS.simplifyICmpInst.L3961` | `zext X >u sext X` and `zext X <s sext X` to false |
| `IS.simplifyICmpInst.L4000` | `zext X ==, >u, >=u C` to false, where `C` isn't a zero extension |
| `IS.simplifyICmpInst.L4005` | `zext X !=, <u, <=u C` to true, there |
| `IS.simplifyICmpInst.L4011` | `zext X >s, >=s C` to `C <s 0`, there |
| `IS.simplifyICmpInst.L4016` | `zext X <s, <=s C` to `C >=s 0`, there |
| `IS.simplifyICmpInst.L4038` | `sext X >=u zext X` and `sext X <=s zext X` to true |
| `IS.simplifyICmpInst.L4040` | `sext X <u zext X` and `sext X >s zext X` to false |
| `IS.simplifyICmpInst.L4074` | `sext X == C` to false, where `C` isn't a sign extension |
| `IS.simplifyICmpInst.L4076` | `sext X != C` to true, there |
| `IS.simplifyICmpInst.L4082` | `sext X >s, >=s C` to `C <s 0`, there |
| `IS.simplifyICmpInst.L4087` | `sext X <s, <=s C` to `C >=s 0`, there |
| `IS.simplifyICmpInst.L4122` | `X == Y` to false and `X != Y` to true, where `isKnownNonEqual(X, Y)` |
| `IS.simplifyICmpInst.L4148` | `icmp X, Y` to what a dominating condition says it is |
| `IS.simplifyICmpInst.L4154` | pointers: `computePointerICmp`, not modelled |

`simplifyICmpOfBools`, `simplifyICmpWithZero`, `simplifyICmpWithConstant` and `simplifyICmpUsingMonotonicValues`
are forwards to their models, and each step that forwards fires with the site its callee fired. `simplifyICmpInst`'s
own recursive calls, on the operands of two casts and on a constant brought to the operand's width, are forwards to
the model one level of `MaxRecurse` down: `simplifyICmpInst.body` recurses on it. The forwards to
`simplifyICmpWithBinOp`, `simplifyICmpWithMinMax`, `simplifyICmpWithIntrinsicOnLHS`,
`simplifyICmpWithDominatingAssume`, `threadCmpOverSelect` and `threadCmpOverPHI` are `.delegate`s, which claim
nothing: another family models the first three. Each is a `.delegate` only where the C++ can answer: the first needs
a binary operator on one side, the second a min, a max or a `select`, the third a `uadd.sat` or `usub.sat` on its
left, so elsewhere the step falls through, as the call returns `nullptr`.

The recursive calls on the operands of two zero or two sign extensions, or of one against a constant that's an
extension, are only right where the cast widens, as LLVM's verifier requires of `zext` and `sext`; `Term` can hold a
`zext` that doesn't, so the model takes those steps only where `v < w`. -/

namespace Peephole.IS

open IRLean ICmp

variable {w v : Nat}

/-! ### Helpers -/

namespace ICmp

/-- `dyn_cast<BinaryOperator>(V)`: what `simplifyICmpWithBinOp` needs on one side. -/
def isBinOp : Term w → Bool
  | .bin .. => true
  | _ => false

/-- What `m_SMax`, `m_SMin`, `m_UMax` and `m_UMin` can match: a min or max intrinsic, or a `select`, which
`simplifyICmpWithMinMax` needs on one side. -/
def isMinMaxLike : Term w → Bool
  | .bi _ .smax .. | .bi _ .smin .. | .bi _ .umax .. | .bi _ .umin .. | .select .. => true
  | _ => false

/-- `uadd.sat` or `usub.sat`: the intrinsics `simplifyICmpWithIntrinsicOnLHS` answers for on its left. -/
def isSatAddSub : Term w → Bool
  | .bi _ .uaddSat .. | .bi _ .usubSat .. => true
  | _ => false

/-- `SrcOp == RI->getOperand(0)`: the same `Value *`, so of one type. -/
def sameSrc {v v' : Nat} (x : Term v) (y : Term v') : Bool :=
  match sameWidth (v := v) y with
  | some y' => specific x y'
  | none => false

theorem sameSrc_eq {ρ : Env} {v v' : Nat} {x : Term v} {y : Term v'} (h : sameSrc x y = true) :
    ∃ e : v' = v, (e ▸ y).denote ρ = x.denote ρ := by
  unfold sameSrc at h
  split at h
  · next y' hy =>
    obtain ⟨e, rfl⟩ := sameWidth_eq hy
    exact ⟨e, specific_denote h⟩
  · cases h

theorem zext_some {a : Val v} {nn : Bool} {z : BitVec w} (h : Val.zext w a nn = some z) :
    ∃ x, a = some x ∧ z = x.setWidth w := by
  cases a with
  | none => cases h
  | some x =>
    simp only [Val.zext] at h
    split at h
    · cases h
    · exact ⟨x, rfl, (Option.some.inj h).symm⟩

theorem sext_some {a : Val v} {z : BitVec w} (h : Val.sext w a = some z) : ∃ x, a = some x ∧ z = x.signExtend w := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, (Option.some.inj h).symm⟩

theorem zext_denote {ρ : Env} {id : Nat} {nn : Bool} {x : Term v} (hc : (Term.zext (w := w) id nn x).Consistent ρ)
    {z : BitVec w} (h : (Term.zext (w := w) id nn x).denote ρ = some z) :
    ∃ xv, x.denote ρ = some xv ∧ z = xv.setWidth w := by
  simp only [Term.Consistent, Term.denote] at hc h
  rw [← hc.2] at h
  exact zext_some h

theorem sext_denote {ρ : Env} {id : Nat} {x : Term v} (hc : (Term.sext (w := w) id x).Consistent ρ)
    {z : BitVec w} (h : (Term.sext (w := w) id x).denote ρ = some z) :
    ∃ xv, x.denote ρ = some xv ∧ z = xv.signExtend w := by
  simp only [Term.Consistent, Term.denote] at hc h
  rw [← hc.2] at h
  exact sext_some h

/-- Two zero extensions to a wider type compare as their operands do, unsigned. -/
theorem test_setWidth (p : Pred) (x y : BitVec v) (h : v < w) :
    test p (x.setWidth w) (y.setWidth w) = test (unsigned p) x y := by
  have hle := Nat.le_of_lt h
  cases p <;> simp only [test, unsigned, bne, Lemmas.setWidth_beq_setWidth _ _ hle,
    Lemmas.setWidth_ult_setWidth _ _ hle, Lemmas.setWidth_ule_setWidth _ _ hle, Lemmas.setWidth_slt_setWidth _ _ h,
    Lemmas.setWidth_sle_setWidth _ _ h]

/-- Two sign extensions compare as their operands do. -/
theorem test_signExtend (p : Pred) (x y : BitVec v) (h : v ≤ w) :
    test p (x.signExtend w) (y.signExtend w) = test p x y := by
  cases p <;> simp only [test, bne, Lemmas.signExtend_beq_signExtend _ _ h, Lemmas.signExtend_ult_signExtend _ _ h,
    Lemmas.signExtend_ule_signExtend _ _ h, Lemmas.signExtend_slt_signExtend _ _ h,
    Lemmas.signExtend_sle_signExtend _ _ h]

/-- A replacement that refines `icmp p' a', b'` refines `icmp p a, b`, where `p` on `a` and `b` is `p'` on `a'` and
`b'` whenever `a` and `b` aren't poison: how a recursive call's answer is right for the instruction. -/
theorem src_refines_via {ρ : Env} {p p' : Pred} {s : Bool} {a b : Term w} {a' b' : Term v} {R : Outcome (Val 1)}
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y →
      ∃ x' y', a'.denote ρ = some x' ∧ b'.denote ρ = some y' ∧ test p x y = test p' x' y')
    (hr : Refines ((src p' false a' b').eval ρ) R) : Refines ((src p s a b).eval ρ) R := by
  refine Refines.trans ?_ hr
  rw [src_eval, src_eval]
  refine refines_ok (eval_refines fun x y hx hy => ?_)
  obtain ⟨x', y', hx', hy', ht⟩ := h x y hx hy
  rw [hx', hy', eval_some, ht]
  rfl

end ICmp

/-! ### The model -/

/-- What a recursive call `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse - 1)` is to a step: the model's steps one
level down. -/
abbrev ICmp.Rec := ∀ {v : Nat}, Pred → Term v → Term v → List (Step 1)

namespace simplifyICmpInst

/-- `if (MaxRecurse && SrcTy == RI->getOperand(0)->getType())`: turn `icmp (zext X), (zext Y)` into a compare of `X`
and `Y` with the unsigned predicate. -/
def zextZext (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : Step 1 :=
  match lhs, rhs with
  | @Term.zext v _ _ _ x, @Term.zext _ _ _ _ y =>
    match sameWidth (v := v) y with
    | some y' => if n != 0 && decide (v < w) then fwd (rec (unsigned p) x y') else .next
    | none => .next
  | _, _ => .next

/-- Fold `(zext X) ule (sext X)`, `(zext X) sge (sext X)` to true. -/
def zextSextTrue (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | .zext _ _ x, .sext _ y =>
    if sameSrc x y && (p == .ule || p == .sge) then .fire "IS.simplifyICmpInst.L3959" getTrue else .next
  | _, _ => .next

/-- ... and `(zext X) ugt (sext X)`, `(zext X) slt (sext X)` to false. -/
def zextSextFalse (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | .zext _ _ x, .sext _ y =>
    if sameSrc x y && (p == .ugt || p == .slt) then .fire "IS.simplifyICmpInst.L3961" getFalse else .next
  | _, _ => .next

/-- Turn `icmp (zext X), Cst` into a compare of `X` and `Cst` if `Cst` is extended too: `AnyEq` is all ones. -/
def zextConstRec (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : Step 1 :=
  match lhs, rhs with
  | @Term.zext v _ _ _ x, .const c =>
    if (c.setWidth v).setWidth w == c && n != 0 && decide (v < w) then
      fwd (rec (unsigned p) x (.const (c.setWidth v)))
    else .next
  | _, _ => .next

/-- Otherwise the upper bits of LHS are zero while RHS has a non-zero bit there: `AnyEq` is null. Each of the four
`return`s of its switch, with the `Constant::getNullValue(ITy)`, `Constant::getAllOnesValue(ITy)` or constant fold it
answers. -/
def zextConstNull (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | @Term.zext v _ _ _ _, .const c =>
    if (c.setWidth v).setWidth w != c then
      match p with
      -- LHS <u RHS.
      | .eq | .ugt | .uge => .fire "IS.simplifyICmpInst.L4000" getFalse
      | .ne | .ult | .ule => .fire "IS.simplifyICmpInst.L4005" getTrue
      -- LHS is non-negative.  If RHS is negative then LHS >s LHS.  If RHS is non-negative then LHS <s RHS.
      | .sgt | .sge => .fire "IS.simplifyICmpInst.L4011" (getBool (BitVec.slt c 0#w))
      | .slt | .sle => .fire "IS.simplifyICmpInst.L4016" (getBool (BitVec.sle 0#w c))
    else .next
  | _, _ => .next

/-- Turn `icmp (sext X), (sext Y)` into a compare of `X` and `Y` if they have the same type; the predicate stays. -/
def sextSext (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : Step 1 :=
  match lhs, rhs with
  | @Term.sext v _ _ x, @Term.sext _ _ _ y =>
    match sameWidth (v := v) y with
    | some y' => if n != 0 && decide (v < w) then fwd (rec p x y') else .next
    | none => .next
  | _, _ => .next

/-- Fold `(sext X) uge (zext X)`, `(sext X) sle (zext X)` to true. -/
def sextZextTrue (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | .sext _ x, .zext _ _ y =>
    if sameSrc x y && (p == .uge || p == .sle) then .fire "IS.simplifyICmpInst.L4038" getTrue else .next
  | _, _ => .next

/-- ... and `(sext X) ult (zext X)`, `(sext X) sgt (zext X)` to false. -/
def sextZextFalse (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | .sext _ x, .zext _ _ y =>
    if sameSrc x y && (p == .ult || p == .sgt) then .fire "IS.simplifyICmpInst.L4040" getFalse else .next
  | _, _ => .next

/-- Turn `icmp (sext X), Cst` into a compare of `X` and `Cst` if `Cst` is extended too. -/
def sextConstRec (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : Step 1 :=
  match lhs, rhs with
  | @Term.sext v _ _ x, .const c =>
    if (c.setWidth v).signExtend w == c && n != 0 && decide (v < w) then fwd (rec p x (.const (c.setWidth v)))
    else .next
  | _, _ => .next

/-- Otherwise the upper bits of LHS are all equal, while RHS has varying bits there: `AnyEq` is null. The switch's
four `return`s. -/
def sextConstNull (p : Pred) (lhs rhs : Term w) : Step 1 :=
  match lhs, rhs with
  | @Term.sext v _ _ _, .const c =>
    if (c.setWidth v).signExtend w != c then
      match p with
      | .eq => .fire "IS.simplifyICmpInst.L4074" getFalse
      | .ne => .fire "IS.simplifyICmpInst.L4076" getTrue
      -- If RHS is non-negative then LHS <s RHS.  If RHS is negative then LHS >s RHS.
      | .sgt | .sge => .fire "IS.simplifyICmpInst.L4082" (getBool (BitVec.slt c 0#w))
      | .slt | .sle => .fire "IS.simplifyICmpInst.L4087" (getBool (BitVec.sle 0#w c))
      | _ => .next
    else .next
  | _, _ => .next

/-- The switch's two recursive calls: if LHS is non-negative then LHS <u RHS, if negative LHS >u RHS, so the
comparison is `LHS <s 0` or `LHS >=s 0`. -/
def sextConstSign (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : Step 1 :=
  match lhs, rhs with
  | @Term.sext v _ _ x, .const c =>
    if (c.setWidth v).signExtend w != c && n != 0 then
      match p with
      -- Comparison is true iff the LHS <s 0.
      | .ugt | .uge => fwd (rec .slt x (.const 0#v))
      -- Comparison is true iff the LHS >=s 0.
      | .ult | .ule => fwd (rec .sge x (.const 0#v))
      | _ => .next
    else .next
  | _, _ => .next

/-- `simplifyICmpInst` once a lone constant is on the right, a step for each statement that can end it. `rec` is the
model one level of `MaxRecurse` down. -/
def steps (o : Oracle) (e : Ext) (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : List (Step 1) :=
  [ -- icmp poison, X -> poison
    if isPoison rhs then .fire "IS.simplifyICmpInst.L3881" .poison else .next,
    -- For EQ and NE, we can always pick a value for the undef to make the predicate pass or fail, so we can return
    -- undef. `UndefValue::get(ITy)` is the `undef` constant of type `i1`.
    if isUndefValue rhs && isEquality p then .fire "IS.simplifyICmpInst.L3887" (.old (.undef : Term 1)) else .next,
    -- icmp X, X -> true/false
    -- icmp X, undef -> true/false because undef could be X.
    if specific lhs rhs || isUndefValue rhs then .fire "IS.simplifyICmpInst.L3892" (getBool (isTrueWhenEqual p))
    else .next,
    fwdR "IS.simplifyICmpOfBools" (simplifyICmpOfBools o p lhs rhs),
    fwdR "IS.simplifyICmpWithZero" (simplifyICmpWithZero o p lhs rhs),
    fwdR "IS.simplifyICmpWithConstant" (simplifyICmpWithConstant o e p lhs rhs),
    -- If both operands have range metadata, use the metadata to simplify the comparison. The ranges are only read at
    -- a positive width (`Peephole.IS.ICmpConstantRange`).
    match e.getRange rhs, e.getRange lhs with
    | some rc, some lc => if w != 0 && lc.icmp p rc then .fire "IS.simplifyICmpInst.L3910" getTrue else .next
    | _, _ => .next,
    match e.getRange rhs, e.getRange lhs with
    | some rc, some lc =>
      if w != 0 && lc.icmp (inverse p) rc then .fire "IS.simplifyICmpInst.L3913" getFalse else .next
    | _, _ => .next,
    -- Compare of cast, for example (zext X) != 0 -> X != 0. `ptrtoint` and `ptrtoaddr` aren't in `Term`.
    zextZext rec p lhs rhs n,
    zextSextTrue p lhs rhs,
    zextSextFalse p lhs rhs,
    zextConstRec rec p lhs rhs n,
    zextConstNull p lhs rhs,
    sextSext rec p lhs rhs n,
    sextZextTrue p lhs rhs,
    sextZextFalse p lhs rhs,
    sextConstRec rec p lhs rhs n,
    sextConstNull p lhs rhs,
    sextConstSign rec p lhs rhs n,
    -- icmp eq|ne X, Y -> false|true if X != Y
    if isEquality p && !zero rhs && o.nonEqual lhs rhs then
      .fire "IS.simplifyICmpInst.L4122" (if p == .ne then getTrue else getFalse)
    else .next,
    -- simplifyICmpWithBinOp: every statement of it that can answer needs an operand that's a `BinaryOperator`.
    if isBinOp lhs || isBinOp rhs then .delegate "simplifyICmpWithBinOp" else .next,
    -- simplifyICmpWithMinMax: every statement of it that can answer needs a min or a max on one side.
    if isMinMaxLike lhs || isMinMaxLike rhs then .delegate "simplifyICmpWithMinMax" else .next,
    -- simplifyICmpWithIntrinsicOnLHS(Pred, LHS, RHS), and with them swapped: it only answers for `uadd.sat` and
    -- `usub.sat` on its left.
    if isSatAddSub lhs then .delegate "simplifyICmpWithIntrinsicOnLHS" else .next,
    if isSatAddSub rhs then .delegate "simplifyICmpWithIntrinsicOnLHS" else .next,
    fwdR "IS.simplifyICmpUsingMonotonicValues" (simplifyICmpUsingMonotonicValues o p lhs rhs),
    fwdR "IS.simplifyICmpUsingMonotonicValues" (simplifyICmpUsingMonotonicValues o (swap p) rhs lhs),
    .delegate "simplifyICmpWithDominatingAssume",
    match e.domCond p lhs rhs with
    | some b => .fire "IS.simplifyICmpInst.L4148" (getBool b)
    | none => .next,
    -- Simplify comparisons of related pointers using a powerful, recursive GEP-walk: `Term` has no pointers.
    -- If the comparison is with the result of a select instruction, check whether comparing with either branch of
    -- the select always yields the same value.
    match lhs, rhs with
    | .select .., _ | _, .select .. => .delegate "threadCmpOverSelect"
    | _, _ => .next,
    -- If the comparison is with the result of a phi instruction ...: a phi is a `Term.var`.
    match lhs, rhs with
    | .var _, _ | _, .var _ => .delegate "threadCmpOverPHI"
    | _, _ => .next ]

/-- `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse)`'s first statements: two constants go to the constant folder,
which isn't modelled, and a lone constant moves to the right, with the predicate swapped. -/
def entry (o : Oracle) (e : Ext) (rec : ICmp.Rec) (p : Pred) (lhs rhs : Term w) (n : Nat) : List (Step 1) :=
  if lhs.isConstant then
    if rhs.isConstant then [.delegate "ConstantFoldCompareInstOperands"]
    else steps o e rec (swap p) rhs lhs n
  else steps o e rec p lhs rhs n

/-- The model at each `MaxRecurse`, recursing on it: each recursive call is the model one level down. -/
def body (o : Oracle) (e : Ext) : Nat → ICmp.Rec
  | 0, _, p, lhs, rhs => entry o e (fun _ _ _ => []) p lhs rhs 0
  | n + 1, _, p, lhs, rhs => entry o e (fun p a b => body o e n p a b) p lhs rhs (n + 1)

/-! `body` at each `MaxRecurse` up to `RecursionLimit`, 3, written out: the same functions, as `body_three` says, but
not recursive, so a copy of them can report which step fired. -/

def body0 (o : Oracle) (e : Ext) : ICmp.Rec := fun p lhs rhs => entry o e (fun _ _ _ => []) p lhs rhs 0
def body1 (o : Oracle) (e : Ext) : ICmp.Rec := fun p lhs rhs => entry o e (fun p a b => body0 o e p a b) p lhs rhs 1
def body2 (o : Oracle) (e : Ext) : ICmp.Rec := fun p lhs rhs => entry o e (fun p a b => body1 o e p a b) p lhs rhs 2
def body3 (o : Oracle) (e : Ext) : ICmp.Rec := fun p lhs rhs => entry o e (fun p a b => body2 o e p a b) p lhs rhs 3

theorem body_three (o : Oracle) (e : Ext) (p : Pred) (lhs rhs : Term w) : body3 o e p lhs rhs = body o e 3 p lhs rhs :=
  rfl

end simplifyICmpInst

/-- `simplifyICmpInst(Pred, LHS, RHS, Q, MaxRecurse)`. -/
def simplifyICmpInst (o : Oracle) (e : Ext) (p : Pred) (lhs rhs : Term w) (n : Nat) : Result 1 :=
  run (simplifyICmpInst.body o e n p lhs rhs)

/-- What InstSimplify does with an `icmp` it reaches, given the analyses the core `Oracle` lacks as `e`:
`simplifyInstructionWithOperands` calls `simplifyICmpInst` with the instruction's `CmpPredicate` and `MaxRecurse` at
`RecursionLimit`, 3, which is `body3`. -/
def simplifyICmpInst.onInstWith (o : Oracle) (e : Ext) : {w : Nat} → Term w → Result w
  | _, .icmp _ p _ a b => run (simplifyICmpInst.body3 o e p a b)
  | _, _ => .null

/-- The entry point: `onInstWith` with the extension that knows nothing, as the comparison with `opt` runs it. -/
def simplifyICmpInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w :=
  simplifyICmpInst.onInstWith o Ext.none

/-! ### The rewrites, one theorem each -/

namespace simplifyICmpInst

/-- `IS.simplifyICmpInst.L3881`: `icmp X, poison` to poison. -/
theorem L3881 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (h : isPoison rhs = true) :
    Refines ((src p s lhs rhs).eval ρ) ((Repl.poison : Repl 1).eval ρ) := by
  rw [src_eval, isPoison_denote h, eval_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyICmpInst.L3887`: `icmp eq/ne X, undef` to `undef`, which without `undef` is about poison: both sides
are. -/
theorem L3887 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (u1 : rhs.hasUndef = false)
    (h : isUndefValue rhs = true) : Refines ((src p s lhs rhs).eval ρ) ((Repl.old (.undef : Term 1)).eval ρ) := by
  rw [src_eval, isUndefValue_denote h u1, eval_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyICmpInst.L3892`: `icmp X, X` to whether the predicate holds on equal values; `icmp X, undef` too,
which without `undef` is `icmp X, poison`. -/
theorem L3892 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (u1 : rhs.hasUndef = false)
    (h : (specific lhs rhs || isUndefValue rhs) = true) :
    Refines ((src p s lhs rhs).eval ρ) ((getBool (isTrueWhenEqual p)).eval ρ) := by
  rw [getBool_eval]
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · refine src_refines_const fun x y hx hy => ?_
    rw [specific_denote h, hx] at hy
    cases hy
    exact test_self p x
  · rw [src_eval, isUndefValue_denote h u1, eval_none_right]
    exact refines_ok (Refine.val_none _)

/-- `IS.simplifyICmpInst.L3910`: `icmp X, Y` to true, where the `!range`s of `X` and `Y` say every pair satisfies
it. -/
theorem L3910 (ρ : Env) (e : Ext) (he : e.Sound ρ) (p : Pred) (s : Bool) (lhs rhs : Term w) (rc lc : CR w)
    (hw : 0 < w) (hr : e.getRange rhs = some rc) (hl : e.getRange lhs = some lc) (h : lc.icmp p rc = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  exact src_refines_const fun x y hx hy =>
    CR.icmp_sound hw h (he.getRange lhs lc x hl hx) (he.getRange rhs rc y hr hy)

/-- `IS.simplifyICmpInst.L3913`: `icmp X, Y` to false, where the `!range`s of `X` and `Y` say every pair satisfies the
inverse predicate. -/
theorem L3913 (ρ : Env) (e : Ext) (he : e.Sound ρ) (p : Pred) (s : Bool) (lhs rhs : Term w) (rc lc : CR w)
    (hw : 0 < w) (hr : e.getRange rhs = some rc) (hl : e.getRange lhs = some lc)
    (h : lc.icmp (inverse p) rc = true) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  have := CR.icmp_sound hw h (he.getRange lhs lc x hl hx) (he.getRange rhs rc y hr hy)
  rw [test_inverse] at this
  simpa using this

/-- The values of `zext X` and `sext X` of one `X`. -/
theorem zext_sext_values {ρ : Env} {id id' : Nat} {nn : Bool} {v' : Nat} {x : Term v} {y : Term v'}
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (c1 : (Term.sext (w := w) id' y).Consistent ρ)
    (h : sameSrc x y = true) {a b : BitVec w} (ha : (Term.zext (w := w) id nn x).denote ρ = some a)
    (hb : (Term.sext (w := w) id' y).denote ρ = some b) : ∃ xv : BitVec v, a = xv.setWidth w ∧ b = xv.signExtend w := by
  obtain ⟨e, he⟩ := sameSrc_eq (ρ := ρ) h
  subst e
  obtain ⟨xv, hx, rfl⟩ := zext_denote c0 ha
  obtain ⟨yv, hy, rfl⟩ := sext_denote c1 hb
  rw [he, hx] at hy
  cases hy
  exact ⟨xv, rfl, rfl⟩

/-- `IS.simplifyICmpInst.L3959`: `zext X <=u sext X` and `zext X >=s sext X` to true. -/
theorem L3959 (ρ : Env) (p : Pred) (s : Bool) {id id' : Nat} {nn : Bool} {v' : Nat} (x : Term v) (y : Term v')
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (c1 : (Term.sext (w := w) id' y).Consistent ρ)
    (h : sameSrc x y = true) (hp : p = .ule ∨ p = .sge) :
    Refines ((src p s (Term.zext (w := w) id nn x) (Term.sext (w := w) id' y)).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := zext_sext_values c0 c1 h ha hb
  rcases hp with rfl | rfl
  · exact Lemmas.setWidth_ule_signExtend xv w
  · exact Lemmas.signExtend_sle_setWidth xv w

/-- `IS.simplifyICmpInst.L3961`: `zext X >u sext X` and `zext X <s sext X` to false. -/
theorem L3961 (ρ : Env) (p : Pred) (s : Bool) {id id' : Nat} {nn : Bool} {v' : Nat} (x : Term v) (y : Term v')
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (c1 : (Term.sext (w := w) id' y).Consistent ρ)
    (h : sameSrc x y = true) (hp : p = .ugt ∨ p = .slt) :
    Refines ((src p s (Term.zext (w := w) id nn x) (Term.sext (w := w) id' y)).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := zext_sext_values c0 c1 h ha hb
  rcases hp with rfl | rfl
  · have := Lemmas.setWidth_ule_signExtend xv w
    simp only [test]
    rw [BitVec.ule_eq_not_ult] at this
    simpa using this
  · have := Lemmas.signExtend_sle_setWidth xv w
    simp only [test]
    rw [BitVec.sle_eq_not_slt] at this
    simpa using this

/-- The value of `zext X` against a constant that isn't a zero extension from `X`'s width. -/
theorem zext_value {ρ : Env} {id : Nat} {nn : Bool} {x : Term v} (c0 : (Term.zext (w := w) id nn x).Consistent ρ)
    {a : BitVec w} (ha : (Term.zext (w := w) id nn x).denote ρ = some a) : ∃ xv : BitVec v, a = xv.setWidth w := by
  obtain ⟨xv, -, rfl⟩ := zext_denote c0 ha
  exact ⟨xv, rfl⟩

/-- `IS.simplifyICmpInst.L4000`: `zext X ==, >u, >=u C` to false, where `C` has a bit set above `X`'s width. -/
theorem L4000 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} {nn : Bool} (x : Term v) (c : BitVec w)
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (h : (c.setWidth v).setWidth w ≠ c)
    (hp : p = .eq ∨ p = .ugt ∨ p = .uge) :
    Refines ((src p s (.zext id nn x) (.const c)).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, rfl⟩ := zext_value c0 ha
  have hlt := Lemmas.setWidth_ult_of_ne xv h
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq] at hlt
  rcases hp with rfl | rfl | rfl <;> simp only [test, BitVec.ult_eq_decide, BitVec.ule_eq_decide]
  · simp only [beq_eq_false_iff_ne, ne_eq, BitVec.toNat_eq]; omega
  · simp only [decide_eq_false_iff_not]; omega
  · simp only [decide_eq_false_iff_not]; omega

/-- `IS.simplifyICmpInst.L4005`: `zext X !=, <u, <=u C` to true, where `C` has a bit set above `X`'s width. -/
theorem L4005 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} {nn : Bool} (x : Term v) (c : BitVec w)
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (h : (c.setWidth v).setWidth w ≠ c)
    (hp : p = .ne ∨ p = .ult ∨ p = .ule) :
    Refines ((src p s (.zext id nn x) (.const c)).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, rfl⟩ := zext_value c0 ha
  have hlt := Lemmas.setWidth_ult_of_ne xv h
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq] at hlt
  rcases hp with rfl | rfl | rfl <;> simp only [test, BitVec.ult_eq_decide, BitVec.ule_eq_decide]
  · simp only [bne_iff_ne, ne_eq, BitVec.toNat_eq]; omega
  · simp only [decide_eq_true_eq]; omega
  · simp only [decide_eq_true_eq]; omega

/-- `IS.simplifyICmpInst.L4011`: `zext X >s, >=s C` to `C <s 0`, where `C` has a bit set above `X`'s width. -/
theorem L4011 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} {nn : Bool} (x : Term v) (c : BitVec w)
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (h : (c.setWidth v).setWidth w ≠ c) (hp : p = .sgt ∨ p = .sge) :
    Refines ((src p s (.zext id nn x) (.const c)).eval ρ) ((getBool (BitVec.slt c 0#w)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, rfl⟩ := zext_value c0 ha
  rw [BitVec.slt_zero_eq_msb]
  rcases hp with rfl | rfl
  · exact Lemmas.slt_setWidth_of_ne xv h
  · exact Lemmas.sle_setWidth_of_ne xv h

/-- `IS.simplifyICmpInst.L4016`: `zext X <s, <=s C` to `C >=s 0`, where `C` has a bit set above `X`'s width. -/
theorem L4016 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} {nn : Bool} (x : Term v) (c : BitVec w)
    (c0 : (Term.zext (w := w) id nn x).Consistent ρ) (h : (c.setWidth v).setWidth w ≠ c) (hp : p = .slt ∨ p = .sle) :
    Refines ((src p s (.zext id nn x) (.const c)).eval ρ) ((getBool (BitVec.sle 0#w c)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, rfl⟩ := zext_value c0 ha
  rw [BitVec.zero_sle_eq_not_msb]
  rcases hp with rfl | rfl
  · exact Lemmas.setWidth_slt_of_ne xv h
  · exact Lemmas.setWidth_sle_of_ne xv h

/-- The values of `sext X` and `zext X` of one `X`. -/
theorem sext_zext_values {ρ : Env} {id id' : Nat} {nn : Bool} {v' : Nat} {x : Term v} {y : Term v'}
    (c0 : (Term.sext (w := w) id x).Consistent ρ) (c1 : (Term.zext (w := w) id' nn y).Consistent ρ)
    (h : sameSrc x y = true) {a b : BitVec w} (ha : (Term.sext (w := w) id x).denote ρ = some a)
    (hb : (Term.zext (w := w) id' nn y).denote ρ = some b) : ∃ xv : BitVec v, a = xv.signExtend w ∧ b = xv.setWidth w := by
  obtain ⟨e, he⟩ := sameSrc_eq (ρ := ρ) h
  subst e
  obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
  obtain ⟨yv, hy, rfl⟩ := zext_denote c1 hb
  rw [he, hx] at hy
  cases hy
  exact ⟨xv, rfl, rfl⟩

/-- `IS.simplifyICmpInst.L4038`: `sext X >=u zext X` and `sext X <=s zext X` to true. -/
theorem L4038 (ρ : Env) (p : Pred) (s : Bool) {id id' : Nat} {nn : Bool} {v' : Nat} (x : Term v) (y : Term v')
    (c0 : (Term.sext (w := w) id x).Consistent ρ) (c1 : (Term.zext (w := w) id' nn y).Consistent ρ)
    (h : sameSrc x y = true) (hp : p = .uge ∨ p = .sle) :
    Refines ((src p s (Term.sext (w := w) id x) (Term.zext (w := w) id' nn y)).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := sext_zext_values c0 c1 h ha hb
  rcases hp with rfl | rfl
  · exact Lemmas.setWidth_ule_signExtend xv w
  · exact Lemmas.signExtend_sle_setWidth xv w

/-- `IS.simplifyICmpInst.L4040`: `sext X <u zext X` and `sext X >s zext X` to false. -/
theorem L4040 (ρ : Env) (p : Pred) (s : Bool) {id id' : Nat} {nn : Bool} {v' : Nat} (x : Term v) (y : Term v')
    (c0 : (Term.sext (w := w) id x).Consistent ρ) (c1 : (Term.zext (w := w) id' nn y).Consistent ρ)
    (h : sameSrc x y = true) (hp : p = .ult ∨ p = .sgt) :
    Refines ((src p s (Term.sext (w := w) id x) (Term.zext (w := w) id' nn y)).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := sext_zext_values c0 c1 h ha hb
  rcases hp with rfl | rfl
  · have := Lemmas.setWidth_ule_signExtend xv w
    simp only [test]
    rw [BitVec.ule_eq_not_ult] at this
    simpa using this
  · have := Lemmas.signExtend_sle_setWidth xv w
    simp only [test]
    rw [BitVec.sle_eq_not_slt] at this
    simpa using this

theorem sext_value {ρ : Env} {id : Nat} {x : Term v} (c0 : (Term.sext (w := w) id x).Consistent ρ)
    {a : BitVec w} (ha : (Term.sext (w := w) id x).denote ρ = some a) :
    ∃ xv : BitVec v, x.denote ρ = some xv ∧ a = xv.signExtend w := sext_denote c0 ha

/-- `IS.simplifyICmpInst.L4074`: `sext X == C` to false, where `C` isn't a sign extension from `X`'s width. -/
theorem L4074 (ρ : Env) (s : Bool) {id : Nat} (x : Term v) (c : BitVec w) (c0 : (Term.sext (w := w) id x).Consistent ρ)
    (h : (c.setWidth v).signExtend w ≠ c) : Refines ((src .eq s (.sext id x) (.const c)).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, -, rfl⟩ := sext_value c0 ha
  simpa [test] using Lemmas.signExtend_ne_of_ne xv h

/-- `IS.simplifyICmpInst.L4076`: `sext X != C` to true, where `C` isn't a sign extension from `X`'s width. -/
theorem L4076 (ρ : Env) (s : Bool) {id : Nat} (x : Term v) (c : BitVec w) (c0 : (Term.sext (w := w) id x).Consistent ρ)
    (h : (c.setWidth v).signExtend w ≠ c) : Refines ((src .ne s (.sext id x) (.const c)).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, -, rfl⟩ := sext_value c0 ha
  simpa [test] using Lemmas.signExtend_ne_of_ne xv h

/-- `IS.simplifyICmpInst.L4082`: `sext X >s, >=s C` to `C <s 0`, where `C` isn't a sign extension from `X`'s
width. -/
theorem L4082 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} (x : Term v) (c : BitVec w)
    (c0 : (Term.sext (w := w) id x).Consistent ρ) (h : (c.setWidth v).signExtend w ≠ c) (hp : p = .sgt ∨ p = .sge) :
    Refines ((src p s (.sext id x) (.const c)).eval ρ) ((getBool (BitVec.slt c 0#w)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, -, rfl⟩ := sext_value c0 ha
  rw [BitVec.slt_zero_eq_msb]
  rcases hp with rfl | rfl
  · exact Lemmas.slt_signExtend_of_ne xv h
  · exact Lemmas.sle_signExtend_of_ne xv h

/-- `IS.simplifyICmpInst.L4087`: `sext X <s, <=s C` to `C >=s 0`, where `C` isn't a sign extension from `X`'s
width. -/
theorem L4087 (ρ : Env) (p : Pred) (s : Bool) {id : Nat} (x : Term v) (c : BitVec w)
    (c0 : (Term.sext (w := w) id x).Consistent ρ) (h : (c.setWidth v).signExtend w ≠ c) (hp : p = .slt ∨ p = .sle) :
    Refines ((src p s (.sext id x) (.const c)).eval ρ) ((getBool (BitVec.sle 0#w c)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun a b ha hb => ?_
  cases hb
  obtain ⟨xv, -, rfl⟩ := sext_value c0 ha
  rw [BitVec.zero_sle_eq_not_msb]
  rcases hp with rfl | rfl
  · exact Lemmas.signExtend_slt_of_ne xv h
  · exact Lemmas.signExtend_sle_of_ne xv h

/-- `IS.simplifyICmpInst.L4122`: `X == Y` to false and `X != Y` to true, where `isKnownNonEqual(X, Y)`. -/
theorem L4122 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (hp : isEquality p = true) (h : o.nonEqual lhs rhs = true) :
    Refines ((src p s lhs rhs).eval ρ) ((if p == .ne then getTrue else getFalse).eval ρ) := by
  cases p <;> simp only [isEquality, Bool.false_eq_true] at hp
  · show Refines _ (getFalse.eval ρ)
    rw [getFalse_eval]
    refine src_refines_const fun x y hx hy => ?_
    show (x == y) = false
    simpa using ho.nonEqual lhs rhs x y h hx hy
  · show Refines _ (getTrue.eval ρ)
    rw [getTrue_eval]
    refine src_refines_const fun x y hx hy => ?_
    show (x != y) = true
    simpa using ho.nonEqual lhs rhs x y h hx hy

/-- `IS.simplifyICmpInst.L4148`: `icmp X, Y` to what a dominating condition says it is. -/
theorem L4148 (ρ : Env) (e : Ext) (he : e.Sound ρ) (p : Pred) (s : Bool) (lhs rhs : Term w) (b : Bool)
    (h : e.domCond p lhs rhs = some b) : Refines ((src p s lhs rhs).eval ρ) ((getBool b).eval ρ) := by
  rw [getBool_eval]
  exact src_refines_const fun x y hx hy => he.domCond p lhs rhs b x y h hx hy

end simplifyICmpInst

end Peephole.IS

/-! ### The steps that forward, and those of the cast section -/

namespace Peephole.IS.simplifyICmpInst

open IRLean ICmp

variable {w : Nat}

/-- What `simplifyICmpInst`'s steps assume of the model one level of `MaxRecurse` down: each value it returns
refines its `icmp`. `body_sound` discharges it by induction on `MaxRecurse`. -/
def RecSound (ρ : Env) (rec : ICmp.Rec) : Prop :=
  ∀ {v : Nat} (p : Pred) (a b : Term v) (r : Repl 1), a.Consistent ρ → b.Consistent ρ → a.hasUndef = false →
    b.hasUndef = false → run (rec p a b) = .value r → Refines ((src p false a b).eval ρ) (r.eval ρ)

section steps

variable {ρ : Env} {rec : ICmp.Rec} (hrec : RecSound ρ rec) {p : Pred} {s : Bool} {lhs rhs : Term w} {n : Nat}
  (c0 : lhs.Consistent ρ) (c1 : rhs.Consistent ρ) (u0 : lhs.hasUndef = false) (u1 : rhs.hasUndef = false)
  {site : String} {r : Repl 1}

include hrec c0 c1 u0 u1 in
theorem zextZext_sound (h : zextZext rec p lhs rhs n = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold zextZext at h
  split at h
  · rename_i v id nn x v' id' nn' y
    split at h
    · next y' hy =>
      split at h
      · next hc =>
        obtain ⟨e, rfl⟩ := sameWidth_eq hy
        cases e
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
        have c0' := c0
        have c1' := c1
        simp only [Term.Consistent] at c0' c1'
        simp only [Term.hasUndef] at u0 u1
        refine src_refines_via (fun a b ha hb => ?_) (hrec (unsigned p) x y r c0'.1 c1'.1 u0 u1 (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := zext_denote c0 ha
        obtain ⟨yv, hy, rfl⟩ := zext_denote c1 hb
        exact ⟨xv, yv, hx, hy, test_setWidth p xv yv hc.2⟩
      · cases h
    · cases h
  · cases h

include c0 c1 in
theorem zextSextTrue_sound (h : zextSextTrue p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold zextSextTrue at h
  split at h
  · rename_i v id nn x v' id' y
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L3959 ρ p s x y c0 c1 hc.1 hc.2
  · cases h

include c0 c1 in
theorem zextSextFalse_sound (h : zextSextFalse p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold zextSextFalse at h
  split at h
  · rename_i v id nn x v' id' y
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L3961 ρ p s x y c0 c1 hc.1 hc.2
  · cases h

include hrec c0 u0 in
theorem zextConstRec_sound (h : zextConstRec rec p lhs rhs n = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold zextConstRec at h
  split at h
  · rename_i v id nn x c
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨hce, -⟩, hvw⟩ := hc
      have c0' := c0
      simp only [Term.Consistent] at c0'
      simp only [Term.hasUndef] at u0
      refine src_refines_via (fun a b ha hb => ?_)
        (hrec (unsigned p) x (.const (c.setWidth v)) r c0'.1 trivial u0 rfl (fwd_fire h))
      obtain ⟨xv, hx, rfl⟩ := zext_denote c0 ha
      cases hb
      refine ⟨xv, c.setWidth v, hx, rfl, ?_⟩
      conv => lhs; rw [← hce]
      exact test_setWidth p xv _ hvw
    · cases h
  · cases h

include c0 in
theorem zextConstNull_sound (h : zextConstNull p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold zextConstNull at h
  split at h
  · rename_i v id nn x c
    split at h
    · next hc =>
      simp only [bne_iff_ne, ne_eq] at hc
      split at h <;> simp only [Step.fire.injEq] at h <;> obtain ⟨-, rfl⟩ := h
      · exact L4000 ρ _ s x c c0 hc (by simp)
      · exact L4000 ρ _ s x c c0 hc (by simp)
      · exact L4000 ρ _ s x c c0 hc (by simp)
      · exact L4005 ρ _ s x c c0 hc (by simp)
      · exact L4005 ρ _ s x c c0 hc (by simp)
      · exact L4005 ρ _ s x c c0 hc (by simp)
      · exact L4011 ρ _ s x c c0 hc (by simp)
      · exact L4011 ρ _ s x c c0 hc (by simp)
      · exact L4016 ρ _ s x c c0 hc (by simp)
      · exact L4016 ρ _ s x c c0 hc (by simp)
    · cases h
  · cases h

include hrec c0 c1 u0 u1 in
theorem sextSext_sound (h : sextSext rec p lhs rhs n = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextSext at h
  split at h
  · rename_i v id x v' id' y
    split at h
    · next y' hy =>
      split at h
      · next hc =>
        obtain ⟨e, rfl⟩ := sameWidth_eq hy
        cases e
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
        have c0' := c0
        have c1' := c1
        simp only [Term.Consistent] at c0' c1'
        simp only [Term.hasUndef] at u0 u1
        refine src_refines_via (fun a b ha hb => ?_) (hrec p x y r c0'.1 c1'.1 u0 u1 (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
        obtain ⟨yv, hy, rfl⟩ := sext_denote c1 hb
        exact ⟨xv, yv, hx, hy, test_signExtend p xv yv (Nat.le_of_lt hc.2)⟩
      · cases h
    · cases h
  · cases h

include c0 c1 in
theorem sextZextTrue_sound (h : sextZextTrue p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextZextTrue at h
  split at h
  · rename_i v id x v' id' nn y
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L4038 ρ p s x y c0 c1 hc.1 hc.2
  · cases h

include c0 c1 in
theorem sextZextFalse_sound (h : sextZextFalse p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextZextFalse at h
  split at h
  · rename_i v id x v' id' nn y
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L4040 ρ p s x y c0 c1 hc.1 hc.2
  · cases h

include hrec c0 u0 in
theorem sextConstRec_sound (h : sextConstRec rec p lhs rhs n = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextConstRec at h
  split at h
  · rename_i v id x c
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨hce, -⟩, hvw⟩ := hc
      have c0' := c0
      simp only [Term.Consistent] at c0'
      simp only [Term.hasUndef] at u0
      refine src_refines_via (fun a b ha hb => ?_)
        (hrec p x (.const (c.setWidth v)) r c0'.1 trivial u0 rfl (fwd_fire h))
      obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
      cases hb
      refine ⟨xv, c.setWidth v, hx, rfl, ?_⟩
      conv => lhs; rw [← hce]
      exact test_signExtend p xv _ (Nat.le_of_lt hvw)
    · cases h
  · cases h

include c0 in
theorem sextConstNull_sound (h : sextConstNull p lhs rhs = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextConstNull at h
  split at h
  · rename_i v id x c
    split at h
    · next hc =>
      simp only [bne_iff_ne, ne_eq] at hc
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;> obtain ⟨-, rfl⟩ := h
      · exact L4074 ρ s x c c0 hc
      · exact L4076 ρ s x c c0 hc
      · exact L4082 ρ _ s x c c0 hc (by simp)
      · exact L4082 ρ _ s x c c0 hc (by simp)
      · exact L4087 ρ _ s x c c0 hc (by simp)
      · exact L4087 ρ _ s x c c0 hc (by simp)
    · cases h
  · cases h

include hrec c0 u0 in
theorem sextConstSign_sound (h : sextConstSign rec p lhs rhs n = .fire site r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold sextConstSign at h
  split at h
  · rename_i v id x c
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      have hne := hc.1
      have c0' := c0
      simp only [Term.Consistent] at c0'
      simp only [Term.hasUndef] at u0
      split at h
      · -- Comparison is true iff the LHS <s 0.
        refine src_refines_via (fun a b ha hb => ?_)
          (hrec .slt x (.const 0#v) r c0'.1 trivial u0 rfl (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
        cases hb
        refine ⟨xv, 0#v, hx, rfl, ?_⟩
        simp only [test, BitVec.slt_zero_eq_msb, Lemmas.ult_signExtend_of_ne xv hne]
      · refine src_refines_via (fun a b ha hb => ?_)
          (hrec .slt x (.const 0#v) r c0'.1 trivial u0 rfl (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
        cases hb
        refine ⟨xv, 0#v, hx, rfl, ?_⟩
        simp only [test, BitVec.slt_zero_eq_msb, Lemmas.ule_signExtend_of_ne xv hne]
      · -- Comparison is true iff the LHS >=s 0.
        refine src_refines_via (fun a b ha hb => ?_)
          (hrec .sge x (.const 0#v) r c0'.1 trivial u0 rfl (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
        cases hb
        refine ⟨xv, 0#v, hx, rfl, ?_⟩
        simp only [test, BitVec.zero_sle_eq_not_msb, BitVec.ult_eq_decide]
        rw [← Lemmas.ule_signExtend_of_ne xv hne, BitVec.ule_eq_decide]
        simp only [← decide_not, Nat.not_le]
      · refine src_refines_via (fun a b ha hb => ?_)
          (hrec .sge x (.const 0#v) r c0'.1 trivial u0 rfl (fwd_fire h))
        obtain ⟨xv, hx, rfl⟩ := sext_denote c0 ha
        cases hb
        refine ⟨xv, 0#v, hx, rfl, ?_⟩
        simp only [test, BitVec.zero_sle_eq_not_msb, BitVec.ule_eq_decide]
        rw [← Lemmas.ult_signExtend_of_ne xv hne, BitVec.ult_eq_decide]
        simp only [← decide_not, Nat.not_lt]
      · cases h
    · cases h
  · cases h

end steps

/-! ### The fold -/

/-- Every step of `simplifyICmpInst` that fires is right, given that the model one level down is. -/
theorem steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ) {rec : ICmp.Rec}
    (hrec : RecSound ρ rec) (p : Pred) (s : Bool) (lhs rhs : Term w) (n : Nat) (c0 : lhs.Consistent ρ)
    (c1 : rhs.Consistent ρ) (u0 : lhs.hasUndef = false) (u1 : rhs.hasUndef = false) :
    ∀ site r, Step.fire site r ∈ steps o e rec p lhs rhs n → Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact L3881 ρ p s lhs rhs (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact L3887 ρ p s lhs rhs u1 hc.1
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    exact L3892 ρ p s lhs rhs u1 hc
  · exact simplifyICmpOfBools.sound ρ o ho p s lhs rhs c0 (fwdR_fire h.symm)
  · exact simplifyICmpWithZero.sound ρ o ho p s lhs rhs (fwdR_fire h.symm)
  · exact simplifyICmpWithConstant.sound ρ o ho e he p s lhs rhs c0 (fwdR_fire h.symm)
  · split at h
    · next rc lc hr hl =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact L3910 ρ e he p s lhs rhs rc lc (Nat.pos_of_ne_zero hc.1) hr hl hc.2
    · cases h
  · split at h
    · next rc lc hr hl =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      exact L3913 ρ e he p s lhs rhs rc lc (Nat.pos_of_ne_zero hc.1) hr hl hc.2
    · cases h
  · exact zextZext_sound hrec c0 c1 u0 u1 h.symm
  · exact zextSextTrue_sound c0 c1 h.symm
  · exact zextSextFalse_sound c0 c1 h.symm
  · exact zextConstRec_sound hrec c0 u0 h.symm
  · exact zextConstNull_sound c0 h.symm
  · exact sextSext_sound hrec c0 c1 u0 u1 h.symm
  · exact sextZextTrue_sound c0 c1 h.symm
  · exact sextZextFalse_sound c0 c1 h.symm
  · exact sextConstRec_sound hrec c0 u0 h.symm
  · exact sextConstNull_sound c0 h.symm
  · exact sextConstSign_sound hrec c0 u0 h.symm
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact L4122 ρ o ho p s lhs rhs hc.1.1 hc.2
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifyICmpUsingMonotonicValues.sound ρ o ho p s lhs rhs c0 c1 (fwdR_fire h.symm)
  · rw [← src_swap]
    exact simplifyICmpUsingMonotonicValues.sound ρ o ho (swap p) s rhs lhs c1 c0 (fwdR_fire h.symm)
  · cases h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next b hb =>
    obtain ⟨-, rfl⟩ := h
    exact L4148 ρ e he p s lhs rhs b hb
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h

/-- `entry`: two constants go to the constant folder, and a lone constant on the left moves right with the
predicate swapped, which compares the same values. -/
theorem entry_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ) {rec : ICmp.Rec}
    (hrec : RecSound ρ rec) (p : Pred) (s : Bool) (lhs rhs : Term w) (n : Nat) (c0 : lhs.Consistent ρ)
    (c1 : rhs.Consistent ρ) (u0 : lhs.hasUndef = false) (u1 : rhs.hasUndef = false) {r : Repl 1}
    (h : run (entry o e rec p lhs rhs n) = .value r) : Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold entry at h
  split at h
  · split at h
    · simp [run] at h
    · rw [← src_swap]
      exact run_sound (steps_sound ρ o ho e he hrec (swap p) s rhs lhs n c1 c0 u1 u0) h
  · exact run_sound (steps_sound ρ o ho e he hrec p s lhs rhs n c0 c1 u0 u1) h

/-- The model at every `MaxRecurse` is right: by induction, each level's recursive calls are. -/
theorem body_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ) :
    ∀ (n : Nat), RecSound ρ (body o e n)
  | 0 => fun p a b r ca cb ua ub h => by
    simp only [body] at h
    exact entry_sound ρ o ho e he (rec := fun _ _ _ => []) (fun _ _ _ _ _ _ _ _ h' => by simp [run] at h')
      p false a b 0 ca cb ua ub h
  | n + 1 => fun p a b r ca cb ua ub h => by
    simp only [body] at h
    exact entry_sound ρ o ho e he (body_sound ρ o ho e he n) p false a b (n + 1) ca cb ua ub h

end Peephole.IS.simplifyICmpInst

namespace Peephole.IS

open IRLean ICmp

/-- Theorem 1 for `simplifyICmpInst`: every value the model returns refines the `icmp` it replaces, with or without
`samesign`, at every width and every `MaxRecurse`, in every run its operands are consistent with, poison included,
given sound analyses, the extension's among them. It says nothing about operands that reach an `undef`. -/
theorem simplifyICmpInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ) {w : Nat}
    (p : Pred) (s : Bool) (lhs rhs : Term w) (n : Nat) (c0 : lhs.Consistent ρ) (c1 : rhs.Consistent ρ)
    (u0 : lhs.hasUndef = false) (u1 : rhs.hasUndef = false) {r : Repl 1}
    (h : simplifyICmpInst o e p lhs rhs n = .value r) : Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold simplifyICmpInst at h
  cases n with
  | zero =>
    simp only [simplifyICmpInst.body] at h
    exact simplifyICmpInst.entry_sound ρ o ho e he (rec := fun _ _ _ => [])
      (fun _ _ _ _ _ _ _ _ h' => by simp [run] at h') p s lhs rhs 0 c0 c1 u0 u1 h
  | succ n =>
    simp only [simplifyICmpInst.body] at h
    exact simplifyICmpInst.entry_sound ρ o ho e he (simplifyICmpInst.body_sound ρ o ho e he n) p s lhs rhs (n + 1)
      c0 c1 u0 u1 h

/-- What `simplifyICmpInst.onInst` returns for an `icmp` refines it: the instruction, as `Term.top` has it. -/
theorem simplifyICmpInst.onInstWith_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ)
    {w : Nat} (t : Term w) (ct : t.Consistent ρ) (ut : t.hasUndef = false) {r : Repl w}
    (h : simplifyICmpInst.onInstWith o e t = .value r) : Refines (t.top.eval ρ) (r.eval ρ) := by
  cases t
  case icmp v id p s a b =>
    simp only [Term.Consistent] at ct
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at ut
    simp only [simplifyICmpInst.onInstWith, simplifyICmpInst.body_three] at h
    exact simplifyICmpInst.sound ρ o ho e he p s a b 3 ct.1 ct.2.1 ut.1 ut.2 h
  all_goals simp [simplifyICmpInst.onInstWith] at h

/-- What the entry point returns for an `icmp` refines it, given sound analyses. -/
theorem simplifyICmpInst.onInst_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) {w : Nat} (t : Term w)
    (ct : t.Consistent ρ) (ut : t.hasUndef = false) {r : Repl w} (h : simplifyICmpInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) :=
  simplifyICmpInst.onInstWith_sound ρ o ho Ext.none (Ext.none_sound ρ) t ct ut h

end Peephole.IS
