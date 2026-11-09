import Peephole.IS.IntrinsicBase

/-! # `simplifyBinaryIntrinsic`'s case for `umin`, `umax`, `smin` and `smax`, and `foldMinMaxSharedOp`

At `llvm/lib/Analysis/InstructionSimplify.cpp:6684-6704` and `6996-7058` at `llvmorg-23.1.3`. The case puts an
immediate constant second, then tries, in order:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyBinaryIntrinsic.L7004` | `max(x, x)` to `x` |
| `IS.simplifyBinaryIntrinsic.L7012` | `max(x, undef)` to the saturation point: without `undef`, of poison |
| `IS.simplifyBinaryIntrinsic.L7020` | `max(x, C)` to `C`, where `C` is the saturation point, such as `umax(x, -1)` |
| `IS.simplifyBinaryIntrinsic.L7027` | `max(x, C)` to `x`, `C` the inverse's saturation point, such as `umin(x, -1)` |
| `IS.simplifyBinaryIntrinsic.L7040` | `max(max(x, C1), C2)` to `max(x, C1)`, where `C1 >= C2` |
| `IS.foldMinMaxSharedOp.L6698` | `max(max(x, y), z)` to `max(x, y)`, where `z` is `x`, `y`, or a min or max of them |
| `IS.foldMinMaxSharedOp.L6701` | `max(min(x, y), z)` to `z`, where `z` is `x`, `y`, or a min or max of them |
| `IS.simplifyBinaryIntrinsic.L7052` | `max(x, y)` to `x`, where `isICmpTrue` says `x >= y` |
| `IS.simplifyBinaryIntrinsic.L7054` | `max(x, y)` to `y`, where `isICmpTrue` says `y >= x` |

"max" stands for each of the four, with its own order, saturation point and inverse. `foldMinMaxSharedOp` is
called twice, with the operands each way round. At this pin `m_MaxOrMin` and `m_c_MaxOrMin` are `m_Intrinsic`s only,
with no `select` form. -/

namespace Peephole.IS

open IRLean Intrinsic

variable {w : Nat}

/-! ### Facts about `umin`, `umax`, `smin` and `smax`, from the lemmas about each -/

private theorem minMax_self {f : BinIntr} (hf : isMinMax f = true) (a : Val w) : f.eval a a = a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_self a
  · exact Lemmas.umax_self a
  · exact Lemmas.smin_self a
  · exact Lemmas.smax_self a

private theorem minMax_comm {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) : f.eval a b = f.eval b a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_comm a b
  · exact Lemmas.umax_comm a b
  · exact Lemmas.smin_comm a b
  · exact Lemmas.smax_comm a b

/-- A min or max with its saturation point is that point. -/
private theorem minMax_satPoint {f : BinIntr} (hf : isMinMax f = true) (a : Val w) :
    Refines (f.eval a (some (satPoint f w))) (some (satPoint f w)) := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, satPoint]
  · exact Lemmas.umin_zero_refines a
  · exact Lemmas.umax_allOnes_refines a
  · exact Lemmas.smin_intMin_refines a
  · exact Lemmas.smax_intMax_refines a

/-- A min or max with its inverse's saturation point is the other operand. -/
private theorem minMax_inverse_satPoint {f : BinIntr} (hf : isMinMax f = true) (a : Val w) :
    f.eval a (some (satPoint (inverse f) w)) = a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, satPoint, inverse]
  · exact Lemmas.umin_allOnes a
  · exact Lemmas.umax_zero a
  · exact Lemmas.smin_intMax a
  · exact Lemmas.smax_intMin a

/-- `max(max(x, c), d)` is `max(x, c)` if `c ≥ d`, by the non-strict predicate. -/
private theorem minMax_nested {f : BinIntr} (hf : isMinMax f = true) (a : Val w) {c d : BitVec w}
    (h : compare (nonStrictPred f) c d = true) : f.eval (f.eval a (some c)) (some d) = f.eval a (some c) := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [Intrinsic.compare, nonStrictPred, Pred.eval, Val.icmpUle, Val.icmpUge, Val.icmpSle, Val.icmpSge,
      Val.icmp, Bool.false_and, Bool.false_eq_true, ite_false, beq_iff_eq, Option.some.injEq] at h <;>
    simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_of_ule a (by cases hc : c.ule d <;> simp_all)
  · exact Lemmas.umax_umax_of_ule a (by cases hc : d.ule c <;> simp_all)
  · exact Lemmas.smin_smin_of_sle a (by cases hc : c.sle d <;> simp_all)
  · exact Lemmas.smax_smax_of_sle a (by cases hc : d.sle c <;> simp_all)

private theorem minMax_left {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    f.eval (f.eval a b) a = f.eval a b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_left a b
  · exact Lemmas.umax_umax_left a b
  · exact Lemmas.smin_smin_left a b
  · exact Lemmas.smax_smax_left a b

private theorem minMax_right {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    f.eval (f.eval a b) b = f.eval a b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval]
  · exact Lemmas.umin_umin_right a b
  · exact Lemmas.umax_umax_right a b
  · exact Lemmas.smin_smin_right a b
  · exact Lemmas.smax_smax_right a b

/-- `max(min(x, y), x)` refines `x`. -/
private theorem minMax_inverse_left {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    Refines (f.eval ((inverse f).eval a b) a) a := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, inverse]
  · exact Lemmas.umin_umax_left_refines a b
  · exact Lemmas.umax_umin_left_refines a b
  · exact Lemmas.smin_smax_left_refines a b
  · exact Lemmas.smax_smin_left_refines a b

private theorem minMax_inverse_right {f : BinIntr} (hf : isMinMax f = true) (a b : Val w) :
    Refines (f.eval ((inverse f).eval a b) b) b := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;> simp only [BinIntr.eval, inverse]
  · exact Lemmas.umin_umax_right_refines a b
  · exact Lemmas.umax_umin_right_refines a b
  · exact Lemmas.smin_smax_right_refines a b
  · exact Lemmas.smax_smin_right_refines a b

/-- A min or max of two values is one of them. -/
private theorem minMax_some_mem {f : BinIntr} (hf : isMinMax f = true) (x y : BitVec w) :
    f.eval (some x) (some y) = some x ∨ f.eval (some x) (some y) = some y := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [BinIntr.eval, Val.umin, Val.umax, Val.smin, Val.smax, Val.map₂] <;> split <;> simp

/-- A min or max of two values whose non-strict predicate holds of them is the first. -/
private theorem minMax_of_pred {f : BinIntr} (hf : isMinMax f = true) {x y : BitVec w}
    (h : (nonStrictPred f).eval (some x) (some y) false = some 1#1) : f.eval (some x) (some y) = some x := by
  cases f <;> simp only [isMinMax, Bool.false_eq_true] at hf <;>
    simp only [nonStrictPred, Pred.eval, Val.icmpUle, Val.icmpUge, Val.icmpSle, Val.icmpSge, Val.icmp,
      Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq] at h <;>
    simp only [BinIntr.eval]
  · exact Lemmas.umin_of_ule (by cases hc : x.ule y <;> simp_all)
  · exact Lemmas.umax_of_ule (by cases hc : y.ule x <;> simp_all)
  · exact Lemmas.smin_of_sle (by cases hc : x.sle y <;> simp_all)
  · exact Lemmas.smax_of_sle (by cases hc : y.sle x <;> simp_all)

/-! ### Matchers -/

/-- `m_MaxOrMin(m_Value(X), m_Value(Y))`: an `smax`, `smin`, `umax` or `umin` call, binding its operands, with the
intrinsic, which `MM0->getIntrinsicID()` reads. -/
def Intrinsic.maxOrMin? : Term w → Option (BinIntr × Term w × Term w)
  | .bi _ f x y => if isMinMax f then some (f, x, y) else none
  | _ => none

/-- `Op1 == X || Op1 == Y || match(Op1, m_c_MaxOrMin(m_Specific(X), m_Specific(Y)))`. -/
def Intrinsic.sharesOp (x y op1 : Term w) : Bool :=
  specific x op1 || specific y op1 ||
    match maxOrMin? op1 with
    | some (_, a, b) => (specific x a && specific y b) || (specific x b && specific y a)
    | none => false

/-- `if (match(Op0, m_ImmConstant())) std::swap(Op0, Op1);`: the operands with an immediate constant second. -/
def Intrinsic.immSwap (op0 op1 : Term w) : Term w × Term w :=
  if op0.isConstant then (op1, op0) else (op0, op1)

/-- The nested call's constant: `Op0` the same intrinsic, `MinMax0->getIntrinsicID() == IID`, with
`match(M00, m_APInt(InnerC)) || match(M01, m_APInt(InnerC))`. -/
def Intrinsic.innerConst? (f : BinIntr) : Term w → Option (BitVec w)
  | .bi _ f0 m00 m01 => if f0 == f then (apint m00).orElse fun _ => apint m01 else none
  | _ => none

/-! ### The models -/

/-- `foldMinMaxSharedOp(IID, Op0, Op1)`, step by step. -/
def foldMinMaxSharedOp.steps (f : BinIntr) (op0 op1 : Term w) : List (Step w) :=
  [ -- if (!match(Op0, m_MaxOrMin(m_Value(X), m_Value(Y)))) return nullptr;
    if (maxOrMin? op0).isSome then .next else .decline,
    -- auto *MM0 = dyn_cast<IntrinsicInst>(Op0); if (!MM0) return nullptr;
    match op0 with
    | .bi .. => .next
    | _ => .decline,
    -- max (max X, Y), X --> max X, Y
    match maxOrMin? op0 with
    | some (f0, x, y) =>
      if sharesOp x y op1 && f0 == f then .fire "IS.foldMinMaxSharedOp.L6698" (.old op0) else .next
    | none => .next,
    -- max (min X, Y), X --> X
    match maxOrMin? op0 with
    | some (f0, x, y) =>
      if sharesOp x y op1 && f0 == inverse f then .fire "IS.foldMinMaxSharedOp.L6701" (.old op1) else .next
    | none => .next ]

/-- `simplifyBinaryIntrinsic`'s case for `smax`, `smin`, `umax` and `umin`, step by step. `r` is the recursive
`simplifyICmpInst` that `isICmpTrue` calls. -/
def simplifyBinaryIntrinsic.minMaxSteps (r : Recur) (f : BinIntr) (op0 op1 : Term w) : List (Step w) :=
  [ -- If the arguments are the same, this is a no-op.
    if specific op0 op1 then .fire "IS.simplifyBinaryIntrinsic.L7004" (.old op0) else .next,
    -- Canonicalize immediate constant operand as Op1. Assume undef is the limit value.
    if isUndefValue (immSwap op0 op1).2 then .fire "IS.simplifyBinaryIntrinsic.L7012" (.const (satPoint f w))
    else .next,
    -- Clamp to limit value. For example: umax(i8 %x, i8 255) --> 255
    match apint (immSwap op0 op1).2 with
    | some c => if c == satPoint f w then .fire "IS.simplifyBinaryIntrinsic.L7020" (.const c) else .next
    | none => .next,
    -- If the constant op is the opposite of the limit value, the other must be larger/smaller or equal. For
    -- example: umin(i8 %x, i8 255) --> %x
    match apint (immSwap op0 op1).2 with
    | some c =>
      if c == satPoint (inverse f) w then .fire "IS.simplifyBinaryIntrinsic.L7027" (.old (immSwap op0 op1).1)
      else .next
    | none => .next,
    -- Remove nested call if constant operands allow it. Example: max (max X, 7), 5 -> max X, 7
    match apint (immSwap op0 op1).2, innerConst? f (immSwap op0 op1).1 with
    | some c, some ic =>
      if compare (nonStrictPred f) ic c then .fire "IS.simplifyBinaryIntrinsic.L7040" (.old (immSwap op0 op1).1)
      else .next
    | _, _ => .next,
    forward (foldMinMaxSharedOp.steps f (immSwap op0 op1).1 (immSwap op0 op1).2),
    forward (foldMinMaxSharedOp.steps f (immSwap op0 op1).2 (immSwap op0 op1).1),
    match isICmpTrue r recursionLimit (nonStrictPred f) (immSwap op0 op1).1 (immSwap op0 op1).2 with
    | some true => .fire "IS.simplifyBinaryIntrinsic.L7052" (.old (immSwap op0 op1).1)
    | some false => .next
    | none => .delegate "simplifyICmpInst",
    match isICmpTrue r recursionLimit (nonStrictPred f) (immSwap op0 op1).2 (immSwap op0 op1).1 with
    | some true => .fire "IS.simplifyBinaryIntrinsic.L7054" (.old (immSwap op0 op1).2)
    | some false => .next
    | none => .delegate "simplifyICmpInst" ]

/-! ### What the matchers say about values -/

theorem bi_denote {ρ : Env} {id : Nat} {f : BinIntr} {x y : Term w} (c : (Term.bi id f x y).Consistent ρ) :
    (Term.bi id f x y).denote ρ = f.eval (x.denote ρ) (y.denote ρ) :=
  c.2.2.symm

theorem maxOrMin?_eq {t : Term w} {f : BinIntr} {x y : Term w} (h : maxOrMin? t = some (f, x, y)) :
    isMinMax f = true ∧ ∃ id, t = .bi id f x y := by
  cases t <;> simp only [maxOrMin?, reduceCtorEq] at h
  next id f' x' y' =>
    split at h
    · next hf => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨hf, id, rfl⟩
    · cases h

/-- What `sharesOp` says of `Op1`'s value: `X`'s, `Y`'s, or poison, since a min or max of `X` and `Y` is one of them
unless one is poison. -/
theorem sharesOp_denote {ρ : Env} {x y op1 : Term w} (h : sharesOp x y op1 = true) (c1 : op1.Consistent ρ) :
    op1.denote ρ = x.denote ρ ∨ op1.denote ρ = y.denote ρ ∨ op1.denote ρ = none := by
  simp only [sharesOp, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact .inl (specific_denote h)
  · exact .inr (.inl (specific_denote h))
  · split at h
    · next g a b hm =>
      obtain ⟨hg, id, rfl⟩ := maxOrMin?_eq hm
      rw [bi_denote c1]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · rw [specific_denote ha, specific_denote hb]
        cases hx : x.denote ρ with
        | none => exact .inr (.inr (BinIntr.eval_none_left _ _))
        | some u =>
          cases hy : y.denote ρ with
          | none => exact .inr (.inr (BinIntr.eval_none_right _ _))
          | some v => rcases minMax_some_mem hg u v with e | e <;> rw [e] <;> simp
      · rw [specific_denote ha, specific_denote hb]
        cases hx : x.denote ρ with
        | none => exact .inr (.inr (BinIntr.eval_none_right _ _))
        | some u =>
          cases hy : y.denote ρ with
          | none => exact .inr (.inr (BinIntr.eval_none_left _ _))
          | some v => rcases minMax_some_mem hg v u with e | e <;> rw [e] <;> simp
    · cases h

theorem immSwap_cases (op0 op1 : Term w) :
    (immSwap op0 op1 = (op0, op1)) ∨ (immSwap op0 op1 = (op1, op0)) := by
  unfold immSwap; split <;> simp

/-- A min or max of the operands is the same with an immediate constant second. -/
theorem minMax_immSwap {ρ : Env} {f : BinIntr} (hf : isMinMax f = true) (op0 op1 : Term w) :
    f.eval (op0.denote ρ) (op1.denote ρ) = f.eval ((immSwap op0 op1).1.denote ρ) ((immSwap op0 op1).2.denote ρ) := by
  rcases immSwap_cases op0 op1 with h | h <;> rw [h]
  exact minMax_comm hf _ _

/-! ### `foldMinMaxSharedOp`'s rewrites -/

/-- `IS.foldMinMaxSharedOp.L6698`: `max(max(x, y), z)` to `max(x, y)`, where `z` is `x`, `y`, or a min or max of
them. -/
theorem foldMinMaxSharedOp.L6698 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (id : Nat) (x y op1 : Term w)
    (c0 : (Term.bi id f x y).Consistent ρ) (c1 : op1.Consistent ρ) (h : sharesOp x y op1 = true) :
    Refines ((Repl.bi f (.old (Term.bi id f x y)) (.old op1)).eval ρ) ((Repl.old (Term.bi id f x y)).eval ρ) := by
  rw [bi_eval, Repl.eval_old, bi_denote c0]
  refine refines_ok ?_
  rcases sharesOp_denote h c1 with e | e | e <;> rw [e]
  · rw [minMax_left hf]; exact Refine.refl_val _
  · rw [minMax_right hf]; exact Refine.refl_val _
  · rw [BinIntr.eval_none_right]; exact Refine.val_none _

/-- `IS.foldMinMaxSharedOp.L6701`: `max(min(x, y), z)` to `z`, where `z` is `x`, `y`, or a min or max of them. -/
theorem foldMinMaxSharedOp.L6701 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (id : Nat) (x y op1 : Term w)
    (c0 : (Term.bi id (inverse f) x y).Consistent ρ) (c1 : op1.Consistent ρ) (h : sharesOp x y op1 = true) :
    Refines ((Repl.bi f (.old (Term.bi id (inverse f) x y)) (.old op1)).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [bi_eval, Repl.eval_old, bi_denote c0]
  refine refines_ok ?_
  rcases sharesOp_denote h c1 with e | e | e <;> rw [e]
  · exact minMax_inverse_left hf _ _
  · exact minMax_inverse_right hf _ _
  · rw [BinIntr.eval_none_right]; exact Refine.val_none _

/-- Every step of `foldMinMaxSharedOp` that fires is right. -/
theorem foldMinMaxSharedOp.steps_sound (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) :
    ∀ s r, Step.fire s r ∈ foldMinMaxSharedOp.steps f op0 op1 →
      Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [foldMinMaxSharedOp.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · next f0 x y hm =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hs, rfl⟩ := hc
      obtain ⟨-, id, rfl⟩ := maxOrMin?_eq hm
      exact foldMinMaxSharedOp.L6698 ρ f0 hf id x y op1 c0 c1 hs
    · cases h
  · split at h
    · next f0 x y hm =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hs, rfl⟩ := hc
      obtain ⟨-, id, rfl⟩ := maxOrMin?_eq hm
      exact foldMinMaxSharedOp.L6701 ρ f hf id x y op1 c0 c1 hs
    · cases h

/-- Theorem 1 for `foldMinMaxSharedOp`: every value the model returns refines the min or max it was called for, at
every width, for every operand, poison included. -/
theorem foldMinMaxSharedOp.sound (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) {r : Repl w}
    (h : run (foldMinMaxSharedOp.steps f op0 op1) = .value r) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) (r.eval ρ) :=
  run_sound (foldMinMaxSharedOp.steps_sound ρ f hf op0 op1 c0 c1) h

/-! ### The case's rewrites -/

/-- The min or max `simplifyBinaryIntrinsic` replaces. -/
abbrev minMaxSrc (f : BinIntr) (op0 op1 : Term w) : Repl w := .bi f (.old op0) (.old op1)

theorem minMaxSrc_swap (ρ : Env) {f : BinIntr} (hf : isMinMax f = true) (op0 op1 : Term w) :
    (minMaxSrc f op0 op1).eval ρ = (minMaxSrc f (immSwap op0 op1).1 (immSwap op0 op1).2).eval ρ := by
  simp only [minMaxSrc, bi_eval, minMax_immSwap hf op0 op1]

/-- `IS.simplifyBinaryIntrinsic.L7004`: `max(x, x)` to `x`. -/
theorem simplifyBinaryIntrinsic.L7004 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    (h : specific op0 op1 = true) : Refines ((minMaxSrc f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [minMaxSrc, bi_eval, Repl.eval_old, specific_denote h, minMax_self hf]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyBinaryIntrinsic.L7012`: `max(x, undef)` to the saturation point, which without `undef` is
`max(x, poison)`, poison. -/
theorem simplifyBinaryIntrinsic.L7012 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) (h : isUndefValue (immSwap op0 op1).2 = true) :
    Refines ((minMaxSrc f op0 op1).eval ρ) ((Repl.const (satPoint f w)).eval ρ) := by
  rw [minMaxSrc_swap ρ hf, minMaxSrc, bi_eval]
  have ub : (immSwap op0 op1).2.hasUndef = false := by
    rcases immSwap_cases op0 op1 with e | e <;> rw [e] <;> assumption
  rw [isUndefValue_denote h ub, BinIntr.eval_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyBinaryIntrinsic.L7020`: `max(x, C)` to `C`, where `C` is the saturation point. -/
theorem simplifyBinaryIntrinsic.L7020 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    {c : BitVec w} (hc : apint (immSwap op0 op1).2 = some c) (h : c = satPoint f w) :
    Refines ((minMaxSrc f op0 op1).eval ρ) ((Repl.const c).eval ρ) := by
  rw [minMaxSrc_swap ρ hf, minMaxSrc, bi_eval, apint_denote hc, h]
  exact refines_ok (minMax_satPoint hf _)

/-- `IS.simplifyBinaryIntrinsic.L7027`: `max(x, C)` to `x`, where `C` is the inverse's saturation point. -/
theorem simplifyBinaryIntrinsic.L7027 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    {c : BitVec w} (hc : apint (immSwap op0 op1).2 = some c) (h : c = satPoint (inverse f) w) :
    Refines ((minMaxSrc f op0 op1).eval ρ) ((Repl.old (immSwap op0 op1).1).eval ρ) := by
  rw [minMaxSrc_swap ρ hf, minMaxSrc, bi_eval, apint_denote hc, h, minMax_inverse_satPoint hf]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyBinaryIntrinsic.L7040`: `max(max(x, C1), C2)` to `max(x, C1)`, where `C1 >= C2`, the nested
constant either operand of the inner call. -/
theorem simplifyBinaryIntrinsic.L7040 (ρ : Env) (f : BinIntr) (hf : isMinMax f = true) (op0 op1 : Term w)
    (ca : (immSwap op0 op1).1.Consistent ρ) {c ic : BitVec w} (hc : apint (immSwap op0 op1).2 = some c)
    (hi : innerConst? f (immSwap op0 op1).1 = some ic) (h : compare (nonStrictPred f) ic c = true) :
    Refines ((minMaxSrc f op0 op1).eval ρ) ((Repl.old (immSwap op0 op1).1).eval ρ) := by
  rw [minMaxSrc_swap ρ hf, minMaxSrc, bi_eval, Repl.eval_old, apint_denote hc]
  refine refines_ok ?_
  generalize (immSwap op0 op1).1 = a at ca hi ⊢
  cases a <;> simp only [innerConst?, reduceCtorEq] at hi
  next id f0 m00 m01 =>
  split at hi
  · next hf0 =>
    simp only [beq_iff_eq] at hf0
    subst hf0
    rw [bi_denote ca]
    cases h0 : apint m00 with
    | some c0 =>
      simp only [h0, Option.orElse_some, Option.some.injEq] at hi
      subst hi
      rw [apint_denote h0, minMax_comm hf (some c0), minMax_nested hf _ h]
      exact Refine.refl_val _
    | none =>
      simp only [h0, Option.orElse_none] at hi
      rw [apint_denote hi, minMax_nested hf _ h]
      exact Refine.refl_val _
  · cases hi

/-- `IS.simplifyBinaryIntrinsic.L7052`: `max(x, y)` to `x`, where the recursive `simplifyICmpInst` says `x >= y`. -/
theorem simplifyBinaryIntrinsic.L7052 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (f : BinIntr) (hf : isMinMax f = true)
    (a b : Term w) (ca : a.Consistent ρ) (cb : b.Consistent ρ) (ua : a.hasUndef = false) (ub : b.hasUndef = false)
    (h : isICmpTrue r recursionLimit (nonStrictPred f) a b = some true) :
    Refines ((minMaxSrc f a b).eval ρ) ((Repl.old a).eval ρ) := by
  rw [minMaxSrc, bi_eval, Repl.eval_old]
  refine refines_ok ?_
  cases hx : a.denote ρ with
  | none => rw [BinIntr.eval_none_left]; exact Refine.val_none _
  | some x =>
    cases hy : b.denote ρ with
    | none => rw [BinIntr.eval_none_right]; exact Refine.val_none _
    | some y =>
      rw [minMax_of_pred hf (isICmpTrue_sound hr h ca cb ua ub hx hy)]
      exact Refine.refl_val _

/-- `IS.simplifyBinaryIntrinsic.L7054`: `max(x, y)` to `y`, where the recursive `simplifyICmpInst` says `y >= x`. -/
theorem simplifyBinaryIntrinsic.L7054 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (f : BinIntr) (hf : isMinMax f = true)
    (a b : Term w) (ca : a.Consistent ρ) (cb : b.Consistent ρ) (ua : a.hasUndef = false) (ub : b.hasUndef = false)
    (h : isICmpTrue r recursionLimit (nonStrictPred f) b a = some true) :
    Refines ((minMaxSrc f a b).eval ρ) ((Repl.old b).eval ρ) := by
  have := simplifyBinaryIntrinsic.L7052 ρ r hr f hf b a cb ca ub ua h
  rwa [minMaxSrc, bi_eval, minMax_comm hf] at this

/-! ### The case -/

/-- Every step of the min and max case that fires is right. -/
theorem simplifyBinaryIntrinsic.minMaxSteps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (f : BinIntr)
    (hf : isMinMax f = true) (op0 op1 : Term w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s rr, Step.fire s rr ∈ simplifyBinaryIntrinsic.minMaxSteps r f op0 op1 →
      Refines ((minMaxSrc f op0 op1).eval ρ) (rr.eval ρ) := by
  have ca : (immSwap op0 op1).1.Consistent ρ := by
    rcases immSwap_cases op0 op1 with e | e <;> rw [e] <;> assumption
  have cb : (immSwap op0 op1).2.Consistent ρ := by
    rcases immSwap_cases op0 op1 with e | e <;> rw [e] <;> assumption
  have ua : (immSwap op0 op1).1.hasUndef = false := by
    rcases immSwap_cases op0 op1 with e | e <;> rw [e] <;> assumption
  have ub : (immSwap op0 op1).2.hasUndef = false := by
    rcases immSwap_cases op0 op1 with e | e <;> rw [e] <;> assumption
  intro s rr hmem
  simp only [simplifyBinaryIntrinsic.minMaxSteps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L7004 ρ f hf op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L7012 ρ f hf op0 op1 u0 u1 (by assumption)
  · split at h
    · next c hc =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next he =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyBinaryIntrinsic.L7020 ρ f hf op0 op1 hc (by simpa using he)
    · cases h
  · split at h
    · next c hc =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next he =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyBinaryIntrinsic.L7027 ρ f hf op0 op1 hc (by simpa using he)
    · cases h
  · split at h
    · next c ic hc hi =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcmp =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyBinaryIntrinsic.L7040 ρ f hf op0 op1 ca hc hi hcmp
    · cases h
  · rw [minMaxSrc_swap ρ hf]
    exact foldMinMaxSharedOp.steps_sound ρ f hf _ _ ca cb s rr (forward_fire h.symm)
  · rw [minMaxSrc_swap ρ hf, minMaxSrc, bi_eval, minMax_comm hf, ← bi_eval]
    exact foldMinMaxSharedOp.steps_sound ρ f hf _ _ cb ca s rr (forward_fire h.symm)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hi =>
    obtain ⟨-, rfl⟩ := h
    rw [minMaxSrc_swap ρ hf]
    exact simplifyBinaryIntrinsic.L7052 ρ r hr f hf _ _ ca cb ua ub hi
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hi =>
    obtain ⟨-, rfl⟩ := h
    rw [minMaxSrc_swap ρ hf]
    exact simplifyBinaryIntrinsic.L7054 ρ r hr f hf _ _ ca cb ua ub hi

end Peephole.IS
