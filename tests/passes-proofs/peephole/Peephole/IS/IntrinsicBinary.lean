import Peephole.IS.IntrinsicMinMax

/-! # InstSimplify's `simplifyBinaryIntrinsic`, and its rewrites of integer intrinsics for every input

`simplifyBinaryIntrinsic` is at `llvm/lib/Analysis/InstructionSimplify.cpp:6894-7291` at `llvmorg-23.1.3`.
`simplifyIntrinsic` calls it on an intrinsic of two operands. Of the intrinsics `Term` holds, those are `abs`, `ctlz`
and `cttz`, whose second operand is their flag, and the eight of `BinIntr`. This is its model on `Peephole.Term`, step
by step in the C++'s order, for those. `IID` and the operands are the call's, `call`.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyBinaryIntrinsic.L6928` | `abs(abs(x))` to `abs(x)` |
| `IS.simplifyBinaryIntrinsic.L6934` | `cttz(1 << x)` to `x` |
| `IS.simplifyBinaryIntrinsic.L6940` | `ctlz(C >> x)` to `x`, for a negative constant `C` |
| `IS.simplifyBinaryIntrinsic.L6942` | `ctlz(C >>s x)` to 0, for a negative constant `C` |
| The min and max case | `Peephole.IS.IntrinsicMinMax`'s nine |
| `IS.simplifyBinaryIntrinsic.L7111` | `uadd.sat(-1, x)` and `uadd.sat(x, -1)` to -1 |
| `IS.simplifyBinaryIntrinsic.L7119` | `uadd.sat` and `sadd.sat` of `undef` to -1: without `undef`, of poison |
| `IS.simplifyBinaryIntrinsic.L7123` | `uadd.sat(x, 0)` and `sadd.sat(x, 0)` to `x` |
| `IS.simplifyBinaryIntrinsic.L7126` | `uadd.sat(0, x)` and `sadd.sat(0, x)` to `x` |
| `IS.simplifyBinaryIntrinsic.L7131` | `usub.sat(0, x)` and `usub.sat(x, -1)` to 0 |
| `IS.simplifyBinaryIntrinsic.L7136` | `usub.sat` and `ssub.sat` of `x, x`, or of `undef`, to 0 |
| `IS.simplifyBinaryIntrinsic.L7139` | `usub.sat(x, 0)` and `ssub.sat(x, 0)` to `x` |

`uadd_sat` falls through to `sadd_sat`'s code, and `usub_sat` to `ssub_sat`'s, so those steps are for both. The cases
for `scmp`, `ucmp`, the `*.with.overflow` intrinsics, `pdep`, `pext`, `ptrmask` and floating point aren't modelled:
`Term` holds none of those calls, and the `switch` reaches only one case. -/

namespace Peephole.IS

open IRLean Intrinsic

variable {w : Nat}

/-! ### Matchers -/

/-- `m_Intrinsic<Intrinsic::abs>(m_Value(), m_Value())`. -/
def Intrinsic.isAbs : Term w → Bool
  | .un _ (.abs _) _ => true
  | _ => false

/-- `m_Shl(m_One(), m_Value(X))`, binding `X`. -/
def Intrinsic.shlOne? (t : Term w) : Option (Term w) :=
  match binop? .shl t with
  | some (_, a, x) => if one a then some x else none
  | none => none

/-- `m_LShr(m_Negative(), m_Value(X))`, binding `X`. -/
def Intrinsic.lshrNegative? (t : Term w) : Option (Term w) :=
  match binop? .lshr t with
  | some (_, c, x) => if negative c then some x else none
  | none => none

/-- `m_AShr(m_Negative(), m_Value())`. -/
def Intrinsic.ashrNegative (t : Term w) : Bool :=
  match binop? .ashr t with
  | some (_, c, _) => negative c
  | none => false

/-! ### The model -/

/-- `simplifyBinaryIntrinsic(IID, ReturnType, Op0, Op1, FMF, Q)`, step by step, for the calls `Term` holds. `r` is
the recursive `simplifyICmpInst` the min and max case asks. -/
def simplifyBinaryIntrinsic.steps (r : Recur) (call : Term w) : List (Step w) :=
  [ -- abs(abs(x)) -> abs(x). We don't need to worry about the nsw arg here. It is always ok to pick the earlier
    -- abs. We'll just lose nsw if its only on the outer abs.
    match call with
    | .un _ (.abs _) op0 => if isAbs op0 then .fire "IS.simplifyBinaryIntrinsic.L6928" (.old op0) else .next
    | _ => .next,
    -- case Intrinsic::cttz: if (match(Op0, m_Shl(m_One(), m_Value(X)))) return X;
    match call with
    | .un _ (.cttz _) op0 =>
      match shlOne? op0 with
      | some x => .fire "IS.simplifyBinaryIntrinsic.L6934" (.old x)
      | none => .next
    | _ => .next,
    -- case Intrinsic::ctlz: if (match(Op0, m_LShr(m_Negative(), m_Value(X)))) return X;
    match call with
    | .un _ (.ctlz _) op0 =>
      match lshrNegative? op0 with
      | some x => .fire "IS.simplifyBinaryIntrinsic.L6940" (.old x)
      | none => .next
    | _ => .next,
    -- if (match(Op0, m_AShr(m_Negative(), m_Value()))) return Constant::getNullValue(ReturnType);
    match call with
    | .un _ (.ctlz _) op0 => if ashrNegative op0 then .fire "IS.simplifyBinaryIntrinsic.L6942" (.const 0#w) else .next
    | _ => .next ] ++
  -- case Intrinsic::smax: case Intrinsic::smin: case Intrinsic::umax: case Intrinsic::umin:
  (match call with
   | .bi _ f op0 op1 => if isMinMax f then simplifyBinaryIntrinsic.minMaxSteps r f op0 op1 else []
   | _ => []) ++
  [ -- case Intrinsic::uadd_sat: sat(MAX + X) -> MAX, sat(X + MAX) -> MAX
    match call with
    | .bi _ .uaddSat op0 op1 =>
      if allOnes op0 || allOnes op1 then .fire "IS.simplifyBinaryIntrinsic.L7111" (.const (BitVec.allOnes w))
      else .next
    | _ => .next,
    -- [[fallthrough]]; case Intrinsic::sadd_sat: sat(X + undef) -> -1, sat(undef + X) -> -1. For unsigned: Assume
    -- undef is MAX, thus we saturate to MAX (-1). For signed: Assume undef is ~X, in which case X + ~X = -1.
    match call with
    | .bi _ f op0 op1 =>
      if (f == .uaddSat || f == .saddSat) && (isUndefValue op0 || isUndefValue op1) then
        .fire "IS.simplifyBinaryIntrinsic.L7119" (.const (BitVec.allOnes w))
      else .next
    | _ => .next,
    -- X + 0 -> X
    match call with
    | .bi _ f op0 op1 =>
      if (f == .uaddSat || f == .saddSat) && zero op1 then .fire "IS.simplifyBinaryIntrinsic.L7123" (.old op0)
      else .next
    | _ => .next,
    -- 0 + X -> X
    match call with
    | .bi _ f op0 op1 =>
      if (f == .uaddSat || f == .saddSat) && zero op0 then .fire "IS.simplifyBinaryIntrinsic.L7126" (.old op1)
      else .next
    | _ => .next,
    -- case Intrinsic::usub_sat: sat(0 - X) -> 0, sat(X - MAX) -> 0
    match call with
    | .bi _ .usubSat op0 op1 =>
      if zero op0 || allOnes op1 then .fire "IS.simplifyBinaryIntrinsic.L7131" (.const 0#w) else .next
    | _ => .next,
    -- [[fallthrough]]; case Intrinsic::ssub_sat: X - X -> 0, X - undef -> 0, undef - X -> 0
    match call with
    | .bi _ f op0 op1 =>
      if (f == .usubSat || f == .ssubSat) && (specific op0 op1 || isUndefValue op0 || isUndefValue op1) then
        .fire "IS.simplifyBinaryIntrinsic.L7136" (.const 0#w)
      else .next
    | _ => .next,
    -- X - 0 -> X
    match call with
    | .bi _ f op0 op1 =>
      if (f == .usubSat || f == .ssubSat) && zero op1 then .fire "IS.simplifyBinaryIntrinsic.L7139" (.old op0)
      else .next
    | _ => .next ]

/-! ### The rewrites, one theorem each -/

/-- `IS.simplifyBinaryIntrinsic.L6928`: `abs(abs(x))` to `abs(x)`, whatever either's flag. -/
theorem simplifyBinaryIntrinsic.L6928 (ρ : Env) (p : Bool) (op0 : Term w) (c0 : op0.Consistent ρ)
    (h : isAbs op0 = true) : Refines ((Repl.un (.abs p) (.old op0)).eval ρ) ((Repl.old op0).eval ρ) := by
  unfold isAbs at h
  split at h
  · next id q x =>
    rw [un_eval, Repl.eval_old, un_denote c0]
    exact refines_ok (Lemmas.abs_abs_refines _ q p)
  · cases h

/-- `IS.simplifyBinaryIntrinsic.L6934`: `cttz(1 << x)` to `x`, whatever the flags. -/
theorem simplifyBinaryIntrinsic.L6934 (ρ : Env) (z : Bool) (op0 x : Term w) (c0 : op0.Consistent ρ)
    (h : shlOne? op0 = some x) : Refines ((Repl.un (.cttz z) (.old op0)).eval ρ) ((Repl.old x).eval ρ) := by
  unfold shlOne? at h
  split at h
  · next f a x' hs =>
    split at h
    · next ha =>
      cases h
      have hd := ok_inj (binop?_consistent hs c0).2.2
      rw [un_eval, Repl.eval_old, ← hd, cst_eq ha]
      exact refines_ok (Lemmas.cttz_shl_one_refines _ _ _ _)
    · cases h
  · cases h

/-- `IS.simplifyBinaryIntrinsic.L6940`: `ctlz(C >> x)` to `x`, for a negative constant `C`, whatever the flags. -/
theorem simplifyBinaryIntrinsic.L6940 (ρ : Env) (z : Bool) (op0 x : Term w) (c0 : op0.Consistent ρ)
    (h : lshrNegative? op0 = some x) : Refines ((Repl.un (.ctlz z) (.old op0)).eval ρ) ((Repl.old x).eval ρ) := by
  unfold lshrNegative? at h
  split at h
  · next f c x' hs =>
    split at h
    · next hc =>
      cases h
      obtain ⟨cv, hneg, hcd⟩ := cst_denote (ρ := ρ) hc
      have hd := ok_inj (binop?_consistent hs c0).2.2
      rw [un_eval, Repl.eval_old, ← hd, hcd]
      exact refines_ok (Lemmas.ctlz_lshr_negative_refines hneg _ _ _)
    · cases h
  · cases h

/-- `IS.simplifyBinaryIntrinsic.L6942`: `ctlz(C >>s x)` to 0, for a negative constant `C`, whatever the flags. -/
theorem simplifyBinaryIntrinsic.L6942 (ρ : Env) (z : Bool) (op0 : Term w) (c0 : op0.Consistent ρ)
    (h : ashrNegative op0 = true) : Refines ((Repl.un (.ctlz z) (.old op0)).eval ρ) ((Repl.const 0#w).eval ρ) := by
  unfold ashrNegative at h
  split at h
  · next f c x hs =>
    obtain ⟨cv, hneg, hcd⟩ := cst_denote (ρ := ρ) h
    have hd := ok_inj (binop?_consistent hs c0).2.2
    rw [un_eval, Repl.eval_const, ← hd, hcd]
    exact refines_ok (Lemmas.ctlz_ashr_negative_refines hneg _ _ _)
  · cases h

/-- `IS.simplifyBinaryIntrinsic.L7111`: `uadd.sat(-1, x)` and `uadd.sat(x, -1)` to -1. -/
theorem simplifyBinaryIntrinsic.L7111 (ρ : Env) (op0 op1 : Term w) (h : (allOnes op0 || allOnes op1) = true) :
    Refines ((Repl.bi .uaddSat (.old op0) (.old op1)).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  rw [bi_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [cst_eq h]
  · exact Lemmas.uaddSat_allOnes_left_refines _
  · exact Lemmas.uaddSat_allOnes_right_refines _

/-- `IS.simplifyBinaryIntrinsic.L7119`: `uadd.sat` and `sadd.sat` of `undef` to -1, which without `undef` is of
poison, poison. -/
theorem simplifyBinaryIntrinsic.L7119 (ρ : Env) (f : BinIntr) (op0 op1 : Term w) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) (h : (isUndefValue op0 || isUndefValue op1) = true) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  rw [bi_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [isUndefValue_denote h u0, BinIntr.eval_none_left]; exact Refine.val_none _
  · rw [isUndefValue_denote h u1, BinIntr.eval_none_right]; exact Refine.val_none _

/-- `IS.simplifyBinaryIntrinsic.L7123`: `uadd.sat(x, 0)` and `sadd.sat(x, 0)` to `x`. -/
theorem simplifyBinaryIntrinsic.L7123 (ρ : Env) (f : BinIntr) (hf : (f == .uaddSat || f == .saddSat) = true)
    (op0 op1 : Term w) (h : zero op1 = true) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [bi_eval, Repl.eval_old, cst_eq h]
  refine refines_ok ?_
  simp only [Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl <;> simp only [BinIntr.eval]
  · rw [Lemmas.uaddSat_zero]; exact Refine.refl_val _
  · rw [Lemmas.saddSat_zero]; exact Refine.refl_val _

/-- `IS.simplifyBinaryIntrinsic.L7126`: `uadd.sat(0, x)` and `sadd.sat(0, x)` to `x`. -/
theorem simplifyBinaryIntrinsic.L7126 (ρ : Env) (f : BinIntr) (hf : (f == .uaddSat || f == .saddSat) = true)
    (op0 op1 : Term w) (h : zero op0 = true) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [bi_eval, Repl.eval_old, cst_eq h]
  refine refines_ok ?_
  simp only [Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl <;> simp only [BinIntr.eval]
  · rw [Lemmas.zero_uaddSat]; exact Refine.refl_val _
  · rw [Lemmas.zero_saddSat]; exact Refine.refl_val _

/-- `IS.simplifyBinaryIntrinsic.L7131`: `usub.sat(0, x)` and `usub.sat(x, -1)` to 0. -/
theorem simplifyBinaryIntrinsic.L7131 (ρ : Env) (op0 op1 : Term w) (h : (zero op0 || allOnes op1) = true) :
    Refines ((Repl.bi .usubSat (.old op0) (.old op1)).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [bi_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [cst_eq h]
  · exact Lemmas.zero_usubSat_refines _
  · exact Lemmas.usubSat_allOnes_refines _

/-- `IS.simplifyBinaryIntrinsic.L7136`: `usub.sat` and `ssub.sat` of `x, x` to 0, and of `undef`, which without `undef`
is of poison, poison. -/
theorem simplifyBinaryIntrinsic.L7136 (ρ : Env) (f : BinIntr) (hf : (f == .usubSat || f == .ssubSat) = true)
    (op0 op1 : Term w) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (h : (specific op0 op1 || isUndefValue op0 || isUndefValue op1) = true) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [bi_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [specific_denote h]
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with rfl | rfl <;> simp only [BinIntr.eval]
    · exact Lemmas.usubSat_self_refines _
    · exact Lemmas.ssubSat_self_refines _
  · rw [isUndefValue_denote h u0, BinIntr.eval_none_left]; exact Refine.val_none _
  · rw [isUndefValue_denote h u1, BinIntr.eval_none_right]; exact Refine.val_none _

/-- `IS.simplifyBinaryIntrinsic.L7139`: `usub.sat(x, 0)` and `ssub.sat(x, 0)` to `x`. -/
theorem simplifyBinaryIntrinsic.L7139 (ρ : Env) (f : BinIntr) (hf : (f == .usubSat || f == .ssubSat) = true)
    (op0 op1 : Term w) (h : zero op1 = true) :
    Refines ((Repl.bi f (.old op0) (.old op1)).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [bi_eval, Repl.eval_old, cst_eq h]
  refine refines_ok ?_
  simp only [Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl <;> simp only [BinIntr.eval]
  · rw [Lemmas.usubSat_zero]; exact Refine.refl_val _
  · rw [Lemmas.ssubSat_zero]; exact Refine.refl_val _

/-! ### The fold -/

/-- Every step of `simplifyBinaryIntrinsic` that fires is right. -/
theorem simplifyBinaryIntrinsic.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (call : Term w)
    (cc : call.Consistent ρ) (uc : call.hasUndef = false) :
    ∀ s rr, Step.fire s rr ∈ simplifyBinaryIntrinsic.steps r call → Refines (call.top.eval ρ) (rr.eval ρ) := by
  intro s rr hmem
  simp only [simplifyBinaryIntrinsic.steps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ((h | h | h | h) | h) | h | h | h | h | h | h | h
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L6928 ρ _ _ cc.1 (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L6934 ρ _ _ _ cc.1 (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L6940 ρ _ _ _ cc.1 (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L6942 ρ _ _ cc.1 (by assumption)
  · split at h
    · next id f op0 op1 =>
      split at h
      · next hf =>
        simp only [Term.hasUndef, Bool.or_eq_false_iff] at uc
        exact simplifyBinaryIntrinsic.minMaxSteps_sound ρ r hr f hf op0 op1 cc.1 cc.2.1 uc.1 uc.2 s rr h
      · cases h
    · cases h
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L7111 ρ _ _ (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at uc
    simp only [Bool.and_eq_true] at hc
    exact simplifyBinaryIntrinsic.L7119 ρ _ _ _ uc.1 uc.2 hc.2
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact simplifyBinaryIntrinsic.L7123 ρ _ hc.1 _ _ hc.2
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact simplifyBinaryIntrinsic.L7126 ρ _ hc.1 _ _ hc.2
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyBinaryIntrinsic.L7131 ρ _ _ (by assumption)
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at uc
    simp only [Bool.and_eq_true] at hc
    exact simplifyBinaryIntrinsic.L7136 ρ _ hc.1 _ _ uc.1 uc.2 hc.2
  · split at h <;> try simp only [reduceCtorEq] at h
    split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact simplifyBinaryIntrinsic.L7139 ρ _ hc.1 _ _ hc.2

/-- Theorem 1 for `simplifyBinaryIntrinsic` on the calls `Term` holds: every value the model returns refines the call,
at every width, flag and operand, poison included, in every run the call is consistent with and in which `r`, the
recursive `simplifyICmpInst`, is sound. It says nothing about operands that reach an `undef`. -/
theorem simplifyBinaryIntrinsic.sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (call : Term w)
    (cc : call.Consistent ρ) (uc : call.hasUndef = false) {rr : Repl w}
    (h : run (simplifyBinaryIntrinsic.steps r call) = .value rr) : Refines (call.top.eval ρ) (rr.eval ρ) :=
  run_sound (simplifyBinaryIntrinsic.steps_sound ρ r hr call cc uc) h

end Peephole.IS
