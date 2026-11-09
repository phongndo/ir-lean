import Peephole.IS.ICmpBase
import IRLean.Generic.Arith
import IRLean.Generic.Bitwise

/-! # InstSimplify's `simplifyByDomEq`, and its rewrites for every input

`simplifyByDomEq` is at `llvm/lib/Analysis/InstructionSimplify.cpp:712-740` at `llvmorg-23.1.3`. `simplifySubInst`,
`simplifyAndInst`, `simplifyOrInst`, `simplifyXorInst` and the division and remainder folds call it with their
opcode: where a dominating condition says the two operands are equal, the operation on them is a constant, or either
operand.

| ID | Rewrite, where a dominating condition has `Op0 == Op1` |
| --- | --- |
| `IS.simplifyByDomEq.L727` | `Op0 - Op1`, `Op0 ^ Op1`, `Op0 urem Op1` and `Op0 srem Op1` to 0 |
| `IS.simplifyByDomEq.L731` | `Op0 sdiv Op1` and `Op0 udiv Op1` to 1 |
| `IS.simplifyByDomEq.L736` | `Op0 & Op1` and `Op0 | Op1` to `Op1` |

`isImpliedByDomCondition` is `ICmp.Ext.domCond`. Each theorem holds for every flag the operation has: a division by 0
is undefined, which allows anything. -/

namespace Peephole.IS

open IRLean ICmp

variable {w : Nat}

/-! ### The model -/

/-- `simplifyByDomEq(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step. `RecursionLimit` is 3. -/
def simplifyByDomEq.steps (e : Ext) (op : BinOp) (op0 op1 : Term w) (maxRecurse : Nat) : List (Step w) :=
  [ -- Recursive run it can not get any benefit
    if maxRecurse != 3 then .decline else .next,
    -- std::optional<bool> Imp = isImpliedByDomCondition(CmpInst::ICMP_EQ, Op0, Op1, Q.CxtI, Q.DL);
    -- case Sub, Xor, URem, SRem: return Constant::getNullValue(Ty);
    if e.domCond .eq op0 op1 == some true && (op == .sub || op == .xor || op == .urem || op == .srem) then
      .fire "IS.simplifyByDomEq.L727" (.const 0#w)
    else .next,
    -- case SDiv, UDiv: return ConstantInt::get(Ty, 1);
    if e.domCond .eq op0 op1 == some true && (op == .sdiv || op == .udiv) then
      .fire "IS.simplifyByDomEq.L731" (.const 1#w)
    else .next,
    -- case And, Or: Could be either one - choose Op1 since that's more likely a constant.
    if e.domCond .eq op0 op1 == some true && (op == .and || op == .or) then
      .fire "IS.simplifyByDomEq.L736" (.old op1)
    else .next ]

def simplifyByDomEq (e : Ext) (op : BinOp) (op0 op1 : Term w) (maxRecurse : Nat) : Result w :=
  run (simplifyByDomEq.steps e op op0 op1 maxRecurse)

/-! ### The rewrites, one theorem each -/

/-- The binary operator `simplifyByDomEq`'s caller simplifies, with its flags. -/
def ICmp.binSrc (op : BinOp) (f : Flags) (op0 op1 : Term w) : Repl w := .bin op f (.old op0) (.old op1)

theorem ICmp.binSrc_eval (ρ : Env) (op : BinOp) (f : Flags) (op0 op1 : Term w) :
    (binSrc op f op0 op1).eval ρ = op.eval f (op0.denote ρ) (op1.denote ρ) := rfl

namespace ICmp

/-- What a sound `isImpliedByDomCondition(ICMP_EQ, Op0, Op1)` says: the operands are equal where neither is
poison. -/
theorem domEq {ρ : Env} {e : Ext} (he : e.Sound ρ) {a b : Term w} (h : e.domCond .eq a b = some true) :
    ∀ x y, a.denote ρ = some x → b.denote ρ = some y → x = y := by
  intro x y hx hy
  have := he.domCond .eq a b true x y h hx hy
  simpa [test] using this

theorem ok_refines {a b : Val w} (h : Refines a b) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok a b).2 h

theorem ub_refines {α : Type} [Refine α] (r : UB) (t : Outcome α) : Refines (Outcome.ub r : Outcome α) t :=
  Refine.outcome_ub r t

theorem ok_none_refines (t : Val w) : Refines (Outcome.ok (none : Val w)) (Outcome.ok t) :=
  ok_refines (Refine.val_none t)

end ICmp

/-- `IS.simplifyByDomEq.L727`: `Op0 - Op1`, `Op0 ^ Op1`, `Op0 urem Op1` and `Op0 srem Op1` to 0, where a dominating
condition has `Op0 == Op1`. -/
theorem simplifyByDomEq.L727 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (h : e.domCond .eq op0 op1 = some true) (hop : op = .sub ∨ op = .xor ∨ op = .urem ∨ op = .srem) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  have heq := domEq he h
  rw [binSrc_eval, Repl.eval_const]
  cases hb : op1.denote ρ with
  | none =>
    rcases hop with rfl | rfl | rfl | rfl
    · cases op0.denote ρ <;> exact ok_none_refines _
    · cases op0.denote ρ <;> exact ok_none_refines _
    · exact ub_refines _ _
    · exact ub_refines _ _
  | some y =>
  cases ha : op0.denote ρ with
  | none =>
    rcases hop with rfl | rfl | rfl | rfl
    · exact ok_none_refines _
    · exact ok_none_refines _
    · simp only [BinOp.eval, Val.urem]
      split
      · exact ub_refines _ _
      · exact ok_none_refines _
    · simp only [BinOp.eval, Val.srem]
      split
      · exact ub_refines _ _
      · split
        · exact ub_refines _ _
        · exact ok_none_refines _
  | some x =>
  obtain rfl := heq x y ha hb
  rcases hop with rfl | rfl | rfl | rfl
  · exact ok_refines (Generic.sub_self_refines _ _ _)
  · exact ok_refines (Generic.xor_self_refines _)
  · simp only [BinOp.eval, Val.urem]
    split
    · exact ub_refines _ _
    · rw [BitVec.umod_self]; exact ok_refines (Refine.refl_val _)
  · simp only [BinOp.eval, Val.srem]
    split
    · exact ub_refines _ _
    · split
      · exact ub_refines _ _
      · rw [BitVec.srem_self]; exact ok_refines (Refine.refl_val _)

/-- `IS.simplifyByDomEq.L731`: `Op0 sdiv Op1` and `Op0 udiv Op1` to 1, where a dominating condition has
`Op0 == Op1`. -/
theorem simplifyByDomEq.L731 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (h : e.domCond .eq op0 op1 = some true) (hop : op = .sdiv ∨ op = .udiv) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 1#w).eval ρ) := by
  have heq := domEq he h
  rw [binSrc_eval, Repl.eval_const]
  cases hb : op1.denote ρ with
  | none => rcases hop with rfl | rfl <;> exact ub_refines _ _
  | some y =>
  cases ha : op0.denote ρ with
  | none =>
    rcases hop with rfl | rfl
    · simp only [BinOp.eval, Val.sdiv]
      split
      · exact ub_refines _ _
      · split
        · exact ub_refines _ _
        · exact ok_none_refines _
    · simp only [BinOp.eval, Val.udiv]
      split
      · exact ub_refines _ _
      · exact ok_none_refines _
  | some x =>
  obtain rfl := heq x y ha hb
  rcases hop with rfl | rfl
  · simp only [BinOp.eval, Val.sdiv]
    split
    · exact ub_refines _ _
    · next hx =>
      split
      · exact ub_refines _ _
      · rw [BitVec.srem_self, BitVec.sdiv_self]
        have hb : (x == 0#w) = false := by simpa using hx
        simp only [hb, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ok_refines (Refine.refl_val _)
  · simp only [BinOp.eval, Val.udiv]
    split
    · exact ub_refines _ _
    · next hx =>
      rw [BitVec.umod_self, BitVec.udiv_self]
      have hb : (x == 0#w) = false := by simpa using hx
      simp only [hb, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ok_refines (Refine.refl_val _)

/-- `IS.simplifyByDomEq.L736`: `Op0 & Op1` and `Op0 | Op1` to `Op1`, where a dominating condition has
`Op0 == Op1`. -/
theorem simplifyByDomEq.L736 (ρ : Env) (e : Ext) (he : e.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (h : e.domCond .eq op0 op1 = some true) (hop : op = .and ∨ op = .or) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  have heq := domEq he h
  rw [binSrc_eval, Repl.eval_old]
  cases hb : op1.denote ρ with
  | none => rcases hop with rfl | rfl <;> cases op0.denote ρ <;> exact ok_none_refines _
  | some y =>
  cases ha : op0.denote ρ with
  | none => rcases hop with rfl | rfl <;> exact ok_none_refines _
  | some x =>
  obtain rfl := heq x y ha hb
  rcases hop with rfl | rfl
  · simp only [BinOp.eval]
    rw [Generic.and_self]
    exact ok_refines (Refine.refl_val _)
  · exact ok_refines (Generic.or_self_disjoint_refines _ _)

/-! ### The fold -/

/-- Every step of `simplifyByDomEq` that fires is right. -/
theorem simplifyByDomEq.steps_sound (ρ : Env) (e : Ext) (he : e.Sound ρ) (op : BinOp) (f : Flags)
    (op0 op1 : Term w) (n : Nat) :
    ∀ site r, Step.fire site r ∈ simplifyByDomEq.steps e op op0 op1 n →
      Refines ((binSrc op f op0 op1).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hc
    exact L727 ρ e he op f op0 op1 hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L731 ρ e he op f op0 op1 hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L736 ρ e he op f op0 op1 hc.1 hc.2

/-- Theorem 1 for `simplifyByDomEq`: every value the model returns refines the operation its caller simplifies, for
`sub`, `xor`, `and`, `or` and the divisions and remainders, with every flag, at every width and recursion budget, in
every run, poison included, given a sound `isImpliedByDomCondition`. -/
theorem simplifyByDomEq.sound (ρ : Env) (e : Ext) (he : e.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (n : Nat) {r : Repl w} (h : simplifyByDomEq e op op0 op1 n = .value r) :
    Refines ((binSrc op f op0 op1).eval ρ) (r.eval ρ) :=
  run_sound (steps_sound ρ e he op f op0 op1 n) h

end Peephole.IS
