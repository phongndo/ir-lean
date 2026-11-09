import Peephole.IS.ArithRecur

/-! # InstSimplify's `simplifyMulInst`, and its rewrites for every input

`simplifyMulInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:898-961` at `llvmorg-23.1.3`. This is its model on
`Peephole.Term`, step by step in the C++'s order. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyMulInst.L906` | `X * poison` to poison |
| `IS.simplifyMulInst.L911` | `X * undef` and `X * 0` to 0. IRLean has no `undef`, so the first is about poison only |
| `IS.simplifyMulInst.L915` | `X * 1` to `X` |
| `IS.simplifyMulInst.L923` | `(X / Y) * Y` and `Y * (X / Y)` to `X`, for an exact `udiv` or `sdiv` |
| `IS.simplifyMulInst.L929` | `mul nsw` in `i1` to 0 |

The forwards to `simplifyAssociativeBinOp`, `expandCommutativeBinOp` and `threadBinOpOverSelect` fire what those
fire, under their own IDs, and their theorems are in `Peephole.IS.ArithRecur`. `Q.IIQ.UseInstrInfo` is true in
InstSimplify's queries, so L923 reads the `exact` flag. -/

namespace Peephole.IS

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-- `m_Exact(m_IDiv(m_Value(X), m_Specific(S)))` on `V`, binding `X`: an exact `udiv` or `sdiv` of `X` by `S`. -/
def exactDivOf (s v : Term w) : Option (Term w) :=
  match v with
  | .bin _ op f x b => if (op == .udiv || op == .sdiv) && f.exact && specific s b then some x else none
  | _ => none

/-- `simplifyMulInst` once `foldOrCommuteConstant` has put a lone constant on the right, step by step. -/
def simplifyMulInst.steps (r : Recur) (op0 op1 : Term w) (isNSW : Bool) (maxRecurse : Nat) : List (Step w) :=
  [ -- X * poison -> poison
    if isPoison op1 then .fire "IS.simplifyMulInst.L906" (.old op1) else .next,
    -- X * undef -> 0
    -- X * 0 -> 0
    if isUndefValue op1 || zero op1 then .fire "IS.simplifyMulInst.L911" (.const 0#w) else .next,
    -- X * 1 -> X
    if one op1 then .fire "IS.simplifyMulInst.L915" (.old op0) else .next,
    -- (X / Y) * Y -> X if the division is exact.
    match exactDivOf op1 op0, exactDivOf op0 op1 with
    | some x, _ => .fire "IS.simplifyMulInst.L923" (.old x)
    | none, some x => .fire "IS.simplifyMulInst.L923" (.old x)
    | none, none => .next,
    -- mul i1 nsw is a special-case because -1 * -1 is poison (+1 is not representable). All other cases reduce to
    -- 0, so just return 0.
    if w == 1 && isNSW then .fire "IS.simplifyMulInst.L929" (.const 0#w) else .next,
    -- Treat "mul i1" as "and i1": what simplifyAndInst answers isn't modelled.
    if w == 1 && maxRecurse != 0 then .delegate "simplifyAndInst" else .next,
    -- Try some generic simplifications for associative operations.
    forward (simplifyAssociativeBinOp.steps r .mul op0 op1 maxRecurse),
    -- Mul distributes over Add. Try some generic simplifications based on this.
    forward (expandCommutativeBinOp.steps r .mul op0 op1 .add maxRecurse),
    -- If the operation is with the result of a select instruction, check whether operating on either branch of the
    -- select always yields the same value.
    if isSelect op0 || isSelect op1 then forward (threadBinOpOverSelect.steps r .mul op0 op1 maxRecurse) else .next,
    -- If the operation is with the result of a phi instruction, check whether operating on all incoming values of
    -- the phi always yields the same value: threadBinOpOverPHI isn't modelled, and a phi is an operand the model
    -- doesn't see into, so this delegates for every operand that may be one, once its `MaxRecurse` check passes.
    if (mayBePhi op0 || mayBePhi op1) && maxRecurse != 0 then .delegate "threadBinOpOverPHI" else .next ]

/-- `simplifyMulInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`. `foldOrCommuteConstant` folds two constants, which the
constant folder does, and swaps a lone constant to the right. `IsNUW` is read by none of its steps. -/
def simplifyMulInst (r : Recur) (op0 op1 : Term w) (isNSW _isNUW : Bool) (maxRecurse : Nat) : Result w :=
  if op0.isConstant then
    if op1.isConstant then .delegated "ConstantFoldBinaryOpOperands"
    else run (simplifyMulInst.steps r op1 op0 isNSW maxRecurse)
  else run (simplifyMulInst.steps r op0 op1 isNSW maxRecurse)

/-- What InstSimplify does with a `mul`: `simplifyInstruction` calls `simplifyMulInst` with the instruction's own
flags and `MaxRecurse` at `RecursionLimit`. The recursive calls are what the model doesn't say: `Recur.unknown`. -/
def simplifyMulInst.onInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .mul f a b => simplifyMulInst Recur.unknown a b f.nsw f.nuw recursionLimit
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

/-- The `mul` `simplifyMulInst` replaces, with its operands and flags. -/
def mulSrc (op0 op1 : Term w) (isNSW isNUW : Bool) : Repl w :=
  binSrc .mul { nuw := isNUW, nsw := isNSW } op0 op1

theorem mulSrc_eval (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (mulSrc op0 op1 isNSW isNUW).eval ρ = Outcome.ok (Val.mul (op0.denote ρ) (op1.denote ρ) isNUW isNSW) := rfl

theorem mulSrc_comm (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (mulSrc op0 op1 isNSW isNUW).eval ρ = (mulSrc op1 op0 isNSW isNUW).eval ρ := by
  rw [mulSrc_eval, mulSrc_eval, Lemmas.mul_comm]

/-- `IS.simplifyMulInst.L906`: `X * poison` to poison. -/
theorem simplifyMulInst.L906 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : isPoison op1 = true) :
    Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [mulSrc, binSrc_eval, isPoison_denote h]
  exact eval_none_right _ _ _ _

/-- `IS.simplifyMulInst.L911`: `X * undef` and `X * 0` to 0. Without `undef`, the first is `X * poison`. -/
theorem simplifyMulInst.L911 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (u1 : op1.hasUndef = false)
    (h : (isUndefValue op1 || zero op1) = true) :
    Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.const 0#w).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [mulSrc, binSrc_eval, isUndefValue_denote h u1]; exact eval_none_right _ _ _ _
  · rw [mulSrc_eval, cst_eq h]; exact ok_refines (Generic.mul_zero_refines _ _ _)

/-- `IS.simplifyMulInst.L915`: `X * 1` to `X`. -/
theorem simplifyMulInst.L915 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : one op1 = true) :
    Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [mulSrc_eval, cst_eq h]
  exact ok_refines (Generic.mul_one_refines _ _ _)

/-- An exact division by `S` that ran, times `S`, refines its dividend. -/
private theorem exactDivOf_refines {ρ : Env} {s v x : Term w} (h : exactDivOf s v = some x) (hc : v.Consistent ρ)
    (nuw nsw : Bool) : Refines (Val.mul (v.denote ρ) (s.denote ρ) nuw nsw) (x.denote ρ) := by
  unfold exactDivOf at h
  split at h
  · next id op f x' b =>
    split at h
    · next hm =>
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨hop, hex⟩, hs⟩ := hm
      obtain ⟨-, -, hv⟩ := hc
      rw [← specific_denote hs]
      simp only [Term.denote]
      rcases hop with rfl | rfl
      · have : Val.udiv (x.denote ρ) (b.denote ρ) true = Outcome.ok (ρ _ id) := by rw [← hex]; exact hv
        exact Lemmas.mul_udiv_exact_refines this nuw nsw
      · have : Val.sdiv (x.denote ρ) (b.denote ρ) true = Outcome.ok (ρ _ id) := by rw [← hex]; exact hv
        exact Lemmas.mul_sdiv_exact_refines this nuw nsw
    · cases h
  · cases h

/-- `IS.simplifyMulInst.L923`, first match: `(X / Y) * Y` to `X`, for an exact `udiv` or `sdiv`. -/
theorem simplifyMulInst.L923 (ρ : Env) (op0 op1 x : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (h : exactDivOf op1 op0 = some x) : Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old x).eval ρ) := by
  rw [mulSrc_eval, Repl.eval_old]
  exact ok_refines (exactDivOf_refines h c0 _ _)

/-- `IS.simplifyMulInst.L923`, second match: `Y * (X / Y)` to `X`. -/
theorem simplifyMulInst.L923_swapped (ρ : Env) (op0 op1 x : Term w) (isNSW isNUW : Bool) (c1 : op1.Consistent ρ)
    (h : exactDivOf op0 op1 = some x) : Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old x).eval ρ) := by
  rw [mulSrc_comm, mulSrc_eval, Repl.eval_old]
  exact ok_refines (exactDivOf_refines h c1 _ _)

/-- `IS.simplifyMulInst.L929`: `mul nsw` in `i1` to 0. -/
theorem simplifyMulInst.L929 (ρ : Env) (op0 op1 : Term 1) (isNUW : Bool) :
    Refines ((mulSrc op0 op1 true isNUW).eval ρ) ((Repl.const 0#1).eval ρ) := by
  rw [mulSrc_eval]
  exact ok_refines (Lemmas.mul_nsw_one_bit_refines _ _ _)

/-! ### The fold -/

/-- Every step of `simplifyMulInst` that fires is right. -/
theorem simplifyMulInst.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifyMulInst.steps r op0 op1 isNSW n →
      Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifyMulInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyMulInst.L906 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyMulInst.L911 ρ op0 op1 isNSW isNUW u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyMulInst.L915 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;> obtain ⟨-, rfl⟩ := h
    · exact simplifyMulInst.L923 ρ op0 op1 _ isNSW isNUW c0 (by assumption)
    · exact simplifyMulInst.L923_swapped ρ op0 op1 _ isNSW isNUW c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact simplifyMulInst.L929 ρ op0 op1 isNUW
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifyAssociativeBinOp.steps_sound ρ r hr .mul rfl _ op0 op1 n c0 c1 u0 u1 s res (forward_fire h.symm)
  · exact expandCommutativeBinOp.steps_sound ρ r hr .mul .add rfl _ op0 op1 n c0 c1 u0 u1 s res
      (forward_fire h.symm)
  · split at h
    · exact threadBinOpOverSelect.steps_sound ρ r hr .mul _ op0 op1 n c0 c1 u0 u1 s res (forward_fire h.symm)
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifyMulInst`: every value the model returns refines the `mul` it replaces, at every width, for
both flags and every recursion budget, in every run its operands are consistent with, poison included, for every
recursive simplifier that's sound in the run. It says nothing about operands that reach an `undef`. -/
theorem simplifyMulInst.sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op0 op1 : Term w) (isNSW isNUW : Bool)
    (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) {res : Repl w} (h : simplifyMulInst r op0 op1 isNSW isNUW n = .value res) :
    Refines ((mulSrc op0 op1 isNSW isNUW).eval ρ) (res.eval ρ) := by
  unfold simplifyMulInst at h
  split at h
  · split at h
    · cases h
    · rw [mulSrc_comm]
      exact run_sound (simplifyMulInst.steps_sound ρ r hr op1 op0 isNSW isNUW n c1 c0 u1 u0) h
  · exact run_sound (simplifyMulInst.steps_sound ρ r hr op0 op1 isNSW isNUW n c0 c1 u0 u1) h

end Peephole.IS
