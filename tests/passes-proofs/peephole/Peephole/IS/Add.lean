import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.Lemmas.Add
import IRLean.Generic.Arith

/-! # InstSimplify's `simplifyAddInst`, and its rewrites for every input

`simplifyAddInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:594-650` at `llvmorg-23.1.3`. This is its model on
`Peephole.Term`, step by step in the C++'s order, as #47's model in `tests/cpp_correspondence` has it. Each step that
rewrites carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyAddInst.L601` | `X + poison` to poison |
| `IS.simplifyAddInst.L605` | `X + undef` to `undef`. IRLean has no `undef`, so this is about poison only |
| `IS.simplifyAddInst.L609` | `X + 0` to `X` |
| `IS.simplifyAddInst.L613` | `X + Y` to 0, where `isKnownNegation(X, Y)` |
| `IS.simplifyAddInst.L621` | `X + (Y - X)` and `(Y - X) + X` to `Y` |
| `IS.simplifyAddInst.L626` | `X + ~X` and `~X + X` to -1 |
| `IS.simplifyAddInst.L633` | `add nsw/nuw (xor Y, signmask), signmask` to `Y` |
| `IS.simplifyAddInst.L637` | `add nuw X, -1` to -1 |

`simplifyAddInst.sound` puts them together: every value the model returns refines the `add`, at every width, flag set
and recursion budget, poison included. It's this rewrite's theorem 1, in the sense of
[the binding approach](../../../../../docs/binding-approach.md#two-theorems-per-unit): a statement about the model,
which a proof about the compiled C++ can meet at `simplifyAddInst`'s name and type. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

/-! ### Helpers it calls -/

/-- `isKnownNegation(X, Y)` from `llvm/lib/Analysis/ValueTracking.cpp`, with its defaults `NeedNSW = false` and
`AllowPoison = true`, as `simplifyAddInst` calls it: `X` is `0 - Y`, `Y` is `0 - X`, or they're `A - B` and
`B - A`. -/
def isKnownNegation (x y : Term w) : Bool :=
  negationOf x y || negationOf y x || subSwapped x y
where
  /-- `match(X, m_Neg(m_Specific(Y)))`. -/
  negationOf (x y : Term w) : Bool :=
    match binop? .sub x with
    | some (_, z, v) => zero z && specific y v
    | none => false
  /-- `match(X, m_Sub(m_Value(A), m_Value(B))) && match(Y, m_Sub(m_Specific(B), m_Specific(A)))`. -/
  subSwapped (x y : Term w) : Bool :=
    match binop? .sub x, binop? .sub y with
    | some (_, a, b), some (_, b', a') => specific b b' && specific a a'
    | _, _ => false

/-- `m_Sub(m_Value(Y), m_Specific(S))` on `V`, binding `Y`. -/
def subOf (s v : Term w) : Option (Term w) :=
  match binop? .sub v with
  | some (_, y, b) => if specific s b then some y else none
  | none => none

/-- `m_Xor(m_Value(Y), m_SignMask())` on `V`, binding `Y`. Not commutative. -/
def xorSignMask (v : Term w) : Option (Term w) :=
  match binop? .xor v with
  | some (_, y, b) => if signMask b then some y else none
  | none => none

/-! ### The model -/

/-- `simplifyAddInst` once `foldOrCommuteConstant` has put a lone constant on the right, step by step. -/
def simplifyAddInst.steps (op0 op1 : Term w) (isNSW isNUW : Bool) (maxRecurse : Nat) : List (Step w) :=
  [ -- X + poison -> poison
    if isPoison op1 then .fire "IS.simplifyAddInst.L601" (.old op1) else .next,
    -- X + undef -> undef
    if isUndefValue op1 then .fire "IS.simplifyAddInst.L605" (.old op1) else .next,
    -- X + 0 -> X
    if zero op1 then .fire "IS.simplifyAddInst.L609" (.old op0) else .next,
    -- If two operands are negative, return 0.
    if isKnownNegation op0 op1 then .fire "IS.simplifyAddInst.L613" (.const 0#w) else .next,
    -- X + (Y - X) -> Y, (Y - X) + X -> Y
    match subOf op0 op1, subOf op1 op0 with
    | some y, _ => .fire "IS.simplifyAddInst.L621" (.old y)
    | none, some y => .fire "IS.simplifyAddInst.L621" (.old y)
    | none, none => .next,
    -- X + ~X -> -1
    if notWith (specific op1) op0 || notWith (specific op0) op1 then
      .fire "IS.simplifyAddInst.L626" (.const (BitVec.allOnes w))
    else .next,
    -- add nsw/nuw (xor Y, signmask), signmask --> Y
    if (isNSW || isNUW) && signMask op1 then
      match xorSignMask op0 with
      | some y => .fire "IS.simplifyAddInst.L633" (.old y)
      | none => .next
    else .next,
    -- add nuw %x, -1  ->  -1
    if isNUW && allOnes op1 then .fire "IS.simplifyAddInst.L637" (.old op1) else .next,
    -- i1 add -> xor: what simplifyXorInst answers isn't modelled.
    if maxRecurse != 0 && w == 1 then .delegate "simplifyXorInst" else .next,
    -- simplifyAssociativeBinOp: `if (!MaxRecurse--) return nullptr;`, and each transform it tries needs an `add`
    -- operand.
    if maxRecurse == 0 then .decline else .next,
    match op0, op1 with
    | .bin _ .add .., _ | _, .bin _ .add .. => .delegate "simplifyAssociativeBinOp"
    | _, _ => .next ]

/-- `simplifyAddInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`. `foldOrCommuteConstant` folds two constants, which the
constant folder does, at `IS.foldOrCommuteConstant.L582`, and swaps a lone constant to the right. -/
def simplifyAddInst (op0 op1 : Term w) (isNSW isNUW : Bool) (maxRecurse : Nat) : Result w :=
  if op0.isConstant then
    if op1.isConstant then .delegated "ConstantFoldBinaryOpOperands"
    else run (simplifyAddInst.steps op1 op0 isNSW isNUW maxRecurse)
  else run (simplifyAddInst.steps op0 op1 isNSW isNUW maxRecurse)

/-- What InstSimplify does with an instruction it reaches: `simplifyInstruction` calls `simplifyAddInst` on an `add`,
with the instruction's own flags and `MaxRecurse` at `RecursionLimit`, 3. -/
def simplifyAddInst.onInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .add f a b => simplifyAddInst a b f.nsw f.nuw 3
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

/-- The `add` `simplifyAddInst` replaces, with its operands and flags. -/
def addSrc (op0 op1 : Term w) (isNSW isNUW : Bool) : Repl w :=
  .bin .add { nuw := isNUW, nsw := isNSW } (.old op0) (.old op1)

theorem addSrc_eval (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (addSrc op0 op1 isNSW isNUW).eval ρ = Outcome.ok (Val.add (op0.denote ρ) (op1.denote ρ) isNUW isNSW) := rfl

theorem addSrc_comm (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (addSrc op0 op1 isNSW isNUW).eval ρ = (addSrc op1 op0 isNSW isNUW).eval ρ := by
  rw [addSrc_eval, addSrc_eval, Lemmas.add_comm]

/-- An `add` that refines `r` as a value refines it as a run. -/
theorem refines_ok {a b : Val w} (h : Refines a b) : Refines (Outcome.ok a) (Outcome.ok b) :=
  (Refine.outcome_ok_ok a b).2 h

theorem sub_denote {ρ : Env} {t a b : Term w} {f : Flags} (h : binop? .sub t = some (f, a, b))
    (hc : t.Consistent ρ) : t.denote ρ = Val.sub (a.denote ρ) (b.denote ρ) f.nuw f.nsw :=
  (ok_inj (binop?_consistent h hc).2.2).symm

theorem xor_denote {ρ : Env} {t a b : Term w} {f : Flags} (h : binop? .xor t = some (f, a, b))
    (hc : t.Consistent ρ) : t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) :=
  (ok_inj (binop?_consistent h hc).2.2).symm

theorem cst_eq {ρ : Env} {t : Term w} {c : BitVec w} (h : cst (· == c) t = true) : t.denote ρ = some c := by
  obtain ⟨c', hc', hd⟩ := cst_denote (ρ := ρ) h
  simp only [beq_iff_eq] at hc'
  rw [hd, hc']

/-- `IS.simplifyAddInst.L601`: `X + poison` to poison. -/
theorem simplifyAddInst.L601 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : isPoison op1 = true) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [addSrc_eval, isPoison_denote h, Lemmas.add_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyAddInst.L605`: `X + undef` to `undef`, which without `undef` is `X + poison` to poison. -/
theorem simplifyAddInst.L605 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (u1 : op1.hasUndef = false)
    (h : isUndefValue op1 = true) : Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [addSrc_eval, isUndefValue_denote h u1, Lemmas.add_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyAddInst.L609`: `X + 0` to `X`. -/
theorem simplifyAddInst.L609 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (h : zero op1 = true) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [addSrc_eval, cst_eq h, Generic.add_zero]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyAddInst.L613`: `X + Y` to 0, where `X` and `Y` are known negations of each other. -/
theorem simplifyAddInst.L613 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : isKnownNegation op0 op1 = true) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [addSrc_eval]
  refine refines_ok ?_
  simp only [isKnownNegation, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · -- (0 - Y) + Y
    unfold isKnownNegation.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c0, cst_eq h.1, specific_denote h.2]
      exact Lemmas.add_sub_cancel_refines _ _ _ _ _ _
    · cases h
  · -- X + (0 - X)
    unfold isKnownNegation.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c1, cst_eq h.1, specific_denote h.2, Lemmas.add_comm]
      exact Lemmas.add_sub_cancel_refines _ _ _ _ _ _
    · cases h
  · -- (A - B) + (B - A)
    unfold isKnownNegation.subSwapped at h
    split at h
    · next f a b f' b' a' hs hs' =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c0, sub_denote hs' c1, specific_denote h.1, specific_denote h.2]
      exact Lemmas.add_sub_sub_refines _ _ _ _ _ _ _ _
    · cases h

theorem subOf_denote {ρ : Env} {s v y : Term w} (h : subOf s v = some y) (hc : v.Consistent ρ) :
    ∃ f : Flags, v.denote ρ = Val.sub (y.denote ρ) (s.denote ρ) f.nuw f.nsw := by
  unfold subOf at h
  split at h
  · next f y' b hs =>
    split at h
    · next hb =>
      cases h
      exact ⟨f, by rw [sub_denote hs hc, specific_denote hb]⟩
    · cases h
  · cases h

/-- `IS.simplifyAddInst.L621`, first match: `X + (Y - X)` to `Y`. -/
theorem simplifyAddInst.L621 (ρ : Env) (op0 op1 y : Term w) (isNSW isNUW : Bool) (c1 : op1.Consistent ρ)
    (h : subOf op0 op1 = some y) : Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old y).eval ρ) := by
  obtain ⟨f, hd⟩ := subOf_denote h c1
  rw [addSrc_eval, hd, Lemmas.add_comm]
  exact refines_ok (Lemmas.add_sub_cancel_refines _ _ _ _ _ _)

/-- `IS.simplifyAddInst.L621`, second match: `(Y - X) + X` to `Y`. -/
theorem simplifyAddInst.L621_swapped (ρ : Env) (op0 op1 y : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (h : subOf op1 op0 = some y) : Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old y).eval ρ) := by
  obtain ⟨f, hd⟩ := subOf_denote h c0
  rw [addSrc_eval, hd]
  exact refines_ok (Lemmas.add_sub_cancel_refines _ _ _ _ _ _)

theorem notWith_specific_denote {ρ : Env} {s t : Term w} (h : notWith (specific s) t = true) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (some (BitVec.allOnes w)) (s.denote ρ) ∨
      t.denote ρ = Val.xor (s.denote ρ) (some (BitVec.allOnes w)) := by
  unfold notWith at h
  split at h
  · next f a b hx =>
    rw [xor_denote hx hc]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact Or.inl (by rw [cst_eq ha, specific_denote hb])
    · exact Or.inr (by rw [cst_eq hb, specific_denote ha])
  · cases h

/-- `IS.simplifyAddInst.L626`: `X + ~X` and `~X + X` to -1. -/
theorem simplifyAddInst.L626 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : (notWith (specific op1) op0 || notWith (specific op0) op1) = true) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  rw [addSrc_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rcases notWith_specific_denote h c0 with hd | hd <;> rw [hd]
    · exact Lemmas.add_not_left_refines _ _ _
    · exact Lemmas.add_not_right_refines _ _ _
  · rcases notWith_specific_denote h c1 with hd | hd <;> rw [hd, Lemmas.add_comm]
    · exact Lemmas.add_not_left_refines _ _ _
    · exact Lemmas.add_not_right_refines _ _ _

/-- `IS.simplifyAddInst.L633`: `add nsw/nuw (xor Y, signmask), signmask` to `Y`. The flags aren't needed: the rewrite
is right without them, as #47 found. -/
theorem simplifyAddInst.L633 (ρ : Env) (op0 op1 y : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (hm : signMask op1 = true) (h : xorSignMask op0 = some y) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old y).eval ρ) := by
  unfold xorSignMask at h
  split at h
  · next f y' b hx =>
    split at h
    · next hb =>
      cases h
      rw [addSrc_eval, xor_denote hx c0, cst_eq hb, cst_eq hm]
      exact refines_ok (Lemmas.add_xor_signMask_refines _ _ _)
    · cases h
  · cases h

/-- `IS.simplifyAddInst.L637`: `add nuw X, -1` to -1. -/
theorem simplifyAddInst.L637 (ρ : Env) (op0 op1 : Term w) (isNSW : Bool) (h : allOnes op1 = true) :
    Refines ((addSrc op0 op1 isNSW true).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [addSrc_eval, Repl.eval_old, cst_eq h]
  exact refines_ok (Lemmas.add_nuw_allOnes_refines _ _)

/-! ### The fold -/

/-- Every step of `simplifyAddInst` that fires is right. -/
theorem simplifyAddInst.steps_sound (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyAddInst.steps op0 op1 isNSW isNUW n →
      Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyAddInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAddInst.L601 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAddInst.L605 ρ op0 op1 isNSW isNUW u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAddInst.L609 ρ op0 op1 isNSW isNUW (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAddInst.L613 ρ op0 op1 isNSW isNUW c0 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;> obtain ⟨-, rfl⟩ := h
    · exact simplifyAddInst.L621 ρ op0 op1 _ isNSW isNUW c1 (by assumption)
    · exact simplifyAddInst.L621_swapped ρ op0 op1 _ isNSW isNUW c0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAddInst.L626 ρ op0 op1 isNSW isNUW c0 c1 (by assumption)
  · split at h
    · next hm =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next y hy =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true] at hm
      exact simplifyAddInst.L633 ρ op0 op1 _ isNSW isNUW c0 hm.2 hy
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨rfl, ha⟩ := hc
    exact simplifyAddInst.L637 ρ op0 op1 isNSW ha
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifyAddInst`: every value the model returns refines the `add` it replaces, at every width,
for both flags and every recursion budget, in every run its operands are consistent with, poison included. It says
nothing about operands that reach an `undef`. -/
theorem simplifyAddInst.sound (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    {r : Repl w} (h : simplifyAddInst op0 op1 isNSW isNUW n = .value r) :
    Refines ((addSrc op0 op1 isNSW isNUW).eval ρ) (r.eval ρ) := by
  unfold simplifyAddInst at h
  split at h
  · split at h
    · cases h
    · rw [addSrc_comm]
      exact run_sound (simplifyAddInst.steps_sound ρ op1 op0 isNSW isNUW n c1 c0 u0) h
  · exact run_sound (simplifyAddInst.steps_sound ρ op0 op1 isNSW isNUW n c0 c1 u1) h

end Peephole.IS
