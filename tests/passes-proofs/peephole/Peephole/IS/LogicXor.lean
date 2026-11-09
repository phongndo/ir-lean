import Peephole.IS.LogicAnd

/-! # InstSimplify's `simplifyXorInst`, and its rewrites for every input

`simplifyXorInst`, with its lambda `foldAndOrNot`, is at `llvm/lib/Analysis/InstructionSimplify.cpp:2530-2607` at
`llvmorg-23.1.3`. This is its model on `Peephole.Term`, step by step in the C++'s order. Each step that rewrites
carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyXorInst.L2537` | `X ^ poison` to poison |
| `IS.simplifyXorInst.L2541` | `A ^ undef` to `undef`. Only `undef` reaches it, so it's listed unproved; see below |
| `IS.simplifyXorInst.L2545` | `A ^ 0` to `A` |
| `IS.simplifyXorInst.L2549` | `A ^ A` to 0 |
| `IS.simplifyXorInst.L2553` | `A ^ ~A` and `~A ^ A` to -1 |
| `IS.simplifyXorInst.foldAndOrNot.L2560` | `(~A & B) ^ (A \| B)` to `A`, in every order |
| `IS.simplifyXorInst.foldAndOrNot.L2569` | `(~A \| B) ^ (A & B)` to `~A`, in every order |
| `IS.simplifyXorInst.L2603` | `(sub nuw C, X) ^ C` to `X`, where `C` is a mask of low bits |

`IS.simplifyXorInst.L2541` isn't proved: without `undef`, `isUndefValue(Op1)` holds only of poison, which `L2537`
takes first, so only an `undef` operand reaches its step, and every theorem assumes none does. Its theorem is kept,
about the poison case the step before never leaves to it, and says nothing past what `L2537`'s does.

`simplifyXorInst.sound` puts them together with the folds it calls: every value the model returns refines the `xor`, at
every width and recursion budget, poison included. -/

namespace Peephole.IS

open IRLean Logic

variable {w : Nat}

namespace Logic

/-- `m_NUWSub(m_Specific(S), m_Value(X))` on `T`: `X`. -/
def nuwSubOf? (s t : Term w) : Option (Term w) :=
  match binop? .sub t with
  | some (f, a, x) => if f.nuw && specific s a then some x else none
  | none => none

end Logic

/-! ## `simplifyXorInst` -/

/-- The lambda `foldAndOrNot(X, Y)` in `simplifyXorInst`, step by step. -/
def simplifyXorInst.foldAndOrNot.steps (X Y : Term w) : List (Step w) :=
  [ -- (~A & B) ^ (A | B) --> A -- There are 8 commuted variants.
    match cbind .and not? some X with
    | some (A, B) => if isOf .or A B Y then .fire "IS.simplifyXorInst.foldAndOrNot.L2560" (.old A) else .next
    | none => .next,
    -- (~A | B) ^ (A & B) --> ~A -- There are 8 commuted variants.
    -- The 'not' op must contain a complete -1 operand (no undef elements for
    -- vector) for the transform to be safe.
    match cbind .or (fun u => (not? u).map fun a => (a, u)) some X with
    | some ((A, NotA), B) =>
      if isOf .and A B Y then .fire "IS.simplifyXorInst.foldAndOrNot.L2569" (.old NotA) else .next
    | none => .next ]

/-- `simplifyXorInst` once `foldOrCommuteConstant` has put a lone constant on the right, step by step. -/
def simplifyXorInst.steps (x : Option Ext) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- X ^ poison -> poison
    if isPoison op1 then .fire "IS.simplifyXorInst.L2537" (.old op1) else .next,
    -- A ^ undef -> undef
    if isUndefValue op1 then .fire "IS.simplifyXorInst.L2541" (.old op1) else .next,
    -- A ^ 0 = A
    if zero op1 then .fire "IS.simplifyXorInst.L2545" (.old op0) else .next,
    -- A ^ A = 0
    if specific op0 op1 then .fire "IS.simplifyXorInst.L2549" (.const 0#w) else .next,
    -- A ^ ~A  =  ~A ^ A  =  -1
    if notWith (specific op1) op0 || notWith (specific op0) op1 then
      .fire "IS.simplifyXorInst.L2553" (.const (BitVec.allOnes w))
    else .next,
    forward (simplifyXorInst.foldAndOrNot.steps op0 op1),
    forward (simplifyXorInst.foldAndOrNot.steps op1 op0),
    forward (simplifyLogicOfAddSub.steps op0 op1 .xor),
    -- Try some generic simplifications for associative operations.
    if assocMayAnswer x .xor op0 op1 n then .delegate "simplifyAssociativeBinOp" else .next,
    -- Threading Xor over selects and phi nodes is pointless, so don't bother.
    domEqStep x op0 op1 n,
    -- (xor (sub nuw C_Mask, X), C_Mask) -> X
    match nuwSubOf? op1 op0 with
    | some X => if cst isMask op1 then .fire "IS.simplifyXorInst.L2603" (.old X) else .next
    | none => .next ]

/-- `simplifyXorInst(Op0, Op1, Q, MaxRecurse)`. `foldOrCommuteConstant` folds two constants, which the constant folder
does, at `IS.foldOrCommuteConstant.L582`, and swaps a lone constant to the right. -/
def simplifyXorInst (x : Option Ext) (op0 op1 : Term w) (n : Nat) : Result w :=
  if op0.isConstant then
    if op1.isConstant then .delegated "ConstantFoldBinaryOpOperands"
    else run (simplifyXorInst.steps x op1 op0 n)
  else run (simplifyXorInst.steps x op0 op1 n)

/-- What InstSimplify does with an instruction it reaches: `simplifyInstruction` calls `simplifyXorInst` on an `xor`,
with `MaxRecurse` at `RecursionLimit`, 3. What the core `Oracle` doesn't answer, `Logic.Ext.ofTerms` answers from the operands' trees. -/
def simplifyXorInst.onInst (_o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .xor _ a b => simplifyXorInst (some Ext.ofTerms) a b 3
  | _, _ => .null

/-! ### The rewrites, one theorem each -/

/-- `IS.simplifyXorInst.L2537`: `X ^ poison` to poison. -/
theorem simplifyXorInst.L2537 (ρ : Env) (op0 op1 : Term w) (h : isPoison op1 = true) :
    Refines ((xorSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [xorSrc_eval, isPoison_denote h, Lemmas.Logic.xor_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyXorInst.L2541`: `A ^ undef` to `undef`, which without `undef` is `A ^ poison` to poison. -/
theorem simplifyXorInst.L2541 (ρ : Env) (op0 op1 : Term w) (u1 : op1.hasUndef = false)
    (h : isUndefValue op1 = true) : Refines ((xorSrc op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [xorSrc_eval, isUndefValue_denote h u1, Lemmas.Logic.xor_none_right]
  exact refines_ok (Refine.val_none _)

/-- `IS.simplifyXorInst.L2545`: `A ^ 0` to `A`. -/
theorem simplifyXorInst.L2545 (ρ : Env) (op0 op1 : Term w) (h : zero op1 = true) :
    Refines ((xorSrc op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [xorSrc_eval, cst_eq h, Generic.xor_zero]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyXorInst.L2549`: `A ^ A` to 0. -/
theorem simplifyXorInst.L2549 (ρ : Env) (op0 op1 : Term w) (h : specific op0 op1 = true) :
    Refines ((xorSrc op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [xorSrc_eval, specific_denote h]
  exact refines_ok (Generic.xor_self_refines _)

/-- `IS.simplifyXorInst.L2553`: `A ^ ~A` and `~A ^ A` to -1. -/
theorem simplifyXorInst.L2553 (ρ : Env) (op0 op1 : Term w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h : (notWith (specific op1) op0 || notWith (specific op0) op1) = true) :
    Refines ((xorSrc op0 op1).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨a, ha, -, hd⟩ := notWith_denote h c0
    rw [xorSrc_eval, hd, specific_denote ha]
    exact refines_ok (Lemmas.xor_not_self_refines _)
  · obtain ⟨a, ha, -, hd⟩ := notWith_denote h c1
    rw [xorSrc_eval, hd, specific_denote ha, Lemmas.Logic.xor_comm]
    exact refines_ok (Lemmas.xor_not_self_refines _)

/-- `IS.simplifyXorInst.foldAndOrNot.L2560`: `(~A & B) ^ (A | B)` to `A`, in every order. -/
theorem simplifyXorInst.foldAndOrNot.L2560 (ρ : Env) (X Y A B : Term w) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    (h0 : cbind .and not? some X = some (A, B)) (h1 : isOf .or A B Y = true) :
    Refines ((xorSrc X Y).eval ρ) ((Repl.old A).eval ρ) := by
  obtain ⟨a, b, ha, hb, ca, -, hx⟩ := cbind_and h0 cX
  cases hb
  obtain ⟨-, had⟩ := not?_denote ha ca
  obtain ⟨d, hy⟩ := isOf_or h1 cY
  rw [xorSrc_eval, Repl.eval_old, hx, had, hy]
  exact refines_ok (Lemmas.xor_and_not_or_refines _ _ _)

/-- `IS.simplifyXorInst.foldAndOrNot.L2569`: `(~A | B) ^ (A & B)` to `~A`, in every order. -/
theorem simplifyXorInst.foldAndOrNot.L2569 (ρ : Env) (X Y A NotA B : Term w) (cX : X.Consistent ρ)
    (cY : Y.Consistent ρ) (h0 : cbind .or (fun u => (not? u).map fun a => (a, u)) some X = some ((A, NotA), B))
    (h1 : isOf .and A B Y = true) : Refines ((xorSrc X Y).eval ρ) ((Repl.old NotA).eval ρ) := by
  obtain ⟨u, b, d, hu, hb, cu, -, hx⟩ := cbind_or h0 cX
  cases hb
  cases hn : not? u with
  | none => simp [hn] at hu
  | some a =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain ⟨-, hnd⟩ := not?_denote hn cu
    rw [xorSrc_eval, Repl.eval_old, hx, hnd, isOf_and h1 cY]
    exact refines_ok (Lemmas.xor_or_not_and_refines _ _ _)

/-- `IS.simplifyXorInst.L2603`: `(sub nuw C, X) ^ C` to `X`, where `C` is a mask of low bits. -/
theorem simplifyXorInst.L2603 (ρ : Env) (op0 op1 X : Term w) (c0 : op0.Consistent ρ) (hs : nuwSubOf? op1 op0 = some X)
    (hm : cst isMask op1 = true) : Refines ((xorSrc op0 op1).eval ρ) ((Repl.old X).eval ρ) := by
  unfold nuwSubOf? at hs
  split at hs
  · next f a x hb =>
    split at hs
    · next hc =>
      cases hs
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hnuw, ha⟩ := hc
      obtain ⟨-, -, hd⟩ := sub_denote' hb c0
      obtain ⟨c, hmc, hc1⟩ := cst_denote (ρ := ρ) hm
      rw [xorSrc_eval, Repl.eval_old, hd, specific_denote ha, hc1, hnuw]
      exact refines_ok (Lemmas.xor_sub_nuw_lowMask_refines _ _ _ (isMask_spec hmc))
    · cases hs
  · cases hs

/-! ### The fold -/

/-- Theorem 1 for the lambda `foldAndOrNot`: what it returns refines the `xor`. -/
theorem simplifyXorInst.foldAndOrNot.sound (ρ : Env) (X Y : Term w) (cX : X.Consistent ρ) (cY : Y.Consistent ρ)
    {r : Repl w} (h : run (simplifyXorInst.foldAndOrNot.steps X Y) = .value r) :
    Refines ((xorSrc X Y).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((xorSrc X Y).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyXorInst.foldAndOrNot.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyXorInst.foldAndOrNot.L2560 ρ X Y _ _ cX cY (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h
  · split at h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyXorInst.foldAndOrNot.L2569 ρ X Y _ _ _ cX cY (by assumption) (by assumption)
    · simp only [reduceCtorEq] at h

/-- Every step of `simplifyXorInst` that fires is right, the folds it forwards to included. -/
theorem simplifyXorInst.steps_sound (ρ : Env) (x : Option Ext) (op0 op1 : Term w) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyXorInst.steps x op0 op1 n → Refines ((xorSrc op0 op1).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyXorInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyXorInst.L2537 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyXorInst.L2541 ρ op0 op1 u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyXorInst.L2545 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyXorInst.L2549 ρ op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyXorInst.L2553 ρ op0 op1 c0 c1 (by assumption)
  · exact simplifyXorInst.foldAndOrNot.sound ρ op0 op1 c0 c1 (run_of_forward h.symm)
  · rw [xorSrc_comm]
    exact simplifyXorInst.foldAndOrNot.sound ρ op1 op0 c1 c0 (run_of_forward h.symm)
  · exact simplifyLogicOfAddSub.sound ρ .xor false op0 op1 c0 c1 u0 u1 (.inr (.inr rfl)) (run_of_forward h.symm)
  · split at h <;> simp only [reduceCtorEq] at h
  · unfold domEqStep at h
    repeat' (split at h <;> try simp only [reduceCtorEq] at h)
  · split at h
    · next X hs =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyXorInst.L2603 ρ op0 op1 X c0 hs (by assumption)
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifyXorInst`: every value the model returns refines the `xor` it replaces, at every width and
recursion budget, in every run its operands are consistent with, poison included. No analysis's answer is used, so
nothing is assumed of the `Logic.Ext`: it only says where the model hands over to `simplifyByDomEq`. It says nothing
about operands that reach an `undef`. -/
theorem simplifyXorInst.sound (ρ : Env) (x : Option Ext) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {r : Repl w}
    (h : simplifyXorInst x op0 op1 n = .value r) : Refines ((xorSrc op0 op1).eval ρ) (r.eval ρ) := by
  unfold simplifyXorInst at h
  split at h
  · split at h
    · cases h
    · rw [xorSrc_comm]
      exact run_sound (simplifyXorInst.steps_sound ρ x op1 op0 n c1 c0 u1 u0) h
  · exact run_sound (simplifyXorInst.steps_sound ρ x op0 op1 n c0 c1 u0 u1) h

/-- What `onInst` answers for an `xor` refines it. -/
theorem simplifyXorInst.onInst_sound (ρ : Env) (o : Oracle) (t : Term w) (ht : t.Consistent ρ)
    (hu : t.hasUndef = false) {r : Repl w} (h : simplifyXorInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  cases t with
  | bin id op f a b =>
    cases op <;> simp only [simplifyXorInst.onInst, reduceCtorEq] at h
    obtain ⟨ca, cb, -⟩ := ht
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at hu
    exact simplifyXorInst.sound ρ _ a b 3 ca cb hu.1 hu.2 h
  | _ => simp [simplifyXorInst.onInst] at h

end Peephole.IS
