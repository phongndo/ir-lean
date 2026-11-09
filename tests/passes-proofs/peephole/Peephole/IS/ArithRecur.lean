import Peephole.IS.ArithCore

/-! # The helper folds InstSimplify's arithmetic folds share

`simplifyByDomEq`, `simplifyAssociativeBinOp`, `expandBinOp`, `expandCommutativeBinOp` and `threadBinOpOverSelect`, at
`llvm/lib/Analysis/InstructionSimplify.cpp:198-421` and `712-739` at `llvmorg-23.1.3`, step by step in the C++'s order.
Each is called with an opcode, and modelled for every one: a theorem about one holds for the opcodes its C++ asserts
or its callers pass. The source each replaces is its caller's instruction, `binSrc op f LHS RHS`, with any flags.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyByDomEq.L727` | `X - Y`, `X ^ Y`, `X urem Y`, `X srem Y` to 0 where a dominating condition says `X == Y` |
| `IS.simplifyByDomEq.L731` | `X udiv Y`, `X sdiv Y` to 1 there |
| `IS.simplifyByDomEq.L736` | `X & Y`, `X | Y` to `Y` there |
| `IS.simplifyAssociativeBinOp.L274` | `(A op B) op C` to `A op B` where `B op C` simplifies to `B` |
| `IS.simplifyAssociativeBinOp.L294` | `A op (B op C)` to `B op C` where `A op B` simplifies to `B` |
| `IS.simplifyAssociativeBinOp.L318` | `(A op B) op C` to `A op B` where `C op A` simplifies to `A` |
| `IS.simplifyAssociativeBinOp.L338` | `A op (B op C)` to `B op C` where `C op A` simplifies to `C` |
| `IS.expandBinOp.L218` | `(B0 op' B1) op X` to `B0 op' B1` where `B0 op X` and `B1 op X` simplify to `B0` and `B1`, or to `B1` and `B0` |
| `IS.threadBinOpOverSelect.L394` | `(select C, T, F) op X` to the select where `T op X` and `F op X` simplify to `T` and `F` |

The returns of a recursive call's answer, such as `return W;` after reassociating, are forwards, not sites: each fires
as `"simplifyBinOp"`, and has its own theorem here too, so each helper's `sound` covers every value it returns. -/

namespace Peephole.IS

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-! ## `simplifyByDomEq` -/

/-- `simplifyByDomEq(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step. -/
def simplifyByDomEq.steps (d : DomOracle) (op : BinOp) (op0 op1 : Term w) (maxRecurse : Nat) : List (Step w) :=
  [ -- Recursive run it can not get any benefit
    if maxRecurse != recursionLimit then .decline else .next,
    if d.implied .eq op0 op1 == some true && (op == .sub || op == .xor || op == .urem || op == .srem) then
      .fire "IS.simplifyByDomEq.L727" (.const 0#w)
    else .next,
    if d.implied .eq op0 op1 == some true && (op == .sdiv || op == .udiv) then
      .fire "IS.simplifyByDomEq.L731" (.const 1#w)
    else .next,
    -- Could be either one - choose Op1 since that's more likely a constant.
    if d.implied .eq op0 op1 == some true && (op == .and || op == .or) then
      .fire "IS.simplifyByDomEq.L736" (.old op1)
    else .next ]

/-- Under a dominating `op0 == op1`, the source refines `t` if `op` on one value twice does. -/
private theorem byDomEq_of {ρ : Env} {d : DomOracle} (hd : d.Sound ρ) {op : BinOp} {f : Flags} {op0 op1 : Term w}
    {t : Val w} (himp : d.implied .eq op0 op1 = some true)
    (h : ∀ x, Refines (op.eval f (some x) (some x)) (Outcome.ok t)) :
    Refines ((binSrc op f op0 op1).eval ρ) (Outcome.ok t) := by
  rw [binSrc_eval]
  cases h0 : op0.denote ρ with
  | none => exact eval_none_left op f _ _
  | some x =>
  cases h1 : op1.denote ρ with
  | none => exact eval_none_right op f _ _
  | some y =>
  obtain rfl := hd.eq himp h0 h1
  exact h x

/-- `IS.simplifyByDomEq.L727`: `X - Y`, `X ^ Y`, `X urem Y` and `X srem Y` to 0, where a dominating condition implies
`X == Y`. -/
theorem simplifyByDomEq.L727 (ρ : Env) (d : DomOracle) (hd : d.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (himp : d.implied .eq op0 op1 = some true)
    (hop : (op == .sub || op == .xor || op == .urem || op == .srem) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  refine byDomEq_of hd himp fun x => ?_
  cases op <;> simp at hop
  · exact ok_refines (Generic.sub_self_refines _ _ _)
  · exact Lemmas.urem_self_refines (some x)
  · exact Lemmas.srem_self_refines (some x)
  · exact ok_refines (Generic.xor_self_refines _)

/-- `IS.simplifyByDomEq.L731`: `X udiv Y` and `X sdiv Y` to 1, where a dominating condition implies `X == Y`. -/
theorem simplifyByDomEq.L731 (ρ : Env) (d : DomOracle) (hd : d.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (himp : d.implied .eq op0 op1 = some true) (hop : (op == .sdiv || op == .udiv) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 1#w).eval ρ) := by
  refine byDomEq_of hd himp fun x => ?_
  cases op <;> simp at hop
  · exact Lemmas.udiv_self_refines (some x) f.exact
  · exact Lemmas.sdiv_self_refines (some x) f.exact

/-- `IS.simplifyByDomEq.L736`: `X & Y` and `X | Y` to `Y`, where a dominating condition implies `X == Y`. -/
theorem simplifyByDomEq.L736 (ρ : Env) (d : DomOracle) (hd : d.Sound ρ) (op : BinOp) (f : Flags) (op0 op1 : Term w)
    (himp : d.implied .eq op0 op1 = some true) (hop : (op == .and || op == .or) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  rw [binSrc_eval, Repl.eval_old]
  cases h0 : op0.denote ρ with
  | none => exact eval_none_left op f _ _
  | some x =>
  cases h1 : op1.denote ρ with
  | none => exact eval_none_right op f _ _
  | some y =>
  obtain rfl := hd.eq himp h0 h1
  cases op <;> simp at hop
  · exact ok_refines (by rw [Generic.and_self]; exact Refine.refl_val _)
  · exact ok_refines (Generic.or_self_disjoint_refines _ _)

/-- Every step of `simplifyByDomEq` that fires is right, for the source's opcode with any flags. -/
theorem simplifyByDomEq.steps_sound (ρ : Env) (d : DomOracle) (hd : d.Sound ρ) (op : BinOp) (f : Flags)
    (op0 op1 : Term w) (n : Nat) :
    ∀ s r, Step.fire s r ∈ simplifyByDomEq.steps d op op0 op1 n → Refines ((binSrc op f op0 op1).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyByDomEq.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact simplifyByDomEq.L727 ρ d hd op f op0 op1 hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact simplifyByDomEq.L731 ρ d hd op f op0 op1 hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact simplifyByDomEq.L736 ρ d hd op f op0 op1 hc.1 hc.2

/-! ## `simplifyAssociativeBinOp` -/

/-- `simplifyAssociativeBinOp(Opcode, LHS, RHS, Q, MaxRecurse)`, step by step: one step for each transform, which
returns at its site, or forwards what the second recursive call answers. -/
def simplifyAssociativeBinOp.steps (r : Recur) (op : BinOp) (lhs rhs : Term w) (maxRecurse : Nat) :
    List (Step w) :=
  [ -- Recursion is always used, so bail out at once if we already hit the limit.
    if maxRecurse == 0 then .decline else .next,
    -- Transform: "(A op B) op C" ==> "A op (B op C)" if it simplifies completely.
    match binop? op lhs with
    | some (_, a, b) =>
      -- Does "B op C" simplify?
      (r.binOp (maxRecurse - 1) op b rhs).bind "simplifyBinOp" .next fun v =>
        -- It does!  Return "A op V" if it simplifies or is already available.
        -- If V equals B then "A op V" is just the LHS.
        if specific b v then .fire "IS.simplifyAssociativeBinOp.L274" (.old lhs)
        -- Otherwise return "A op V" if it simplifies.
        else (r.binOp (maxRecurse - 1) op a v).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- Transform: "A op (B op C)" ==> "(A op B) op C" if it simplifies completely.
    match binop? op rhs with
    | some (_, b, c) =>
      -- Does "A op B" simplify?
      (r.binOp (maxRecurse - 1) op lhs b).bind "simplifyBinOp" .next fun v =>
        -- If V equals B then "V op C" is just the RHS.
        if specific b v then .fire "IS.simplifyAssociativeBinOp.L294" (.old rhs)
        -- Otherwise return "V op C" if it simplifies.
        else (r.binOp (maxRecurse - 1) op v c).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- The remaining transforms require commutativity as well as associativity.
    if !isCommutative op then .decline else .next,
    -- Transform: "(A op B) op C" ==> "(C op A) op B" if it simplifies completely.
    match binop? op lhs with
    | some (_, a, b) =>
      -- Does "C op A" simplify?
      (r.binOp (maxRecurse - 1) op rhs a).bind "simplifyBinOp" .next fun v =>
        -- If V equals A then "V op B" is just the LHS.
        if specific a v then .fire "IS.simplifyAssociativeBinOp.L318" (.old lhs)
        -- Otherwise return "V op B" if it simplifies.
        else (r.binOp (maxRecurse - 1) op v b).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next,
    -- Transform: "A op (B op C)" ==> "B op (C op A)" if it simplifies completely.
    match binop? op rhs with
    | some (_, b, c) =>
      -- Does "C op A" simplify?
      (r.binOp (maxRecurse - 1) op c lhs).bind "simplifyBinOp" .next fun v =>
        -- If V equals C then "B op V" is just the RHS.
        if specific c v then .fire "IS.simplifyAssociativeBinOp.L338" (.old rhs)
        -- Otherwise return "B op V" if it simplifies.
        else (r.binOp (maxRecurse - 1) op b v).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')
    | none => .next ]

/-- What a sound recursive answer about two values says: the answer is the operation's `raw` value. -/
private theorem recur_val {ρ : Env} {r : Recur} (hr : r.Sound ρ) {n : Nat} {op : BinOp}
    (hop : isAssociative op = true) {a b t : Term w} (h : r.binOp n op a b = .val t) (ca : a.Consistent ρ)
    (cb : b.Consistent ρ) (ua : a.hasUndef = false) (ub : b.hasUndef = false) :
    t.Consistent ρ ∧ t.hasUndef = false ∧
      ∀ x y, a.denote ρ = some x → b.denote ρ = some y → t.denote ρ = some (raw op x y) := by
  obtain ⟨ct, ut, hrf⟩ := hr.binOp n op a b t h ca cb ua ub
  refine ⟨ct, ut, fun x y hx hy => ?_⟩
  rw [hx, hy, eval_assoc_plain hop] at hrf
  exact eq_of_refines_some hrf

/-- A matched associative operator's value, where it's a value, is `raw` of its operands'. -/
private theorem binop_raw {ρ : Env} {op : BinOp} (hop : isAssociative op = true) {t a b : Term w} {g : Flags}
    (h : binop? op t = some (g, a, b)) (hc : t.Consistent ρ) {l : BitVec w} (hl : t.denote ρ = some l) :
    ∃ x y, a.denote ρ = some x ∧ b.denote ρ = some y ∧ l = raw op x y := by
  have := binop?_eval h hc
  rw [hl] at this
  exact eval_assoc_some hop this

/-- The facts each transform's proof starts from. -/
private structure AssocCtx (ρ : Env) (r : Recur) (op : BinOp) (lhs rhs : Term w) : Prop where
  hr : r.Sound ρ
  hop : isAssociative op = true
  cl : lhs.Consistent ρ
  cr : rhs.Consistent ρ
  ul : lhs.hasUndef = false
  ur : rhs.hasUndef = false

/-- `IS.simplifyAssociativeBinOp.L274`: `(A op B) op C` to `A op B`, where `B op C` simplifies to `B`. -/
theorem simplifyAssociativeBinOp.L274 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {a b v : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hl : binop? op lhs = some (g, a, b)) (hv : r.binOp n op b rhs = .val v) (hs : specific b v = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old lhs).eval ρ) := by
  obtain ⟨-, cb, -⟩ := binop?_consistent hl cl
  obtain ⟨-, ub⟩ := binop?_noUndef hl ul
  obtain ⟨-, -, hV⟩ := recur_val hr hop hv cb cr ub ur
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun l z hL hC => ?_
  obtain ⟨x, y, hA, hB, rfl⟩ := binop_raw hop hl cl hL
  have hvb := hV y z hB hC
  rw [specific_denote hs, hB, Option.some.injEq] at hvb
  rw [hL, raw_assoc hop, ← hvb]

/-- `simplifyAssociativeBinOp`'s first transform, where `A op V` simplifies to `W`: `(A op B) op C` to `W`. -/
theorem simplifyAssociativeBinOp.fwd274 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {a b v w' : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hl : binop? op lhs = some (g, a, b)) (hv : r.binOp n op b rhs = .val v) (hw : r.binOp n op a v = .val w') :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨ca, cb, -⟩ := binop?_consistent hl cl
  obtain ⟨ua, ub⟩ := binop?_noUndef hl ul
  obtain ⟨cv, uv, hV⟩ := recur_val hr hop hv cb cr ub ur
  obtain ⟨-, -, hW⟩ := recur_val hr hop hw ca cv ua uv
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun l z hL hC => ?_
  obtain ⟨x, y, hA, hB, rfl⟩ := binop_raw hop hl cl hL
  rw [hW x _ hA (hV y z hB hC), raw_assoc hop]

/-- `IS.simplifyAssociativeBinOp.L294`: `A op (B op C)` to `B op C`, where `A op B` simplifies to `B`. -/
theorem simplifyAssociativeBinOp.L294 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {b c v : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hrh : binop? op rhs = some (g, b, c)) (hv : r.binOp n op lhs b = .val v) (hs : specific b v = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old rhs).eval ρ) := by
  obtain ⟨cb, -, -⟩ := binop?_consistent hrh cr
  obtain ⟨ub, -⟩ := binop?_noUndef hrh ur
  obtain ⟨-, -, hV⟩ := recur_val hr hop hv cl cb ul ub
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun x m hL hR => ?_
  obtain ⟨y, z, hB, hC, rfl⟩ := binop_raw hop hrh cr hR
  have hvb := hV x y hL hB
  rw [specific_denote hs, hB, Option.some.injEq] at hvb
  rw [hR, ← raw_assoc hop, ← hvb]

/-- `simplifyAssociativeBinOp`'s second transform, where `V op C` simplifies to `W`: `A op (B op C)` to `W`. -/
theorem simplifyAssociativeBinOp.fwd294 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {b c v w' : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hrh : binop? op rhs = some (g, b, c)) (hv : r.binOp n op lhs b = .val v) (hw : r.binOp n op v c = .val w') :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old w').eval ρ) := by
  obtain ⟨cb, cc, -⟩ := binop?_consistent hrh cr
  obtain ⟨ub, uc⟩ := binop?_noUndef hrh ur
  obtain ⟨cv, uv, hV⟩ := recur_val hr hop hv cl cb ul ub
  obtain ⟨-, -, hW⟩ := recur_val hr hop hw cv cc uv uc
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun x m hL hR => ?_
  obtain ⟨y, z, hB, hC, rfl⟩ := binop_raw hop hrh cr hR
  rw [hW _ z (hV x y hL hB) hC, raw_assoc hop]

/-- `IS.simplifyAssociativeBinOp.L318`: `(A op B) op C` to `A op B`, where `C op A` simplifies to `A`. -/
theorem simplifyAssociativeBinOp.L318 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {a b v : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hl : binop? op lhs = some (g, a, b)) (hv : r.binOp n op rhs a = .val v) (hs : specific a v = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old lhs).eval ρ) := by
  have hc := isCommutative_of_isAssociative hop
  obtain ⟨ca, -, -⟩ := binop?_consistent hl cl
  obtain ⟨ua, -⟩ := binop?_noUndef hl ul
  obtain ⟨-, -, hV⟩ := recur_val hr hop hv cr ca ur ua
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun l z hL hC => ?_
  obtain ⟨x, y, hA, hB, rfl⟩ := binop_raw hop hl cl hL
  have hva := hV z x hC hA
  rw [specific_denote hs, hA, Option.some.injEq] at hva
  rw [hL, raw_comm hc (raw op x y) z, ← raw_assoc hop, ← hva]

/-- `simplifyAssociativeBinOp`'s third transform, where `V op B` simplifies to `W`: `(A op B) op C` to `W`. -/
theorem simplifyAssociativeBinOp.fwd318 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {a b v w' : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hl : binop? op lhs = some (g, a, b)) (hv : r.binOp n op rhs a = .val v) (hw : r.binOp n op v b = .val w') :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old w').eval ρ) := by
  have hc := isCommutative_of_isAssociative hop
  obtain ⟨ca, cb, -⟩ := binop?_consistent hl cl
  obtain ⟨ua, ub⟩ := binop?_noUndef hl ul
  obtain ⟨cv, uv, hV⟩ := recur_val hr hop hv cr ca ur ua
  obtain ⟨-, -, hW⟩ := recur_val hr hop hw cv cb uv ub
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun l z hL hC => ?_
  obtain ⟨x, y, hA, hB, rfl⟩ := binop_raw hop hl cl hL
  rw [hW _ y (hV z x hC hA) hB, raw_comm hc (raw op x y) z, ← raw_assoc hop]

/-- `IS.simplifyAssociativeBinOp.L338`: `A op (B op C)` to `B op C`, where `C op A` simplifies to `C`. -/
theorem simplifyAssociativeBinOp.L338 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {b c v : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hrh : binop? op rhs = some (g, b, c)) (hv : r.binOp n op c lhs = .val v) (hs : specific c v = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old rhs).eval ρ) := by
  have hc := isCommutative_of_isAssociative hop
  obtain ⟨-, cc, -⟩ := binop?_consistent hrh cr
  obtain ⟨-, uc⟩ := binop?_noUndef hrh ur
  obtain ⟨-, -, hV⟩ := recur_val hr hop hv cc cl uc ul
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun x m hL hR => ?_
  obtain ⟨y, z, hB, hC, rfl⟩ := binop_raw hop hrh cr hR
  have hvc := hV z x hC hL
  rw [specific_denote hs, hC, Option.some.injEq] at hvc
  rw [hR, raw_comm hc x (raw op y z), raw_assoc hop, ← hvc]

/-- `simplifyAssociativeBinOp`'s fourth transform, where `B op V` simplifies to `W`: `A op (B op C)` to `W`. -/
theorem simplifyAssociativeBinOp.fwd338 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat) {g : Flags} {b c v w' : Term w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hrh : binop? op rhs = some (g, b, c)) (hv : r.binOp n op c lhs = .val v) (hw : r.binOp n op b v = .val w') :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old w').eval ρ) := by
  have hc := isCommutative_of_isAssociative hop
  obtain ⟨cb, cc, -⟩ := binop?_consistent hrh cr
  obtain ⟨ub, uc⟩ := binop?_noUndef hrh ur
  obtain ⟨cv, uv, hV⟩ := recur_val hr hop hv cc cl uc ul
  obtain ⟨-, -, hW⟩ := recur_val hr hop hw cb cv ub uv
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun x m hL hR => ?_
  obtain ⟨y, z, hB, hC, rfl⟩ := binop_raw hop hrh cr hR
  rw [hW y _ hB (hV z x hC hL), raw_comm hc x (raw op y z), raw_assoc hop]

/-- A transform's step fires its site, or what the second recursive call answered. -/
private theorem bind_bind_fire {a1 : Ans w} {k1 : Term w → Ans w} {p : Term w → Bool} {site s : String}
    {s0 : Term w → Repl w} {res : Repl w}
    (h : a1.bind "simplifyBinOp" .next (fun t => if p t then .fire site (s0 t)
      else (k1 t).bind "simplifyBinOp" .next fun w' => .fire "simplifyBinOp" (.old w')) = .fire s res) :
    ∃ t, a1 = .val t ∧ ((p t = true ∧ res = s0 t) ∨ ∃ w', k1 t = .val w' ∧ res = .old w') := by
  rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨t, ht, h⟩
  · cases h
  · refine ⟨t, ht, ?_⟩
    split at h
    · next hp => simp only [Step.fire.injEq] at h; exact .inl ⟨hp, h.2.symm⟩
    · rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨w', hw, h⟩
      · cases h
      · simp only [Step.fire.injEq] at h; exact .inr ⟨w', hw, h.2.symm⟩

/-- Every step of `simplifyAssociativeBinOp` that fires is right, for an associative opcode, as its C++ asserts. -/
theorem simplifyAssociativeBinOp.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isAssociative op = true) (f : Flags) (lhs rhs : Term w) (n : Nat)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifyAssociativeBinOp.steps r op lhs rhs n →
      Refines ((binSrc op f lhs rhs).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifyAssociativeBinOp.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h
    · next a b _ hl =>
      obtain ⟨v, hv, (⟨hs, hres⟩ | ⟨w', hw, hres⟩)⟩ := bind_bind_fire h.symm <;> subst hres
      · exact simplifyAssociativeBinOp.L274 ρ r hr op hop f lhs rhs _ cl cr ul ur hl hv hs
      · exact simplifyAssociativeBinOp.fwd274 ρ r hr op hop f lhs rhs _ cl cr ul ur hl hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next b c _ hrh =>
      obtain ⟨v, hv, (⟨hs, hres⟩ | ⟨w', hw, hres⟩)⟩ := bind_bind_fire h.symm <;> subst hres
      · exact simplifyAssociativeBinOp.L294 ρ r hr op hop f lhs rhs _ cl cr ul ur hrh hv hs
      · exact simplifyAssociativeBinOp.fwd294 ρ r hr op hop f lhs rhs _ cl cr ul ur hrh hv hw
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h
    · next a b _ hl =>
      obtain ⟨v, hv, (⟨hs, hres⟩ | ⟨w', hw, hres⟩)⟩ := bind_bind_fire h.symm <;> subst hres
      · exact simplifyAssociativeBinOp.L318 ρ r hr op hop f lhs rhs _ cl cr ul ur hl hv hs
      · exact simplifyAssociativeBinOp.fwd318 ρ r hr op hop f lhs rhs _ cl cr ul ur hl hv hw
    · simp only [reduceCtorEq] at h
  · split at h
    · next b c _ hrh =>
      obtain ⟨v, hv, (⟨hs, hres⟩ | ⟨w', hw, hres⟩)⟩ := bind_bind_fire h.symm <;> subst hres
      · exact simplifyAssociativeBinOp.L338 ρ r hr op hop f lhs rhs _ cl cr ul ur hrh hv hs
      · exact simplifyAssociativeBinOp.fwd338 ρ r hr op hop f lhs rhs _ cl cr ul ur hrh hv hw
    · simp only [reduceCtorEq] at h

/-! ## `expandBinOp` and `expandCommutativeBinOp` -/

/-- `expandBinOp(Opcode, V, OtherOp, OpcodeToExpand, Q, MaxRecurse)`: "V op OtherOp", with `V` "B0 op' B1",
distributed as "(B0 op OtherOp) op' (B1 op OtherOp)". One step: each `return nullptr` declines, and it returns at its
site or forwards what the last recursive call answered. -/
def expandBinOp.steps (r : Recur) (op : BinOp) (v other : Term w) (opex : BinOp) (maxRecurse : Nat) :
    List (Step w) :=
  [ match binop? opex v with
    | none => .decline
    | some (_, b0, b1) =>
      (r.binOp maxRecurse op b0 other).bind "simplifyBinOp" .decline fun l =>
      (r.binOp maxRecurse op b1 other).bind "simplifyBinOp" .decline fun rr =>
      -- Does the expanded pair of binops simplify to the existing binop?
      if (specific b0 l && specific b1 rr) || (isCommutative opex && specific b1 l && specific b0 rr) then
        .fire "IS.expandBinOp.L218" (.old v)
      -- Otherwise, return "L op' R" if it simplifies.
      else (r.binOp maxRecurse opex l rr).bind "simplifyBinOp" .decline fun s => .fire "simplifyBinOp" (.old s) ]

/-- `expandCommutativeBinOp(Opcode, L, R, OpcodeToExpand, Q, MaxRecurse)`, step by step. -/
def expandCommutativeBinOp.steps (r : Recur) (op : BinOp) (l rr : Term w) (opex : BinOp) (maxRecurse : Nat) :
    List (Step w) :=
  [ -- Recursion is always used, so bail out at once if we already hit the limit.
    if maxRecurse == 0 then .decline else .next,
    forward (expandBinOp.steps r op l rr opex (maxRecurse - 1)),
    forward (expandBinOp.steps r op rr l opex (maxRecurse - 1)) ]

/-- `IS.expandBinOp.L218`: `(B0 op' B1) op X` to `B0 op' B1`, where `B0 op X` and `B1 op X` simplify to `B0` and `B1`,
or, for a commutative `op'`, to `B1` and `B0`. For the pairs where `op` distributes over `op'`. -/
theorem expandBinOp.L218 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op opex : BinOp) (hd : distributes op opex = true)
    (f : Flags) (v other : Term w) (n : Nat) {g : Flags} {b0 b1 l rr : Term w}
    (cv : v.Consistent ρ) (co : other.Consistent ρ) (uv : v.hasUndef = false) (uo : other.hasUndef = false)
    (hb : binop? opex v = some (g, b0, b1)) (hl : r.binOp n op b0 other = .val l)
    (hrr : r.binOp n op b1 other = .val rr)
    (hs : ((specific b0 l && specific b1 rr) || (isCommutative opex && specific b1 l && specific b0 rr)) = true) :
    Refines ((binSrc op f v other).eval ρ) ((Repl.old v).eval ρ) := by
  have hop := isAssociative_of_distributes_left hd
  have hcx := isCommutative_of_distributes_right hd
  have hox := isAssociative_of_isCommutative hcx
  obtain ⟨c0, c1, -⟩ := binop?_consistent hb cv
  obtain ⟨u0, u1⟩ := binop?_noUndef hb uv
  obtain ⟨-, -, hL⟩ := recur_val hr hop hl c0 co u0 uo
  obtain ⟨-, -, hR⟩ := recur_val hr hop hrr c1 co u1 uo
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun m o hV hO => ?_
  obtain ⟨x, y, hx, hy, rfl⟩ := binop_raw hox hb cv hV
  have el := hL x o hx hO
  have er := hR y o hy hO
  rw [hV, raw_distrib hd]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with ⟨h0, h1⟩ | ⟨⟨-, h0⟩, h1⟩
  · rw [specific_denote h0, hx, Option.some.injEq] at el
    rw [specific_denote h1, hy, Option.some.injEq] at er
    rw [← el, ← er]
  · rw [specific_denote h0, hy, Option.some.injEq] at el
    rw [specific_denote h1, hx, Option.some.injEq] at er
    rw [← el, ← er, raw_comm hcx]

/-- `expandBinOp`, where "L op' R" simplifies to `S`: `(B0 op' B1) op X` to `S`. -/
theorem expandBinOp.fwd218 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op opex : BinOp) (hd : distributes op opex = true)
    (f : Flags) (v other : Term w) (n : Nat) {g : Flags} {b0 b1 l rr s : Term w}
    (cv : v.Consistent ρ) (co : other.Consistent ρ) (uv : v.hasUndef = false) (uo : other.hasUndef = false)
    (hb : binop? opex v = some (g, b0, b1)) (hl : r.binOp n op b0 other = .val l)
    (hrr : r.binOp n op b1 other = .val rr) (hsv : r.binOp n opex l rr = .val s) :
    Refines ((binSrc op f v other).eval ρ) ((Repl.old s).eval ρ) := by
  have hop := isAssociative_of_distributes_left hd
  have hox := isAssociative_of_isCommutative (isCommutative_of_distributes_right hd)
  obtain ⟨c0, c1, -⟩ := binop?_consistent hb cv
  obtain ⟨u0, u1⟩ := binop?_noUndef hb uv
  obtain ⟨cl, ul, hL⟩ := recur_val hr hop hl c0 co u0 uo
  obtain ⟨cr, ur, hR⟩ := recur_val hr hop hrr c1 co u1 uo
  obtain ⟨-, -, hS⟩ := recur_val hr hox hsv cl cr ul ur
  rw [binSrc_eval, Repl.eval_old]
  refine eval_assoc_refines hop f fun m o hV hO => ?_
  obtain ⟨x, y, hx, hy, rfl⟩ := binop_raw hox hb cv hV
  rw [hS _ _ (hL x o hx hO) (hR y o hy hO), raw_distrib hd]

/-- Every step of `expandBinOp` that fires is right, where `op` distributes over `op'`. -/
theorem expandBinOp.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op opex : BinOp)
    (hd : distributes op opex = true) (f : Flags) (v other : Term w) (n : Nat)
    (cv : v.Consistent ρ) (co : other.Consistent ρ) (uv : v.hasUndef = false) (uo : other.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ expandBinOp.steps r op v other opex n →
      Refines ((binSrc op f v other).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [expandBinOp.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  split at hmem
  · simp only [reduceCtorEq] at hmem
  · next b0 b1 _ hb =>
    rcases Ans.bind_fire hmem.symm with ⟨-, h⟩ | ⟨l, hl, h⟩
    · cases h
    rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨rr, hrr, h⟩
    · cases h
    split at h
    · next hs =>
      simp only [Step.fire.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact expandBinOp.L218 ρ r hr op opex hd f v other n cv co uv uo hb hl hrr hs
    · rcases Ans.bind_fire h with ⟨-, h⟩ | ⟨s', hs', h⟩
      · cases h
      simp only [Step.fire.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact expandBinOp.fwd218 ρ r hr op opex hd f v other n cv co uv uo hb hl hrr hs'

/-- Every step of `expandCommutativeBinOp` that fires is right, where `op` distributes over `op'`. -/
theorem expandCommutativeBinOp.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op opex : BinOp)
    (hd : distributes op opex = true) (f : Flags) (l rr : Term w) (n : Nat)
    (cl : l.Consistent ρ) (cr : rr.Consistent ρ) (ul : l.hasUndef = false) (ur : rr.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ expandCommutativeBinOp.steps r op l rr opex n →
      Refines ((binSrc op f l rr).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [expandCommutativeBinOp.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact expandBinOp.steps_sound ρ r hr op opex hd f l rr _ cl cr ul ur s res (forward_fire h.symm)
  · rw [binSrc_eval, eval_comm (isCommutative_of_distributes_left hd), ← binSrc_eval]
    exact expandBinOp.steps_sound ρ r hr op opex hd f rr l _ cr cl ur ul s res (forward_fire h.symm)

/-! ## `threadBinOpOverSelect` -/

/-- `SI`: `LHS` if it's a select, else `RHS`, which the callers have checked is; with its condition, its arms, and
whether it's `LHS`. -/
def selectOperand (lhs rhs : Term w) : Option (Term w × Term 1 × Term w × Term w × Bool) :=
  match lhs with
  | .select id c t e => some (.select id c t e, c, t, e, true)
  | _ =>
    match rhs with
    | .select id c t e => some (.select id c t e, c, t, e, false)
    | _ => none

theorem selectOperand_spec {lhs rhs si t e : Term w} {c : Term 1} {onLeft : Bool}
    (h : selectOperand lhs rhs = some (si, c, t, e, onLeft)) :
    (if onLeft then lhs else rhs) = si ∧ ∃ id, si = .select id c t e := by
  unfold selectOperand at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, _, rfl⟩
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, _, rfl⟩
    · cases h

/-- "If one branch simplified and the other did not, and the simplified value is equal to the unsimplified one,
return the simplified value": `S`, with `UB` the arm that didn't simplify. -/
def threadBinOpOverSelect.oneSimplified (op : BinOp) (lhs rhs : Term w) (onLeft : Bool) (s ub : Term w) :
    Step w :=
  -- Check that the simplified value has the form "X op Y" where "op" is the same as the original operation.
  match binop? op s with
  | some (g, s0, s1) =>
    if poisonFlags op g then .next
    else
      -- The value that didn't simplify is "UnsimplifiedLHS op UnsimplifiedRHS".
      if specific (if onLeft then ub else lhs) s0 && specific (if onLeft then rhs else ub) s1 then
        .fire "simplifyBinOp" (.old s)
      else if isCommutative op && specific (if onLeft then ub else lhs) s1 &&
          specific (if onLeft then rhs else ub) s0 then
        .fire "simplifyBinOp" (.old s)
      else .next
  | none => .next

/-- `threadBinOpOverSelect(Opcode, LHS, RHS, Q, MaxRecurse)`, step by step. `TV` and `FV` are the recursive calls on
the select's arms. -/
def threadBinOpOverSelect.steps (r : Recur) (op : BinOp) (lhs rhs : Term w) (maxRecurse : Nat) : List (Step w) :=
  match selectOperand lhs rhs with
  | none => [.decline]
  | some (si, _, t, e, onLeft) =>
    let tv := if onLeft then r.binOp (maxRecurse - 1) op t rhs else r.binOp (maxRecurse - 1) op lhs t
    let fv := if onLeft then r.binOp (maxRecurse - 1) op e rhs else r.binOp (maxRecurse - 1) op lhs e
    [ -- Recursion is always used, so bail out at once if we already hit the limit.
      if maxRecurse == 0 then .decline else .next,
      -- Evaluate the BinOp on the true and false branches of the select.
      match tv, fv with
      | .unknown, _ | _, .unknown => .delegate "simplifyBinOp"
      | _, _ => .next,
      -- If they simplified to the same value, then return the common value.
      -- If they both failed to simplify then return null.
      match tv, fv with
      | .val x, .val y => if specific x y then .fire "simplifyBinOp" (.old x) else .next
      | .null, .null => .decline
      | _, _ => .next,
      -- If one branch simplified to undef, return the other one.
      match tv, fv with
      | .val x, .val y => if isUndefValue x then .fire "simplifyBinOp" (.old y) else .next
      | .val x, .null => if isUndefValue x then .decline else .next
      | _, _ => .next,
      match tv, fv with
      | .val x, .val y => if isUndefValue y then .fire "simplifyBinOp" (.old x) else .next
      | .null, .val y => if isUndefValue y then .decline else .next
      | _, _ => .next,
      -- If applying the operation did not change the true and false select values, then the result of the binop is
      -- the select itself.
      match tv, fv with
      | .val x, .val y =>
        if specific t x && specific e y then .fire "IS.threadBinOpOverSelect.L394" (.old si) else .next
      | _, _ => .next,
      match tv, fv with
      | .val s, .null => threadBinOpOverSelect.oneSimplified op lhs rhs onLeft s e
      | .null, .val s => threadBinOpOverSelect.oneSimplified op lhs rhs onLeft s t
      | _, _ => .next ]


/-- Threading over a select: the source refines `res` if the operation on the arm the select's value is refines it. -/
private theorem thread_src {ρ : Env} {op : BinOp} {f : Flags} {lhs rhs t e : Term w} {c : Term 1} {onLeft : Bool}
    {id : Nat} {res : Val w} (hsi : (if onLeft then lhs else rhs) = .select id c t e)
    (csi : (Term.select id c t e).Consistent ρ)
    (hT : ρ w id = t.denote ρ → Refines (op.eval f (if onLeft then t.denote ρ else lhs.denote ρ)
      (if onLeft then rhs.denote ρ else t.denote ρ)) (Outcome.ok res))
    (hE : ρ w id = e.denote ρ → Refines (op.eval f (if onLeft then e.denote ρ else lhs.denote ρ)
      (if onLeft then rhs.denote ρ else e.denote ρ)) (Outcome.ok res)) :
    Refines (op.eval f (lhs.denote ρ) (rhs.denote ρ)) (Outcome.ok res) := by
  obtain ⟨-, -, -, hsel⟩ := csi
  have hcase := select_cases (c.denote ρ) (t.denote ρ) (e.denote ρ)
  rw [hsel] at hcase
  cases onLeft with
  | true =>
    simp only [ite_true] at hsi hT hE
    subst hsi
    show Refines (op.eval f (ρ w id) (rhs.denote ρ)) (Outcome.ok res)
    rcases hcase with h | h | h
    · rw [h]; exact eval_none_left op f _ _
    · rw [h]; exact hT h
    · rw [h]; exact hE h
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hsi hT hE
    subst hsi
    show Refines (op.eval f (lhs.denote ρ) (ρ w id)) (Outcome.ok res)
    rcases hcase with h | h | h
    · rw [h]; exact eval_none_right op f _ _
    · rw [h]; exact hT h
    · rw [h]; exact hE h

/-- An arm's recursive answer: consistent, with no `undef`, and refined by the operation on the arm. -/
private theorem arm_val {ρ : Env} {r : Recur} (hr : r.Sound ρ) {n : Nat} {op : BinOp} (f : Flags)
    {lhs rhs u x : Term w} {onLeft : Bool} (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) (cu : u.Consistent ρ) (uu : u.hasUndef = false)
    (h : (if onLeft then r.binOp n op u rhs else r.binOp n op lhs u) = .val x) :
    x.Consistent ρ ∧ x.hasUndef = false ∧
      Refines (op.eval f (if onLeft then u.denote ρ else lhs.denote ρ)
        (if onLeft then rhs.denote ρ else u.denote ρ)) (Outcome.ok (x.denote ρ)) := by
  cases onLeft with
  | true =>
    obtain ⟨cx, ux, hx⟩ := hr.binOp n op u rhs x h cu cr uu ur
    exact ⟨cx, ux, Refines.trans (eval_drop_flags op f _ _) hx⟩
  | false =>
    obtain ⟨cx, ux, hx⟩ := hr.binOp n op lhs u x h cl cu ul uu
    exact ⟨cx, ux, Refines.trans (eval_drop_flags op f _ _) hx⟩

/-- The select's parts are consistent and have no `undef`. -/
private theorem select_parts {ρ : Env} {lhs rhs si t e : Term w} {c : Term 1} {onLeft : Bool}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft)) :
    ∃ id, (if onLeft then lhs else rhs) = .select id c t e ∧ (Term.select id c t e).Consistent ρ ∧
      t.Consistent ρ ∧ e.Consistent ρ ∧ t.hasUndef = false ∧ e.hasUndef = false ∧ si = .select id c t e := by
  obtain ⟨hsi, id, rfl⟩ := selectOperand_spec hsel
  have csi : (Term.select id c t e).Consistent ρ := by rw [← hsi]; cases onLeft <;> assumption
  have usi : (Term.select id c t e).hasUndef = false := by rw [← hsi]; cases onLeft <;> assumption
  obtain ⟨-, ct, ce, -⟩ := csi
  simp only [Term.hasUndef, Bool.or_eq_false_iff] at usi
  exact ⟨id, hsi, by rw [← hsi]; cases onLeft <;> assumption, ct, ce, usi.1.2, usi.2, rfl⟩

/-- `IS.threadBinOpOverSelect.L394`: `(select C, T, F) op X` to the select, and `X op (select C, T, F)` likewise,
where the operation on each arm simplifies to the arm. For any opcode and flags. -/
theorem threadBinOpOverSelect.L394 (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e x y : Term w} {c : Term 1} {onLeft : Bool}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (htv : (if onLeft then r.binOp n op t rhs else r.binOp n op lhs t) = .val x)
    (hfv : (if onLeft then r.binOp n op e rhs else r.binOp n op lhs e) = .val y)
    (hs : (specific t x && specific e y) = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old si).eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, rfl⟩ := select_parts cl cr ul ur hsel
  obtain ⟨-, -, hT⟩ := arm_val hr f cl cr ul ur ct ut htv
  obtain ⟨-, -, hE⟩ := arm_val hr f cl cr ul ur ce ue hfv
  simp only [Bool.and_eq_true] at hs
  rw [specific_denote hs.1] at hT
  rw [specific_denote hs.2] at hE
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun h => by show Refines _ (Outcome.ok (ρ w id)); rw [h]; exact hT)
    (fun h => by show Refines _ (Outcome.ok (ρ w id)); rw [h]; exact hE)

/-- `threadBinOpOverSelect`, where both arms simplify to one value: the source to it. -/
theorem threadBinOpOverSelect.fwdSame (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e x y : Term w} {c : Term 1} {onLeft : Bool}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (htv : (if onLeft then r.binOp n op t rhs else r.binOp n op lhs t) = .val x)
    (hfv : (if onLeft then r.binOp n op e rhs else r.binOp n op lhs e) = .val y)
    (hs : specific x y = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, -⟩ := select_parts cl cr ul ur hsel
  obtain ⟨-, -, hT⟩ := arm_val hr f cl cr ul ur ct ut htv
  obtain ⟨-, -, hE⟩ := arm_val hr f cl cr ul ur ce ue hfv
  rw [specific_denote hs] at hE
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun _ => hT) (fun _ => hE)

/-- `threadBinOpOverSelect`, where the true arm simplifies to poison or `undef`: the source to what the false arm
simplifies to. -/
theorem threadBinOpOverSelect.fwdUndefT (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e x y : Term w} {c : Term 1} {onLeft : Bool}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (htv : (if onLeft then r.binOp n op t rhs else r.binOp n op lhs t) = .val x)
    (hfv : (if onLeft then r.binOp n op e rhs else r.binOp n op lhs e) = .val y)
    (hu : isUndefValue x = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old y).eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, -⟩ := select_parts cl cr ul ur hsel
  obtain ⟨-, ux, hT⟩ := arm_val hr f cl cr ul ur ct ut htv
  obtain ⟨-, -, hE⟩ := arm_val hr f cl cr ul ur ce ue hfv
  rw [isUndefValue_denote hu ux] at hT
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun _ => refines_of_refines_ok_none hT _) (fun _ => hE)

/-- `threadBinOpOverSelect`, where the false arm simplifies to poison or `undef`: the source to what the true arm
simplifies to. -/
theorem threadBinOpOverSelect.fwdUndefF (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e x y : Term w} {c : Term 1} {onLeft : Bool}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (htv : (if onLeft then r.binOp n op t rhs else r.binOp n op lhs t) = .val x)
    (hfv : (if onLeft then r.binOp n op e rhs else r.binOp n op lhs e) = .val y)
    (hu : isUndefValue y = true) :
    Refines ((binSrc op f lhs rhs).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, -⟩ := select_parts cl cr ul ur hsel
  obtain ⟨-, -, hT⟩ := arm_val hr f cl cr ul ur ct ut htv
  obtain ⟨-, uy, hE⟩ := arm_val hr f cl cr ul ur ce ue hfv
  rw [isUndefValue_denote hu uy] at hE
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun _ => hT) (fun _ => refines_of_refines_ok_none hE _)

/-- What `oneSimplified` fires: the simplified value, which is the operation, without flags, on the arm that didn't
simplify. -/
private theorem oneSimplified_fire {ρ : Env} {op : BinOp} {lhs rhs s ub : Term w} {onLeft : Bool} {site : String}
    {res : Repl w} (h : threadBinOpOverSelect.oneSimplified op lhs rhs onLeft s ub = .fire site res)
    (cs : s.Consistent ρ) :
    res = .old s ∧ op.eval {} (if onLeft then ub.denote ρ else lhs.denote ρ)
      (if onLeft then rhs.denote ρ else ub.denote ρ) = Outcome.ok (s.denote ρ) := by
  unfold threadBinOpOverSelect.oneSimplified at h
  have dl : (if onLeft then ub.denote ρ else lhs.denote ρ) = (if onLeft then ub else lhs).denote ρ := by
    cases onLeft <;> rfl
  have dr : (if onLeft then rhs.denote ρ else ub.denote ρ) = (if onLeft then rhs else ub).denote ρ := by
    cases onLeft <;> rfl
  rw [dl, dr]
  generalize (if onLeft then ub else lhs) = ul at h ⊢
  generalize (if onLeft then rhs else ub) = ur at h ⊢
  split at h
  · next g s0 s1 hb =>
    have hv := binop?_eval hb cs
    by_cases hp : poisonFlags op g = true
    · simp [hp] at h
    · simp only [hp, Bool.false_eq_true, ite_false] at h
      simp only [Bool.not_eq_true] at hp
      rw [eval_of_poisonFlags hp] at hv
      by_cases hm : (specific ul s0 && specific ur s1) = true
      · simp only [hm, ite_true, Step.fire.injEq] at h
        simp only [Bool.and_eq_true] at hm
        rw [specific_denote hm.1, specific_denote hm.2] at hv
        exact ⟨h.2.symm, hv⟩
      · simp only [hm, Bool.false_eq_true, ite_false] at h
        by_cases hm' : (isCommutative op && specific ul s1 && specific ur s0) = true
        · simp only [hm', ite_true, Step.fire.injEq] at h
          simp only [Bool.and_eq_true] at hm'
          rw [specific_denote hm'.1.2, specific_denote hm'.2, eval_comm hm'.1.1] at hv
          exact ⟨h.2.symm, hv⟩
        · simp [hm'] at h
  · cases h

/-- `threadBinOpOverSelect`, where the true arm simplifies to `S`, the false arm doesn't, and `S` is the operation on
the false arm: the source to `S`. -/
theorem threadBinOpOverSelect.fwdOneT (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e s : Term w} {c : Term 1} {onLeft : Bool} {site : String} {res : Repl w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (htv : (if onLeft then r.binOp n op t rhs else r.binOp n op lhs t) = .val s)
    (h : threadBinOpOverSelect.oneSimplified op lhs rhs onLeft s e = .fire site res) :
    Refines ((binSrc op f lhs rhs).eval ρ) (res.eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, -⟩ := select_parts cl cr ul ur hsel
  obtain ⟨cs, -, hT⟩ := arm_val hr f cl cr ul ur ct ut htv
  obtain ⟨rfl, hv⟩ := oneSimplified_fire h cs
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun _ => hT) (fun _ => by rw [← hv]; exact eval_drop_flags op f _ _)

/-- `threadBinOpOverSelect`, where the false arm simplifies to `S`, the true arm doesn't, and `S` is the operation on
the true arm: the source to `S`. -/
theorem threadBinOpOverSelect.fwdOneF (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat) {si t e s : Term w} {c : Term 1} {onLeft : Bool} {site : String} {res : Repl w}
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false)
    (hsel : selectOperand lhs rhs = some (si, c, t, e, onLeft))
    (hfv : (if onLeft then r.binOp n op e rhs else r.binOp n op lhs e) = .val s)
    (h : threadBinOpOverSelect.oneSimplified op lhs rhs onLeft s t = .fire site res) :
    Refines ((binSrc op f lhs rhs).eval ρ) (res.eval ρ) := by
  obtain ⟨id, hsi, csi, ct, ce, ut, ue, -⟩ := select_parts cl cr ul ur hsel
  obtain ⟨cs, -, hE⟩ := arm_val hr f cl cr ul ur ce ue hfv
  obtain ⟨rfl, hv⟩ := oneSimplified_fire h cs
  rw [binSrc_eval, Repl.eval_old]
  exact thread_src hsi csi (fun _ => by rw [← hv]; exact eval_drop_flags op f _ _) (fun _ => hE)

/-- Every step of `threadBinOpOverSelect` that fires is right, for any opcode and flags. -/
theorem threadBinOpOverSelect.steps_sound (ρ : Env) (r : Recur) (hr : r.Sound ρ) (op : BinOp) (f : Flags)
    (lhs rhs : Term w) (n : Nat)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ threadBinOpOverSelect.steps r op lhs rhs n →
      Refines ((binSrc op f lhs rhs).eval ρ) (res.eval ρ) := by
  intro s res hmem
  unfold threadBinOpOverSelect.steps at hmem
  split at hmem
  · simp at hmem
  · next si c t e onLeft hsel =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    generalize htv : (if onLeft then r.binOp (n - 1) op t rhs else r.binOp (n - 1) op lhs t) = tv at hmem
    generalize hfv : (if onLeft then r.binOp (n - 1) op e rhs else r.binOp (n - 1) op lhs e) = fv at hmem
    rcases hmem with h | h | h | h | h | h | h
    · split at h <;> simp only [reduceCtorEq] at h
    · split at h <;> simp only [reduceCtorEq] at h
    · split at h
      · next x y =>
        split at h
        · next hs =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact threadBinOpOverSelect.fwdSame ρ r hr op f lhs rhs _ cl cr ul ur hsel htv hfv hs
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · split at h
      · next x y =>
        split at h
        · next hu =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact threadBinOpOverSelect.fwdUndefT ρ r hr op f lhs rhs _ cl cr ul ur hsel htv hfv hu
        · simp only [reduceCtorEq] at h
      · split at h <;> simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · split at h
      · next x y =>
        split at h
        · next hu =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact threadBinOpOverSelect.fwdUndefF ρ r hr op f lhs rhs _ cl cr ul ur hsel htv hfv hu
        · simp only [reduceCtorEq] at h
      · split at h <;> simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · split at h
      · next x y =>
        split at h
        · next hs =>
          simp only [Step.fire.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact threadBinOpOverSelect.L394 ρ r hr op f lhs rhs _ cl cr ul ur hsel htv hfv hs
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · split at h
      · exact threadBinOpOverSelect.fwdOneT ρ r hr op f lhs rhs _ cl cr ul ur hsel htv h.symm
      · exact threadBinOpOverSelect.fwdOneF ρ r hr op f lhs rhs _ cl cr ul ur hsel hfv h.symm
      · simp only [reduceCtorEq] at h

end Peephole.IS
