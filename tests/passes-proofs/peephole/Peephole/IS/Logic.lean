import Peephole.Match
import Peephole.Oracle
import Peephole.Fold
import Peephole.IS.Add
import Peephole.Lemmas.Add
import Peephole.Lemmas.Logic

/-! # InstSimplify's bitwise folds: what they share

`simplifyAndInst`, `simplifyOrInst` and `simplifyXorInst`, at `llvm/lib/Analysis/InstructionSimplify.cpp:2071-2607`
at `llvmorg-23.1.3`, share helpers. This module holds what they need of them, and the two helpers with rewrites of
their own that more than one of them calls:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyLogicOfAddSub.L2011` | `(X + C) op (~C - X)` to 0 for `and`, -1 for `or` and `xor` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1965` | `and (icmp eq a, b), x` to false where `x` is false when `a == b`, and `or (icmp ne a, b), x` to true where `x` is true when `a == b` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1967` | the same, to the `icmp`, where `x` is the operation's identity when `a == b` |
| `IS.simplifyAndOrWithICmpEq.Simplify.L1975` | `and (icmp ne a, b), x` to `x` where `x` is false when `a == b`, and `or (icmp eq a, b), x` to `x` where `x` is true when `a == b` |

The matchers of `PatternMatch.h` that the bitwise folds use and `Peephole.Match` doesn't have are here too, in
`Peephole.IS.Logic`: the commutative ones that bind, and what each match says about values.

## What the core `Oracle` doesn't answer

Three calls in these folds ask what the core `Oracle` doesn't have. `Logic.Ext` answers them:

- `isImpliedCondition(A, B, DL, /*LHSIsTrue=*/false)`, which `simplifyOrInst` asks. Its answers are an analysis's,
  true in the run when `Logic.Ext.Sound.impliesFalse` holds, which is PASS-01's to prove, as `Oracle.Sound` is.
- `simplifyWithOpReplaced(V, Op, RepOp, Q.getWithoutUndef(), /*AllowRefinement=*/true, nullptr, MaxRecurse)`, a
  recursive call into InstSimplify, which `simplifyAndOrWithICmpEq` makes. Its answer refines `V` wherever `Op` and
  `RepOp` are the same value: `Logic.Ext.Sound.replaced`, the recursive simplifier's soundness, which the theorems that
  rest on it name.
- `isImpliedByDomCondition(ICMP_EQ, Op0, Op1, ...)`, which `simplifyByDomEq` asks. `simplifyByDomEq` isn't modelled
  here, so the answer only says when the model hands over to it, and claims nothing.

A fold takes `Option Logic.Ext`. With `none`, as `onInst` has it, the model hands over (`.delegate`) at each of these
calls, so it claims nothing there. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

namespace Logic

/-! ### What the core `Oracle` doesn't answer -/

/-- Answers to what the bitwise folds ask that the core `Oracle` doesn't have. -/
structure Ext where
  /-- `isImpliedCondition(A, B, DL, /*LHSIsTrue=*/false)`: `some true` if `B` is true whenever `A` is false,
  `some false` if `B` is false whenever `A` is false. -/
  impliesFalse : Term 1 → Term 1 → Option Bool
  /-- `isImpliedByDomCondition(ICMP_EQ, A, B, CxtI, DL)`: `some true` if a condition dominating the instruction says
  `A == B`. -/
  domEq : {w : Nat} → Term w → Term w → Option Bool
  /-- `simplifyWithOpReplaced(V, Op, RepOp, Q.getWithoutUndef(), /*AllowRefinement=*/true, nullptr, MaxRecurse)`: `V`
  simplified with `Op` replaced by `RepOp`, if it simplifies. -/
  replaced : Nat → {u v : Nat} → Term u → Term v → Term v → Option (Term u)

/-- `e`'s answers are true in the run `ρ`: the analysis's, and the recursive simplifier's. -/
structure Ext.Sound (e : Ext) (ρ : Env) : Prop where
  /-- `isImpliedCondition` with `LHSIsTrue` false is sound: PASS-01's. -/
  impliesFalse : ∀ (a b : Term 1) (r : Bool), e.impliesFalse a b = some r → a.denote ρ = some 0#1 →
    b.denote ρ = none ∨ b.denote ρ = some (BitVec.ofBool r)
  /-- `simplifyWithOpReplaced` with `AllowRefinement` is sound: where `Op` and `RepOp` are the same value, what it
  answers refines `V`. -/
  replaced : ∀ (n : Nat) {u v : Nat} (V r : Term u) (a b : Term v) (x : BitVec v),
    e.replaced n V a b = some r → a.denote ρ = some x → b.denote ρ = some x → Refines (V.denote ρ) (r.denote ρ)

/-! ### Calls to other folds -/

/-- `if (Value *V = callee(...)) return V;`, for a callee modelled here as `steps`: what it answers, under the site
that answered, or the next step if it answers `nullptr`. -/
def forward (steps : List (Step w)) : Step w :=
  match run steps with
  | .value r => .fire ((firedSite steps).getD "") r
  | .null => .next
  | .delegated c => .delegate c

/-- `return callee(...);`: as `forward`, but `nullptr` ends the caller too. -/
def tail (steps : List (Step w)) : Step w :=
  match run steps with
  | .value r => .fire ((firedSite steps).getD "") r
  | .null => .decline
  | .delegated c => .delegate c

theorem run_of_forward {steps : List (Step w)} {s : String} {r : Repl w} (h : forward steps = .fire s r) :
    run steps = .value r := by
  unfold forward at h
  split at h <;> simp_all

theorem run_of_tail {steps : List (Step w)} {s : String} {r : Repl w} (h : tail steps = .fire s r) :
    run steps = .value r := by
  unfold tail at h
  split at h <;> simp_all

/-! ### Matchers -/

/-- Whether a binary operator has opcode `op`: `isa<BinaryOperator>` and `getOpcode() == op`. -/
def isBin (op : BinOp) (t : Term w) : Bool := (binop? op t).isSome

/-- `m_c_<Op>(L, R)`, where `L` and `R` test their operand: operand 0 for `L` and operand 1 for `R`, or the other way
round. -/
def chas (op : BinOp) (l r : Term w → Bool) (t : Term w) : Bool :=
  match binop? op t with
  | some (_, a, b) => (l a && r b) || (l b && r a)
  | none => false

/-- `m_c_<Op>(L, R)`, where `L` and `R` bind: operand 0 for `L` and operand 1 for `R`, else the other way round, and
what they bound in the first order that matches. -/
def cbind {α β : Type} (op : BinOp) (l : Term w → Option α) (r : Term w → Option β) (t : Term w) :
    Option (α × β) :=
  match binop? op t with
  | some (_, a, b) =>
    match l a, r b with
    | some x, some y => some (x, y)
    | _, _ =>
      match l b, r a with
      | some x, some y => some (x, y)
      | _, _ => none
  | none => none

/-- `m_Not(L)`, `m_c_Xor(m_AllOnes(), L)`, where `L` binds: operand 1 for `L` if operand 0 is all ones, else operand
0 if operand 1 is. -/
def notBind {α : Type} (l : Term w → Option α) (t : Term w) : Option α :=
  match binop? .xor t with
  | some (_, a, b) =>
    match (if allOnes a then l b else none) with
    | some x => some x
    | none => if allOnes b then l a else none
  | none => none

/-- `m_<Op>(m_Value(A), m_Value(B))`, not commutative. -/
def ops? (op : BinOp) (t : Term w) : Option (Term w × Term w) :=
  (binop? op t).map fun (_, a, b) => (a, b)

/-- `m_c_<Op>(m_Specific(A), m_Specific(B))`. -/
def isOf (op : BinOp) (a b t : Term w) : Bool := chas op (specific a) (specific b) t

/-- `m_c_Xor(m_Not(m_Value(A)), m_Value(B))` and the like: an operand that's a `not`, binding what it negates, and
the other operand. -/
def notAnd (op : BinOp) (t : Term w) : Option (Term w × Term w) := cbind op not? some t

/-- `m_c_<Op>(m_CombineAnd(m_Value(NotA), m_Not(m_Value(A))), m_Value(B))`: as `notAnd`, also binding the `not`. -/
def notAnd' (op : BinOp) (t : Term w) : Option ((Term w × Term w) × Term w) :=
  cbind op (fun u => (not? u).map fun a => (u, a)) some t

/-- `m_ICmpLike(Pred, m_Value(A), m_Value(B))` with `ICmpInst::isEquality(Pred)`: an `icmp eq` or `icmp ne`, or
`trunc nuw X to i1`, which is `icmp ne X, 0`. Whether the predicate is `eq`, and `A` and `B`, at their width. -/
def icmpEq? : {w : Nat} → Term w → Option (Bool × ((v : Nat) × Term v × Term v))
  | _, .icmp _ .eq _ a b => some (true, ⟨_, a, b⟩)
  | _, .icmp _ .ne _ a b => some (false, ⟨_, a, b⟩)
  | w, .trunc (v := v) _ nuw _ a => if nuw && w == 1 then some (false, ⟨v, a, .const 0#v⟩) else none
  | _, _ => none

/-- `APInt::isMask()`: a nonzero mask of low bits, `0+1+`. -/
def isMask (c : BitVec w) : Bool := c != 0#w && c &&& (c + 1#w) == 0#w

/-! ### What a match says about values -/

variable {ρ : Env}

theorem isMask_spec {c : BitVec w} (h : isMask c = true) : c &&& (c + 1#w) = 0#w := by
  simp only [isMask, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact h.2

/-- A matched `and`, `or` or `xor`'s value and operands. -/
theorem and_denote {t a b : Term w} {f : Flags} (h : binop? .and t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem or_denote {t a b : Term w} {f : Flags} (h : binop? .or t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) f.disjoint := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem xor_denote' {t a b : Term w} {f : Flags} (h : binop? .xor t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem add_denote {t a b : Term w} {f : Flags} (h : binop? .add t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.add (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem sub_denote' {t a b : Term w} {f : Flags} (h : binop? .sub t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.sub (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem shl_denote {t a b : Term w} {f : Flags} (h : binop? .shl t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.shl (a.denote ρ) (b.denote ρ) f.nuw f.nsw := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

theorem lshr_denote {t a b : Term w} {f : Flags} (h : binop? .lshr t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = Val.lshr (a.denote ρ) (b.denote ρ) f.exact := by
  obtain ⟨h1, h2, h3⟩ := binop?_consistent h hc
  exact ⟨h1, h2, (ok_inj h3).symm⟩

/-- `m_Not(m_Value(A))`'s value, as `xor A, -1`, whichever operand the `-1` was. -/
theorem not?_denote {t a : Term w} (h : not? t = some a) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold not? at h
  split at h
  · next f p q hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    split at h
    · next h1 => cases h; exact ⟨hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
    · split at h
      · next _ h2 => cases h; exact ⟨hp, by rw [hd, cst_eq h2]⟩
      · cases h
  · cases h

/-- `m_Not(P)`'s value, as `xor A, -1`, for the `A` that matches `P`. -/
theorem notWith_denote {p : Term w → Bool} {t : Term w} (h : notWith p t = true) (hc : t.Consistent ρ) :
    ∃ a, p a = true ∧ a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold notWith at h
  split at h
  · next f x y hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨y, h2, hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
    · exact ⟨x, h2, hp, by rw [hd, cst_eq h1]⟩
  · cases h

theorem notBind_denote {α : Type} {l : Term w → Option α} {t : Term w} {x : α} (h : notBind l t = some x)
    (hc : t.Consistent ρ) :
    ∃ a, l a = some x ∧ a.Consistent ρ ∧ t.denote ρ = Val.xor (a.denote ρ) (some (BitVec.allOnes w)) := by
  unfold notBind at h
  split at h
  · next f p q hx =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hx hc
    split at h
    · next y hy =>
      cases h
      split at hy
      · next h1 => exact ⟨q, hy, hq, by rw [hd, cst_eq h1, Lemmas.Logic.xor_comm]⟩
      · cases hy
    · split at h
      · next h2 => exact ⟨p, h, hp, by rw [hd, cst_eq h2]⟩
      · cases h
  · cases h

/-- What a commutative matcher on `and` bound, with the operands in the matcher's order. -/
theorem cbind_and {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .and l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := and_denote hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.and_comm]⟩
      · cases h
  · cases h

theorem cbind_or {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .or l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b d, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := or_denote hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, _, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, _, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.or_comm]⟩
      · cases h
  · cases h

theorem cbind_xor {α β : Type} {l : Term w → Option α} {r : Term w → Option β} {t : Term w} {x : α} {y : β}
    (h : cbind .xor l r t = some (x, y)) (hc : t.Consistent ρ) :
    ∃ a b, l a = some x ∧ r b = some y ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  unfold cbind at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hb hc
    split at h
    · next x' y' h1 h2 => cases h; exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · split at h
      · next x' y' h1 h2 =>
        cases h; exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.xor_comm]⟩
      · cases h
  · cases h

/-- What a commutative matcher on `and` tested, with the operands in the matcher's order. -/
theorem chas_and {l r : Term w → Bool} {t : Term w} (h : chas .and l r t = true) (hc : t.Consistent ρ) :
    ∃ a b, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := and_denote hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.and_comm]⟩
  · cases h

theorem chas_or {l r : Term w → Bool} {t : Term w} (h : chas .or l r t = true) (hc : t.Consistent ρ) :
    ∃ a b d, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := or_denote hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, _, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, _, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.or_comm]⟩
  · cases h

theorem chas_xor {l r : Term w → Bool} {t : Term w} (h : chas .xor l r t = true) (hc : t.Consistent ρ) :
    ∃ a b, l a = true ∧ r b = true ∧ a.Consistent ρ ∧ b.Consistent ρ ∧
      t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  unfold chas at h
  split at h
  · next f p q hb =>
    obtain ⟨hp, hq, hd⟩ := xor_denote' hb hc
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, q, h1, h2, hp, hq, hd⟩
    · exact ⟨q, p, h1, h2, hq, hp, by rw [hd, Lemmas.Logic.xor_comm]⟩
  · cases h

/-- `m_c_And(m_Specific(A), m_Specific(B))` and the like: the operands' values are `A`'s and `B`'s. -/
theorem isOf_and {a b t : Term w} (h : isOf .and a b t = true) (hc : t.Consistent ρ) :
    t.denote ρ = Val.and (a.denote ρ) (b.denote ρ) := by
  obtain ⟨p, q, h1, h2, -, -, hd⟩ := chas_and h hc
  rw [hd, specific_denote h1, specific_denote h2]

theorem isOf_or {a b t : Term w} (h : isOf .or a b t = true) (hc : t.Consistent ρ) :
    ∃ d, t.denote ρ = Val.or (a.denote ρ) (b.denote ρ) d := by
  obtain ⟨p, q, d, h1, h2, -, -, hd⟩ := chas_or h hc
  exact ⟨d, by rw [hd, specific_denote h1, specific_denote h2]⟩

theorem isOf_xor {a b t : Term w} (h : isOf .xor a b t = true) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (a.denote ρ) (b.denote ρ) := by
  obtain ⟨p, q, h1, h2, -, -, hd⟩ := chas_xor h hc
  rw [hd, specific_denote h1, specific_denote h2]

end Logic

open Logic

/-! ### The instructions the folds replace -/

/-- The `and` a fold replaces. -/
def andSrc (op0 op1 : Term w) : Repl w := .bin .and {} (.old op0) (.old op1)

/-- The `or` a fold replaces, with its `disjoint` flag. -/
def orSrc (op0 op1 : Term w) (disjoint : Bool) : Repl w := .bin .or { disjoint := disjoint } (.old op0) (.old op1)

/-- The `xor` a fold replaces. -/
def xorSrc (op0 op1 : Term w) : Repl w := .bin .xor {} (.old op0) (.old op1)

theorem andSrc_eval (ρ : Env) (op0 op1 : Term w) :
    (andSrc op0 op1).eval ρ = Outcome.ok (Val.and (op0.denote ρ) (op1.denote ρ)) := rfl

theorem orSrc_eval (ρ : Env) (op0 op1 : Term w) (d : Bool) :
    (orSrc op0 op1 d).eval ρ = Outcome.ok (Val.or (op0.denote ρ) (op1.denote ρ) d) := rfl

theorem xorSrc_eval (ρ : Env) (op0 op1 : Term w) :
    (xorSrc op0 op1).eval ρ = Outcome.ok (Val.xor (op0.denote ρ) (op1.denote ρ)) := rfl

theorem andSrc_comm (ρ : Env) (op0 op1 : Term w) : (andSrc op0 op1).eval ρ = (andSrc op1 op0).eval ρ := by
  rw [andSrc_eval, andSrc_eval, Lemmas.Logic.and_comm]

theorem orSrc_comm (ρ : Env) (op0 op1 : Term w) (d : Bool) : (orSrc op0 op1 d).eval ρ = (orSrc op1 op0 d).eval ρ := by
  rw [orSrc_eval, orSrc_eval, Lemmas.Logic.or_comm]

theorem xorSrc_comm (ρ : Env) (op0 op1 : Term w) : (xorSrc op0 op1).eval ρ = (xorSrc op1 op0).eval ρ := by
  rw [xorSrc_eval, xorSrc_eval, Lemmas.Logic.xor_comm]

/-- The bitwise operation a fold replaces: `and`, `or disjoint` or `xor`. -/
def logicSrc (opc : BinOp) (disjoint : Bool) (op0 op1 : Term w) : Repl w :=
  .bin opc { disjoint := disjoint } (.old op0) (.old op1)

/-! ## `simplifyLogicOfAddSub` -/

/-- `m_Add(m_Value(X), m_Constant(C1))` on `A` and `m_Sub(m_Constant(C2), m_Specific(X))` on `S`: `X`, `C1` and
`C2`. -/
def addSubPair (a s : Term w) : Option (Term w × Term w × Term w) :=
  match binop? .add a with
  | some (_, x, c1) =>
    if c1.isConstant then
      match binop? .sub s with
      | some (_, c2, x') => if c2.isConstant && specific x x' then some (x, c1, c2) else none
      | none => none
    else none
  | none => none

/-- `ConstantExpr::getNot(C)` on a constant: `~C` for a `ConstantInt`, and poison and `undef` for themselves, as the
constant folder has `xor`. -/
def notConst : Term w → Option (Term w)
  | .const c => some (.const (~~~c))
  | .poison => some .poison
  | .undef => some .undef
  | _ => none

/-- The `add` and the `sub` `simplifyLogicOfAddSub` matched, either way round. -/
def addSubPairs (op0 op1 : Term w) : Option (Term w × Term w × Term w) :=
  match addSubPair op0 op1 with
  | some p => some p
  | none => addSubPair op1 op0

/-- `simplifyLogicOfAddSub(Op0, Op1, Opcode)`, step by step: the `add` and `sub` either way round, then whether
`~C1 == C2`, by address, as LLVM uniques constants. -/
def simplifyLogicOfAddSub.steps (op0 op1 : Term w) (opc : BinOp) : List (Step w) :=
  [ match addSubPairs op0 op1 with
    | some (_, c1, c2) =>
      match notConst c1 with
      | some nc1 =>
        -- (X + C) & (~C - X) --> (X + C) & ~(X + C) --> 0
        -- (X + C) | (~C - X) --> (X + C) | ~(X + C) --> -1
        -- (X + C) ^ (~C - X) --> (X + C) ^ ~(X + C) --> -1
        if nc1.ident == c2.ident then
          .fire "IS.simplifyLogicOfAddSub.L2011"
            (if opc == .and then .const 0#w else .const (BitVec.allOnes w))
        else .next
      | none => .next
    | none => .next ]

theorem addSubPair_denote {ρ : Env} {a s x c1 c2 : Term w} (h : addSubPair a s = some (x, c1, c2))
    (ca : a.Consistent ρ) (cs : s.Consistent ρ) (us : s.hasUndef = false) :
    c2.hasUndef = false ∧ ∃ f1 f2 f3 f4, a.denote ρ = Val.add (x.denote ρ) (c1.denote ρ) f1 f2 ∧
      s.denote ρ = Val.sub (c2.denote ρ) (x.denote ρ) f3 f4 := by
  unfold addSubPair at h
  split at h
  · next f x' c1' ha =>
    split at h
    · split at h
      · next f' c2' x'' hs =>
        split at h
        · next hh =>
          cases h
          simp only [Bool.and_eq_true] at hh
          obtain ⟨-, -, hda⟩ := add_denote ha ca
          obtain ⟨-, -, hds⟩ := sub_denote' hs cs
          exact ⟨(binop?_noUndef hs us).1, _, _, _, _, hda, by rw [hds, specific_denote hh.2]⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- What `notConst` says, with no `undef`: poison for poison, `~k` for `k`. -/
theorem notConst_denote {ρ : Env} {c d e : Term w} (h : notConst c = some d) (hid : d.ident = e.ident)
    (hu : e.hasUndef = false) :
    (c.denote ρ = none ∧ e.denote ρ = none) ∨ ∃ k, c.denote ρ = some k ∧ e.denote ρ = some (~~~k) := by
  cases c <;> simp only [notConst, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · next k => exact .inr ⟨k, rfl, by rw [← Term.denote_of_ident hid]; rfl⟩
  · exact .inl ⟨rfl, by rw [← Term.denote_of_ident hid]; rfl⟩
  · cases e <;> simp_all [Term.ident, Term.hasUndef]

/-- `IS.simplifyLogicOfAddSub.L2011`: `(X + C) op (~C - X)`, either way round, to 0 for `and` and -1 for `or` and
`xor`. `C` may be poison, which makes both poison. -/
theorem simplifyLogicOfAddSub.L2011 (ρ : Env) (opc : BinOp) (d : Bool) (op0 op1 x c1 c2 nc1 : Term w)
    (c0 : op0.Consistent ρ) (c1' : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (hopc : opc = .and ∨ opc = .or ∨ opc = .xor) (hp : addSubPairs op0 op1 = some (x, c1, c2))
    (hn : notConst c1 = some nc1) (hid : nc1.ident = c2.ident) :
    Refines ((logicSrc opc d op0 op1).eval ρ)
      ((if opc == .and then Repl.const 0#w else .const (BitVec.allOnes w)).eval ρ) := by
  -- The values of the two operands, as `add` then `sub`.
  have key : ∃ A S, (Val.and (op0.denote ρ) (op1.denote ρ) = Val.and A S ∧
      Val.or (op0.denote ρ) (op1.denote ρ) d = Val.or A S d ∧ Val.xor (op0.denote ρ) (op1.denote ρ) = Val.xor A S) ∧
      ∃ f1 f2 f3 f4, A = Val.add (x.denote ρ) (c1.denote ρ) f1 f2 ∧ S = Val.sub (c2.denote ρ) (x.denote ρ) f3 f4 ∧
        c2.hasUndef = false := by
    unfold addSubPairs at hp
    split at hp
    · next p hp' =>
      cases hp
      obtain ⟨hu, f1, f2, f3, f4, ha, hs⟩ := addSubPair_denote hp' c0 c1' u1
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, f1, f2, f3, f4, ha, hs, hu⟩
    · obtain ⟨hu, f1, f2, f3, f4, ha, hs⟩ := addSubPair_denote hp c1' c0 u0
      exact ⟨_, _, ⟨Lemmas.Logic.and_comm _ _, Lemmas.Logic.or_comm _ _ _, Lemmas.Logic.xor_comm _ _⟩,
        f1, f2, f3, f4, ha, hs, hu⟩
  obtain ⟨A, S, ⟨hand, hor, hxor⟩, f1, f2, f3, f4, rfl, rfl, hu⟩ := key
  rcases hopc with rfl | rfl | rfl
  · show Refines (Outcome.ok (Val.and (op0.denote ρ) (op1.denote ρ))) (Outcome.ok (some 0#w))
    refine refines_ok ?_
    rw [hand]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.and_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.and_add_sub_not_refines _ _ _ _ _ _
  · show Refines (Outcome.ok (Val.or (op0.denote ρ) (op1.denote ρ) d)) (Outcome.ok (some (BitVec.allOnes w)))
    refine refines_ok ?_
    rw [hor]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.or_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.or_add_sub_not_refines _ _ _ _ _ _ _
  · show Refines (Outcome.ok (Val.xor (op0.denote ρ) (op1.denote ρ))) (Outcome.ok (some (BitVec.allOnes w)))
    refine refines_ok ?_
    rw [hxor]
    rcases notConst_denote hn hid hu with ⟨h1, -⟩ | ⟨k, h1, h2⟩
    · rw [h1, Lemmas.add_none_right, Lemmas.Logic.xor_none_left]; exact Refine.val_none _
    · rw [h1, h2]; exact Lemmas.xor_add_sub_not_refines _ _ _ _ _ _

/-- Theorem 1 for `simplifyLogicOfAddSub`: what it returns refines the `and`, `or` or `xor` it's called on. -/
theorem simplifyLogicOfAddSub.sound (ρ : Env) (opc : BinOp) (d : Bool) (op0 op1 : Term w)
    (cs0 : op0.Consistent ρ) (cs1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (hopc : opc = .and ∨ opc = .or ∨ opc = .xor) {r : Repl w}
    (h : run (simplifyLogicOfAddSub.steps op0 op1 opc) = .value r) :
    Refines ((logicSrc opc d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((logicSrc opc d op0 op1).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyLogicOfAddSub.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  split at hmem
  · next x c1 c2 hp =>
    split at hmem
    · next nc1 hn =>
      split at hmem
      · next hid =>
        simp only [Step.fire.injEq] at hmem
        obtain ⟨-, rfl⟩ := hmem
        exact simplifyLogicOfAddSub.L2011 ρ opc d op0 op1 x c1 c2 nc1 cs0 cs1 u0 u1 hopc hp hn
          (by simpa using hid)
      · simp at hmem
    · simp at hmem
  · simp at hmem

/-! ## `simplifyAndOrWithICmpEq` -/

/-- `ConstantExpr::getBinOpAbsorber(Opcode, Ty)`: 0 for `and`, -1 for `or`. -/
def absorber (isAnd : Bool) : BitVec w := if isAnd then 0#w else BitVec.allOnes w

/-- `ConstantExpr::getBinOpIdentity(Opcode, Ty)`: -1 for `and`, 0 for `or`. -/
def identity (isAnd : Bool) : BitVec w := if isAnd then BitVec.allOnes w else 0#w

/-- The `and` or `or` `simplifyAndOrWithICmpEq` is called on. -/
def andOrSrc (isAnd d : Bool) (op0 op1 : Term w) : Repl w := if isAnd then andSrc op0 op1 else orSrc op0 op1 d

/-- The lambda `Simplify` in `simplifyAndOrWithICmpEq`, on what `simplifyWithOpReplaced` answered, `Res`, step by
step. `isEq` is whether the predicate is `eq`. -/
def simplifyAndOrWithICmpEq.Simplify.steps (isAnd isEq : Bool) (op0 op1 res : Term w) : List (Step w) :=
  [ -- and (icmp eq a, b), x implies (a==b) inside x.
    -- or (icmp ne a, b), x implies (a==b) inside x.
    -- If x simplifies to true/false, we can simplify the and/or.
    if isEq == isAnd && res.ident == (Term.const (absorber isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1965" (.const (absorber isAnd))
    else .next,
    if isEq == isAnd && res.ident == (Term.const (identity isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1967" (.old op0)
    else .next,
    if isEq == isAnd then .decline else .next,
    -- If we have and (icmp ne a, b), x and for a==b we can simplify x to false,
    -- then we can drop the icmp, as x will already be false in the case where
    -- the icmp is false. Similar for or and true.
    if res.ident == (Term.const (absorber isAnd : BitVec w)).ident then
      .fire "IS.simplifyAndOrWithICmpEq.Simplify.L1975" (.old op1)
    else .next ]

/-- `if (Value *Res = simplifyWithOpReplaced(Op1, A, B, ...)) return Simplify(Res);`, or with `B` replaced by `A`
if `swap`. With no `Ext`, the model hands over to `simplifyWithOpReplaced`, which it doesn't follow. -/
def simplifyAndOrWithICmpEq.replacedStep (x : Option Ext) (isAnd swap : Bool) (op0 op1 : Term w) (n : Nat) :
    Step w :=
  match icmpEq? op0 with
  | none => .next
  | some (isEq, p) =>
    match x with
    | none => .delegate "simplifyWithOpReplaced"
    | some e =>
      match (if swap then e.replaced n op1 p.2.2 p.2.1 else e.replaced n op1 p.2.1 p.2.2) with
      | some res => tail (simplifyAndOrWithICmpEq.Simplify.steps isAnd isEq op0 op1 res)
      | none => .next

/-- `simplifyAndOrWithICmpEq(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step, `isAnd` for `and`. -/
def simplifyAndOrWithICmpEq.steps (x : Option Ext) (isAnd : Bool) (op0 op1 : Term w) (n : Nat) : List (Step w) :=
  [ -- `match(Op0, m_ICmpLike(Pred, m_Value(A), m_Value(B)))` and `ICmpInst::isEquality(Pred)`, or return nullptr.
    if (icmpEq? op0).isNone then .decline else .next,
    -- In the final case (Res == Absorber with inverted predicate), it is safe to
    -- refine poison during simplification, but not undef. For simplicity always
    -- disable undef-based folds here.
    simplifyAndOrWithICmpEq.replacedStep x isAnd false op0 op1 n,
    simplifyAndOrWithICmpEq.replacedStep x isAnd true op0 op1 n ]

theorem icmpEq_true {v : Nat} {a b : Val v} {s : Bool} {c : BitVec 1} (h : Val.icmpEq a b s = some c)
    (hc : c = BitVec.allOnes 1) : ∃ x, a = some x ∧ b = some x := by
  subst hc
  cases a with
  | none => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      refine ⟨x, rfl, ?_⟩
      simp only [Val.icmpEq, Val.icmp] at h
      split at h
      · cases h
      · by_cases hxy : x = y
        · rw [hxy]
        · simp [hxy] at h

theorem icmpNe_false {v : Nat} {a b : Val v} {s : Bool} {c : BitVec 1} (h : Val.icmpNe a b s = some c)
    (hc : c = 0#1) : ∃ x, a = some x ∧ b = some x := by
  subst hc
  cases a with
  | none => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      refine ⟨x, rfl, ?_⟩
      simp only [Val.icmpNe, Val.icmp] at h
      split at h
      · cases h
      · by_cases hxy : x = y
        · rw [hxy]
        · simp [hxy] at h

theorem trunc_nuw_false {v : Nat} {a : Val v} {nsw : Bool} (h : Val.trunc 1 a true nsw = some 0#1) :
    a = some 0#v := by
  cases a with
  | none => cases h
  | some x =>
    simp only [Val.trunc, Bool.true_and] at h
    split at h
    · cases h
    · next h1 =>
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
        rw [← h1, h]
        simp

/-- What a match of `m_ICmpLike` with an equality predicate says: the operation is on `i1`, and where the `icmp` is
true for `eq`, or false for `ne`, `A` and `B` are the same value. -/
theorem icmpEq?_spec {ρ : Env} {op0 : Term w} {isEq : Bool} {p : (v : Nat) × Term v × Term v}
    (h : icmpEq? op0 = some (isEq, p)) (hc : op0.Consistent ρ) :
    w = 1 ∧ ∀ c : BitVec w, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes w else 0#w) →
      ∃ x, p.2.1.denote ρ = some x ∧ p.2.2.denote ρ = some x := by
  cases op0 with
  | icmp id pr s a b =>
    refine ⟨rfl, fun c hd hcv => ?_⟩
    obtain ⟨-, -, he⟩ := hc
    simp only [Term.denote] at hd
    rw [hd] at he
    cases pr <;> simp only [icmpEq?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · exact icmpEq_true he hcv
    · exact icmpNe_false he hcv
  | trunc id nuw nsw a =>
    simp only [icmpEq?] at h
    split at h
    · next hw =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun c hd hcv => ⟨0#_, ?_, rfl⟩⟩
      obtain ⟨-, he⟩ := hc
      simp only [Term.denote] at hd
      simp only [Bool.false_eq_true, ite_false] at hcv
      rw [hd, hcv] at he
      exact trunc_nuw_false he
    · cases h
  | _ => simp [icmpEq?] at h

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1965`: `and (icmp eq a, b), x` to false where `x` is false when `a == b`,
and `or (icmp ne a, b), x` to true where `x` is true when `a == b`. `hres` says `x` refines `Res` wherever the `icmp`
says `a == b`, which `simplifyWithOpReplaced`'s soundness gives. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1965 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (h : (isEq == isAnd && res.ident == (Term.const (absorber isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.const (absorber isAnd : BitVec 1)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hid⟩ := h
  have hr := Term.denote_of_ident (ρ := ρ) hid
  cases isEq <;> simp only [andOrSrc, absorber, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_const] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_true_of_implies _ _ d fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)
  · refine Lemmas.and_refines_false_of_implies _ _ fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1967`: `and (icmp eq a, b), x` to the `icmp` where `x` is true when
`a == b`, and `or (icmp ne a, b), x` to the `icmp` where `x` is false when `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1967 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (h : (isEq == isAnd && res.ident == (Term.const (identity isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hid⟩ := h
  have hr := Term.denote_of_ident (ρ := ρ) hid
  cases isEq <;> simp only [andOrSrc, identity, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_old] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_left_of_implies _ _ d fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm
  · refine Lemmas.and_refines_left_of_implies _ _ fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)

/-- `IS.simplifyAndOrWithICmpEq.Simplify.L1975`: `and (icmp ne a, b), x` to `x` where `x` is false when `a == b`, and
`or (icmp eq a, b), x` to `x` where `x` is true when `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.L1975 (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    (hp : (isEq == isAnd) = false) (h : (res.ident == (Term.const (absorber isAnd : BitVec 1)).ident) = true) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) ((Repl.old op1).eval ρ) := by
  simp only [beq_iff_eq] at h
  have hr := Term.denote_of_ident (ρ := ρ) h
  cases isAnd <;> cases isEq <;> simp at hp <;>
    simp only [andOrSrc, absorber, Bool.false_eq_true, ite_false, ite_true] at hr ⊢ <;>
    rw [Repl.eval_old] <;> refine refines_ok ?_
  · refine Lemmas.or_refines_right_of_true _ _ d fun hc => ?_
    have := hres _ hc (by decide)
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm.trans (by decide)
  · refine Lemmas.and_refines_right_of_false _ _ fun hc => ?_
    have := hres _ hc rfl
    rw [hr, Lemmas.Logic.refines_iff] at this
    simp only [Term.denote] at this
    exact this.imp id fun h => h.symm

/-- Theorem 1 for the lambda `Simplify`: what it returns refines the `and` or `or`, given `x` refines `Res` wherever
the `icmp` says `a == b`. -/
theorem simplifyAndOrWithICmpEq.Simplify.sound (ρ : Env) (isAnd isEq d : Bool) (op0 op1 res : Term 1)
    (hres : ∀ c, op0.denote ρ = some c → c = (if isEq then BitVec.allOnes 1 else 0#1) →
      Refines (op1.denote ρ) (res.denote ρ))
    {r : Repl 1} (h : run (simplifyAndOrWithICmpEq.Simplify.steps isAnd isEq op0 op1 res) = .value r) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound_ordered (P := fun r => Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ))
    (fun pre s r post hs hpre => ?_) h
  simp only [simplifyAndOrWithICmpEq.Simplify.steps] at hs
  match pre, hs with
  | [], hs =>
    simp only [List.nil_append, List.cons.injEq] at hs
    obtain ⟨h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    exact simplifyAndOrWithICmpEq.Simplify.L1965 ρ isAnd isEq d op0 op1 res hres (by assumption)
  | [_], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    exact simplifyAndOrWithICmpEq.Simplify.L1967 ρ isAnd isEq d op0 op1 res hres (by assumption)
  | [_, _], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, -, h1, -⟩ := hs
    split at h1 <;> simp only [reduceCtorEq] at h1
  | [_, _, s3], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨-, -, h3, h1, -⟩ := hs
    split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
    obtain ⟨-, rfl⟩ := h1
    have h3' := hpre s3 (by simp)
    rw [h3'] at h3
    have hp : (isEq == isAnd) = false := by
      cases hq : (isEq == isAnd) <;> simp_all
    exact simplifyAndOrWithICmpEq.Simplify.L1975 ρ isAnd isEq d op0 op1 res hres hp (by assumption)
  | _ :: _ :: _ :: _ :: _, hs =>
    simp only [List.cons_append, List.cons.injEq] at hs
    obtain ⟨-, -, -, -, h⟩ := hs
    simp at h

/-- Theorem 1 for `simplifyAndOrWithICmpEq`: what it returns refines the `and` or `or`, in a run where the answers
of `Logic.Ext`, if given, are sound: it rests on `simplifyWithOpReplaced`'s soundness, `Logic.Ext.Sound.replaced`. -/
theorem simplifyAndOrWithICmpEq.sound (ρ : Env) (x : Option Ext) (hx : ∀ e, x = some e → e.Sound ρ)
    (isAnd d : Bool) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ) {r : Repl w}
    (h : run (simplifyAndOrWithICmpEq.steps x isAnd op0 op1 n) = .value r) :
    Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((andOrSrc isAnd d op0 op1).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
  simp only [simplifyAndOrWithICmpEq.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h1 | h1 | h1
  · split at h1 <;> simp only [reduceCtorEq] at h1
  all_goals
    unfold simplifyAndOrWithICmpEq.replacedStep at h1
    split at h1
    · simp only [reduceCtorEq] at h1
    · next isEq p hp =>
      split at h1
      · simp only [reduceCtorEq] at h1
      · next e =>
        split at h1
        · next res hres =>
          obtain ⟨rfl, hspec⟩ := icmpEq?_spec hp c0
          have hs := hx e rfl
          refine simplifyAndOrWithICmpEq.Simplify.sound ρ isAnd isEq d op0 op1 res (fun c hd hc => ?_)
            (run_of_tail h1.symm)
          obtain ⟨v, ha, hb⟩ := hspec c hd hc
          simp only [Bool.false_eq_true, ite_false, ite_true] at hres
          first
            | exact hs.replaced n op1 res _ _ v hres ha hb
            | exact hs.replaced n op1 res _ _ v hres hb ha
        · simp only [reduceCtorEq] at h1

end Peephole.IS
