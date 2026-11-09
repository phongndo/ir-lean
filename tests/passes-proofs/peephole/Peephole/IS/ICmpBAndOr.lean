import Peephole.IS.ICmpB
import Peephole.IS.ICmpBConstantRange
import Peephole.IS.ICmpUnsignedRangeCheck

/-! # InstSimplify's folds of an `and` or `or` of two compares, and their rewrites for every input

At `llvmorg-23.1.3`, in `llvm/lib/Analysis/InstructionSimplify.cpp`: `simplifyAndOrOfICmpsWithConstants` at 1621-1656,
`simplifyAndOfICmpsWithAdd` at 1658-1704, `simplifyAndOrOfICmpsWithCtpop` at 1706-1723, `simplifyAndOfICmps` at
1725-1746, `simplifyOrOfICmpsWithAdd` at 1748-1793, `simplifyOrOfICmps` at 1795-1819 and `simplifyAndOrOfCmps` at
1902-1937. `simplifyAndInst` and `simplifyOrInst` forward to the last. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyAndOrOfICmpsWithConstants.L1638` | `(X P0 C0) & (X P1 C1)` to false where no `X` satisfies both |
| `IS.simplifyAndOrOfICmpsWithConstants.L1643` | `(X P0 C0) \| (X P1 C1)` to true where every `X` satisfies one |
| `IS.simplifyAndOrOfICmpsWithConstants.L1651` | the `and` to the smaller compare, the `or` to the larger |
| `IS.simplifyAndOrOfICmpsWithConstants.L1653` | the same, the other way round |
| `IS.simplifyAndOfICmpsWithAdd.L1682` … `L1699` | `(X + C0 P0 C1) & (X P1 C0)` to false, six forms |
| `IS.simplifyOrOfICmpsWithAdd.L1772` … `L1789` | `(X + C0 P0 C1) \| (X P1 C0)` to true, six forms |
| `IS.simplifyAndOrOfICmpsWithCtpop.L1717` | `(ctpop(X) == C) \| (X != 0)` to `X != 0`, for `C != 0` |
| `IS.simplifyAndOrOfICmpsWithCtpop.L1720` | `(ctpop(X) != C) & (X == 0)` to `X == 0`, for `C != 0` |
| `IS.simplifyAndOrOfCmps.L1933` | `cast(A) op cast(B)` to the constant `cast(V)`, where `A op B` simplified to `V` |

`simplifyAndOrOfICmpsWithConstants` asks `ConstantRange` whether the exact regions of the two compares meet, cover
everything, or contain one another. The model computes the answers as `llvm/lib/IR/ConstantRange.cpp` does: the
`icmp` family's `makeExactICmpRegion`, `contains`, `isEmptySet` and `isFullSet`, and `intersectWith` and `unionWith`
from `Peephole.IS.ICmpBConstantRange`. What each answer says about values is proved there and in
`Peephole.IS.ICmpConstantRange`, so the rewrites rest on no hypothesis about `ConstantRange`. The model reads a range
only at a positive width: LLVM has no `i0`, and at width 0 the full and the empty range are the same pair.
`simplifyAndOfICmps` and `simplifyOrOfICmps` also call `simplifyUnsignedRangeCheck`, first, both ways round: forwards
to the `icmp` family's model of it, `Peephole.IS.ICmpUnsignedRangeCheck`, whose `sound` and `sound_swap` are those
steps' theorems.

Each fold's theorem is about the `and`, or the `or` with or without `disjoint`, of the two compares it's given. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w u : Nat}

/-! ### What these folds replace -/

/-- `and A, B`, or `or [disjoint] A, B`: what an `and`/`or` fold replaces. -/
def logicSrc (isAnd d : Bool) (a b : Term w) : Repl w :=
  if isAnd then .bin .and {} (.old a) (.old b) else .bin .or { disjoint := d } (.old a) (.old b)

/-- The value of `and`/`or`. -/
def logicVal (isAnd d : Bool) (a b : Val w) : Val w := if isAnd then Val.and a b else Val.or a b d

theorem logicSrc_eval (ρ : Env) (isAnd d : Bool) (a b : Term w) :
    (logicSrc isAnd d a b).eval ρ = Outcome.ok (logicVal isAnd d (a.denote ρ) (b.denote ρ)) := by
  unfold logicSrc logicVal
  split <;> rfl

theorem logicVal_comm (isAnd d : Bool) (a b : Val w) : logicVal isAnd d a b = logicVal isAnd d b a := by
  cases a <;> cases b <;> cases isAnd <;> simp only [logicVal, Val.and, Val.map₂, Val.or, Bool.false_eq_true,
    ite_false, ite_true]
  · rename_i x y
    rw [BitVec.and_comm x y, BitVec.or_comm x y]
  · rename_i x y
    rw [BitVec.and_comm x y]

theorem logicSrc_comm (ρ : Env) (isAnd d : Bool) (a b : Term w) :
    (logicSrc isAnd d a b).eval ρ = (logicSrc isAnd d b a).eval ρ := by
  rw [logicSrc_eval, logicSrc_eval, logicVal_comm]

theorem logicVal_none_left (isAnd d : Bool) (b : Val w) : logicVal isAnd d none b = none := by
  cases isAnd <;> rfl

theorem logicVal_none_right (isAnd d : Bool) (a : Val w) : logicVal isAnd d a none = none := by
  cases isAnd <;> cases a <;> rfl

theorem logicVal_some (isAnd d : Bool) (x y : BitVec w) :
    logicVal isAnd d (some x) (some y) = none ∨
      logicVal isAnd d (some x) (some y) = some (if isAnd then x &&& y else x ||| y) := by
  cases isAnd <;> simp only [logicVal, Val.and, Val.map₂, Val.or, Bool.false_eq_true, ite_false, ite_true]
  · split <;> simp
  · simp

theorem logicVal_plain (isAnd : Bool) (x y : BitVec w) :
    logicVal isAnd false (some x) (some y) = some (if isAnd then x &&& y else x ||| y) := by
  cases isAnd <;> rfl

/-- An `and`/`or` of two `i1` values that's `r` wherever neither is poison refines `r`. -/
theorem logic_refines {ρ : Env} {isAnd d : Bool} {a b : Term w} {r : Repl w} {c : BitVec w}
    (hr : r.eval ρ = Outcome.ok (some c))
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y → (if isAnd then x &&& y else x ||| y) = c) :
    Refines ((logicSrc isAnd d a b).eval ρ) (r.eval ρ) := by
  rw [logicSrc_eval, hr]
  refine refines_ok ?_
  cases ha : a.denote ρ with
  | none => rw [logicVal_none_left]; exact Refine.val_none _
  | some x =>
  cases hb : b.denote ρ with
  | none => rw [logicVal_none_right]; exact Refine.val_none _
  | some y =>
  rcases logicVal_some isAnd d x y with h' | h' <;> rw [h']
  · exact Refine.val_none _
  · rw [h x y ha hb]; exact Refine.refl_val _

/-- An `and`/`or` of two `i1` values that's `b`'s wherever neither is poison refines `b`. -/
theorem logic_refines_right {ρ : Env} {isAnd d : Bool} {a b : Term w}
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y → (if isAnd then x &&& y else x ||| y) = y) :
    Refines ((logicSrc isAnd d a b).eval ρ) ((Repl.old b).eval ρ) := by
  rw [logicSrc_eval, Repl.eval_old]
  refine refines_ok ?_
  cases ha : a.denote ρ with
  | none => rw [logicVal_none_left]; exact Refine.val_none _
  | some x =>
  cases hb : b.denote ρ with
  | none => rw [logicVal_none_right]; exact Refine.val_none _
  | some y =>
  rcases logicVal_some isAnd d x y with h' | h' <;> rw [h']
  · exact Refine.val_none _
  · rw [h x y ha hb]; exact Refine.refl_val _

theorem logic_refines_left {ρ : Env} {isAnd d : Bool} {a b : Term w}
    (h : ∀ x y, a.denote ρ = some x → b.denote ρ = some y → (if isAnd then x &&& y else x ||| y) = x) :
    Refines ((logicSrc isAnd d a b).eval ρ) ((Repl.old a).eval ρ) := by
  rw [logicSrc_eval, Repl.eval_old]
  refine refines_ok ?_
  cases ha : a.denote ρ with
  | none => rw [logicVal_none_left]; exact Refine.val_none _
  | some x =>
  cases hb : b.denote ρ with
  | none => rw [logicVal_none_right]; exact Refine.val_none _
  | some y =>
  rcases logicVal_some isAnd d x y with h' | h' <;> rw [h']
  · exact Refine.val_none _
  · rw [h x y ha hb]; exact Refine.refl_val _

/-- A compare's value, where it isn't poison: what `test` says of its operands'. -/
theorem icmp_val {ρ : Env} {id : Nat} {p : Pred} {s : Bool} {l r : Term u}
    (hc : (Term.icmp id p s l r).Consistent ρ) {x : BitVec 1} (hx : (Term.icmp id p s l r).denote ρ = some x) :
    ∃ lv rv, l.denote ρ = some lv ∧ r.denote ρ = some rv ∧ x = BitVec.ofBool (test p lv rv) := by
  simp only [Term.Consistent] at hc
  obtain ⟨-, -, he⟩ := hc
  have hx' : ρ 1 id = some x := hx
  rw [← he] at hx'
  cases hl : l.denote ρ with
  | none => rw [hl, eval_none_left] at hx'; cases hx'
  | some lv =>
  cases hr : r.denote ρ with
  | none => rw [hr, eval_none_right] at hx'; cases hx'
  | some rv =>
  rw [hl, hr, eval_some] at hx'
  split at hx'
  · cases hx'
  · exact ⟨lv, rv, rfl, rfl, (Option.some.inj hx').symm⟩

theorem ofBool_and (a b : Bool) : BitVec.ofBool a &&& BitVec.ofBool b = BitVec.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

theorem ofBool_or (a b : Bool) : BitVec.ofBool a ||| BitVec.ofBool b = BitVec.ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-! ### `simplifyAndOrOfICmpsWithConstants` -/

theorem test_eq (p : Pred) (x y : BitVec w) : test p x y = ICmp.test p x y := by
  cases p <;> rfl

/-- `makeExactICmpRegion(P0, C0).intersectWith(makeExactICmpRegion(P1, C1)).isEmptySet()`, at a positive width. -/
def crEmptyAnd (p0 : Pred) (c0 : BitVec w) (p1 : Pred) (c1 : BitVec w) : Bool :=
  decide (0 < w) &&
    (Range.intersectWith (ICmp.CR.makeExactICmpRegion p0 c0) (ICmp.CR.makeExactICmpRegion p1 c1)).isEmptySet

/-- `makeExactICmpRegion(P0, C0).unionWith(makeExactICmpRegion(P1, C1)).isFullSet()`, at a positive width. -/
def crFullOr (p0 : Pred) (c0 : BitVec w) (p1 : Pred) (c1 : BitVec w) : Bool :=
  decide (0 < w) &&
    (Range.unionWith (ICmp.CR.makeExactICmpRegion p0 c0) (ICmp.CR.makeExactICmpRegion p1 c1)).isFullSet

/-- `makeExactICmpRegion(P0, C0).contains(makeExactICmpRegion(P1, C1))`, at a positive width. -/
def crContains (p0 : Pred) (c0 : BitVec w) (p1 : Pred) (c1 : BitVec w) : Bool :=
  decide (0 < w) && (ICmp.CR.makeExactICmpRegion p0 c0).containsRange (ICmp.CR.makeExactICmpRegion p1 c1)

/-- Where the intersection of the exact regions is empty, no value satisfies both compares. -/
theorem crEmptyAnd_sound {p0 p1 : Pred} {c0 c1 : BitVec w} (h : crEmptyAnd p0 c0 p1 c1 = true) (x : BitVec w) :
    (test p0 x c0 && test p1 x c1) = false := by
  simp only [crEmptyAnd, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, he⟩ := h
  rw [test_eq, test_eq, ← ICmp.CR.makeExact_contains hw, ← ICmp.CR.makeExact_contains hw]
  apply Bool.eq_false_iff.2
  intro hb
  rw [Bool.and_eq_true] at hb
  have hi := Range.intersectWith_contains hb.1 hb.2
  rw [ICmp.CR.isEmptySet_contains hw he] at hi
  cases hi

/-- Where the union of the exact regions is full, every value satisfies one of the compares. -/
theorem crFullOr_sound {p0 p1 : Pred} {c0 c1 : BitVec w} (h : crFullOr p0 c0 p1 c1 = true) (x : BitVec w) :
    (test p0 x c0 || test p1 x c1) = true := by
  simp only [crFullOr, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hf⟩ := h
  rw [test_eq, test_eq, ← ICmp.CR.makeExact_contains hw, ← ICmp.CR.makeExact_contains hw, Bool.or_eq_true]
  exact Range.unionWith_isFullSet hf x

/-- Where the first exact region contains the second, every value satisfying the second compare satisfies the first. -/
theorem crContains_sound {p0 p1 : Pred} {c0 c1 : BitVec w} (h : crContains p0 c0 p1 c1 = true) (x : BitVec w)
    (h1 : test p1 x c1 = true) : test p0 x c0 = true := by
  simp only [crContains, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hc⟩ := h
  rw [test_eq, ← ICmp.CR.makeExact_contains hw] at h1 ⊢
  exact ICmp.CR.containsRange_sound hw hc h1

/-- The steps once both compares have one width: `Cmp0`, `Cmp1`, their predicates and operands. -/
def crSteps (cmp0 cmp1 : Term 1) (p0 p1 : Pred) (x0 x1 k0 k1 : Term u) (isAnd : Bool) :
    List (Step 1) :=
  -- Look for this pattern: {and/or} (icmp X, C0), (icmp X, C1)).
  if specific x0 x1 then
    match apint k0, apint k1 with
    | some c0, some c1 =>
      [ -- For and-of-compares, check if the intersection is empty:
        -- (icmp X, C0) && (icmp X, C1) --> empty set --> false
        if isAnd && crEmptyAnd p0 c0 p1 c1 then .fire "IS.simplifyAndOrOfICmpsWithConstants.L1638" (boolR false)
        else .next,
        -- For or-of-compares, check if the union is full:
        -- (icmp X, C0) || (icmp X, C1) --> full set --> true
        if !isAnd && crFullOr p0 c0 p1 c1 then .fire "IS.simplifyAndOrOfICmpsWithConstants.L1643" (boolR true)
        else .next,
        -- Is one range a superset of the other?
        if crContains p0 c0 p1 c1 then
          .fire "IS.simplifyAndOrOfICmpsWithConstants.L1651" (.old (if isAnd then cmp1 else cmp0))
        else .next,
        if crContains p1 c1 p0 c0 then
          .fire "IS.simplifyAndOrOfICmpsWithConstants.L1653" (.old (if isAnd then cmp0 else cmp1))
        else .next ]
    | _, _ => []
  else []

/-- `simplifyAndOrOfICmpsWithConstants(Cmp0, Cmp1, IsAnd)`, step by step. Operands of different widths are different
pointers, so it declines. -/
def _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.steps (cmp0 cmp1 : Term 1) (isAnd : Bool) : List (Step 1) :=
  match cmp0, cmp1 with
  | .icmp (w := u) id0 p0 s0 x0 k0, .icmp (w := u') id1 p1 s1 x1 k1 =>
    if h : u' = u then crSteps (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1) p0 p1 x0 (h ▸ x1) k0 (h ▸ k1) isAnd
    else []
  | _, _ => []

def _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants (cmp0 cmp1 : Term 1) (isAnd : Bool) : Result 1 :=
  run (simplifyAndOrOfICmpsWithConstants.steps cmp0 cmp1 isAnd)

theorem cr_vals {ρ : Env} {id0 id1 : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {x0 x1 k0 k1 : Term u} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ)
    (hx : specific x0 x1 = true) (hk0 : apint k0 = some c0) (hk1 : apint k1 = some c1) :
    ∀ a b, (Term.icmp id0 p0 s0 x0 k0).denote ρ = some a → (Term.icmp id1 p1 s1 x1 k1).denote ρ = some b →
      ∃ xv, a = BitVec.ofBool (test p0 xv c0) ∧ b = BitVec.ofBool (test p1 xv c1) := by
  intro a b ha hb
  obtain ⟨l0, r0, hl0, hr0, rfl⟩ := icmp_val cc0 ha
  obtain ⟨l1, r1, hl1, hr1, rfl⟩ := icmp_val cc1 hb
  rw [apint_denote hk0] at hr0
  rw [apint_denote hk1] at hr1
  rw [specific_denote hx, hl0] at hl1
  cases hr0; cases hr1; cases hl1
  exact ⟨l0, rfl, rfl⟩

/-- `IS.simplifyAndOrOfICmpsWithConstants.L1638`: `(X P0 C0) & (X P1 C1)` to false where no `X` satisfies both. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.L1638 (ρ : Env) (d : Bool)
    (id0 id1 : Nat) (p0 p1 : Pred) (s0 s1 : Bool) (x0 x1 k0 k1 : Term u) (c0 c1 : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ)
    (hx : specific x0 x1 = true) (hk0 : apint k0 = some c0) (hk1 : apint k1 = some c1)
    (h : (isAnd && crEmptyAnd p0 c0 p1 c1) = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1)).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true] at h
  obtain ⟨rfl, he⟩ := h
  refine logic_refines (boolR_eval ρ false) fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := cr_vals cc0 cc1 hx hk0 hk1 a b ha hb
  simp only [ite_true, ofBool_and, crEmptyAnd_sound he xv]

/-- `IS.simplifyAndOrOfICmpsWithConstants.L1643`: `(X P0 C0) | (X P1 C1)` to true where every `X` satisfies one. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.L1643 (ρ : Env) (d : Bool)
    (id0 id1 : Nat) (p0 p1 : Pred) (s0 s1 : Bool) (x0 x1 k0 k1 : Term u) (c0 c1 : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ)
    (hx : specific x0 x1 = true) (hk0 : apint k0 = some c0) (hk1 : apint k1 = some c1)
    (h : (!isAnd && crFullOr p0 c0 p1 c1) = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1)).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨rfl, he⟩ := h
  refine logic_refines (boolR_eval ρ true) fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := cr_vals cc0 cc1 hx hk0 hk1 a b ha hb
  simp only [Bool.false_eq_true, ite_false, ofBool_or, crFullOr_sound he xv]

/-- `IS.simplifyAndOrOfICmpsWithConstants.L1651`: where the first region contains the second, the `and` to the second
compare and the `or` to the first. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.L1651 (ρ : Env) (d : Bool)
    (id0 id1 : Nat) (p0 p1 : Pred) (s0 s1 : Bool) (x0 x1 k0 k1 : Term u) (c0 c1 : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ)
    (hx : specific x0 x1 = true) (hk0 : apint k0 = some c0) (hk1 : apint k1 = some c1)
    (h : crContains p0 c0 p1 c1 = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1)).eval ρ)
      ((Repl.old (if isAnd then Term.icmp id1 p1 s1 x1 k1 else .icmp id0 p0 s0 x0 k0)).eval ρ) := by
  have hv := cr_vals cc0 cc1 hx hk0 hk1
  have hc := crContains_sound h
  cases isAnd
  · simp only [Bool.false_eq_true, ite_false]
    refine logic_refines_left fun a b ha hb => ?_
    obtain ⟨xv, rfl, rfl⟩ := hv a b ha hb
    simp only [Bool.false_eq_true, ite_false, ofBool_or]
    cases h1 : test p1 xv c1
    · simp
    · simp [hc xv h1]
  · simp only [ite_true]
    refine logic_refines_right fun a b ha hb => ?_
    obtain ⟨xv, rfl, rfl⟩ := hv a b ha hb
    simp only [ite_true, ofBool_and]
    cases h1 : test p1 xv c1
    · simp
    · simp [hc xv h1]

/-- `IS.simplifyAndOrOfICmpsWithConstants.L1653`: where the second region contains the first, the `and` to the first
compare and the `or` to the second. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.L1653 (ρ : Env) (d : Bool)
    (id0 id1 : Nat) (p0 p1 : Pred) (s0 s1 : Bool) (x0 x1 k0 k1 : Term u) (c0 c1 : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ)
    (hx : specific x0 x1 = true) (hk0 : apint k0 = some c0) (hk1 : apint k1 = some c1)
    (h : crContains p1 c1 p0 c0 = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1)).eval ρ)
      ((Repl.old (if isAnd then Term.icmp id0 p0 s0 x0 k0 else .icmp id1 p1 s1 x1 k1)).eval ρ) := by
  have hv := cr_vals cc0 cc1 hx hk0 hk1
  have hc := crContains_sound h
  cases isAnd
  · simp only [Bool.false_eq_true, ite_false]
    refine logic_refines_right fun a b ha hb => ?_
    obtain ⟨xv, rfl, rfl⟩ := hv a b ha hb
    simp only [Bool.false_eq_true, ite_false, ofBool_or]
    cases h0 : test p0 xv c0
    · simp
    · simp [hc xv h0]
  · simp only [ite_true]
    refine logic_refines_left fun a b ha hb => ?_
    obtain ⟨xv, rfl, rfl⟩ := hv a b ha hb
    simp only [ite_true, ofBool_and]
    cases h0 : test p0 xv c0
    · simp
    · simp [hc xv h0]

theorem crSteps_sound (ρ : Env) (d : Bool) (id0 id1 : Nat) (p0 p1 : Pred)
    (s0 s1 : Bool) (x0 x1 k0 k1 : Term u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 x0 k0).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x1 k1).Consistent ρ) :
    ∀ site r, Step.fire site r ∈ crSteps (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1) p0 p1 x0 x1 k0 k1 isAnd →
      Refines ((logicSrc isAnd d (.icmp id0 p0 s0 x0 k0) (.icmp id1 p1 s1 x1 k1)).eval ρ) (r.eval ρ) := by
  intro site r hmem
  unfold crSteps at hmem
  split at hmem
  · next hx =>
    split at hmem
    · next c0 c1 hk0 hk1 =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
        obtain ⟨-, rfl⟩ := h
      · exact simplifyAndOrOfICmpsWithConstants.L1638 ρ d _ _ _ _ _ _ _ _ _ _ _ _ isAnd cc0 cc1 hx hk0 hk1
          (by assumption)
      · exact simplifyAndOrOfICmpsWithConstants.L1643 ρ d _ _ _ _ _ _ _ _ _ _ _ _ isAnd cc0 cc1 hx hk0 hk1
          (by assumption)
      · exact simplifyAndOrOfICmpsWithConstants.L1651 ρ d _ _ _ _ _ _ _ _ _ _ _ _ isAnd cc0 cc1 hx hk0 hk1
          (by assumption)
      · exact simplifyAndOrOfICmpsWithConstants.L1653 ρ d _ _ _ _ _ _ _ _ _ _ _ _ isAnd cc0 cc1 hx hk0 hk1
          (by assumption)
    · simp at hmem
  · simp at hmem

/-- Theorem 1 for `simplifyAndOrOfICmpsWithConstants`: every value the model returns refines `and Cmp0, Cmp1` or
`or [disjoint] Cmp0, Cmp1`, at every width and `samesign` flag, poison included. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithConstants.sound (ρ : Env) (d : Bool)
    (cmp0 cmp1 : Term 1) (isAnd : Bool) (c0 : cmp0.Consistent ρ) (c1 : cmp1.Consistent ρ) {r : Repl 1}
    (h : simplifyAndOrOfICmpsWithConstants cmp0 cmp1 isAnd = .value r) :
    Refines ((logicSrc isAnd d cmp0 cmp1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyAndOrOfICmpsWithConstants.steps cmp0 cmp1 isAnd →
      Refines ((logicSrc isAnd d cmp0 cmp1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifyAndOrOfICmpsWithConstants.steps at hmem
  split at hmem
  · next u id0 p0 s0 x0 k0 u' id1 p1 s1 x1 k1 =>
    split at hmem
    · next hu =>
      subst hu
      exact crSteps_sound ρ d id0 id1 p0 p1 s0 s1 x0 x1 k0 k1 isAnd c0 c1 site r hmem
    · simp at hmem
  · simp at hmem

/-! ### `simplifyAndOfICmpsWithAdd` and `simplifyOrOfICmpsWithAdd` -/

/-- `simplifyAndOfICmpsWithAdd`'s tests, once both compares match. -/
def andAddSteps (p0 p1 : Pred) (f : Flags) (c0 c1 : BitVec u) : List (Step 1) :=
  [ if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .ult && p1 == .sgt then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1682" (boolR false)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .slt && p1 == .sgt && f.nsw then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1684" (boolR false)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .ule && p1 == .sgt then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1688" (boolR false)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .sle && p1 == .sgt && f.nsw then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1690" (boolR false)
    else .next,
    if c0 != 0#u && f.nuw && (c1 - c0).toNat == 2 && p0 == .ult && p1 == .ugt then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1696" (boolR false)
    else .next,
    if c0 != 0#u && f.nuw && (c1 - c0).toNat == 1 && p0 == .ule && p1 == .ugt then
      .fire "IS.simplifyAndOfICmpsWithAdd.L1699" (boolR false)
    else .next ]

/-- `simplifyOrOfICmpsWithAdd`'s tests, once both compares match. -/
def orAddSteps (p0 p1 : Pred) (f : Flags) (c0 c1 : BitVec u) : List (Step 1) :=
  [ if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .uge && p1 == .sle then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1772" (boolR true)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .sge && p1 == .sle && f.nsw then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1774" (boolR true)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .ugt && p1 == .sle then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1778" (boolR true)
    else .next,
    if !c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .sgt && p1 == .sle && f.nsw then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1780" (boolR true)
    else .next,
    if c0 != 0#u && f.nuw && (c1 - c0).toNat == 2 && p0 == .uge && p1 == .ule then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1786" (boolR true)
    else .next,
    if c0 != 0#u && f.nuw && (c1 - c0).toNat == 1 && p0 == .ugt && p1 == .ule then
      .fire "IS.simplifyOrOfICmpsWithAdd.L1789" (boolR true)
    else .next ]

/-- `match(Op0, m_ICmp(Pred0, m_Add(m_Value(V), m_APInt(C0)), m_APInt(C1)))`,
`match(Op1, m_ICmp(Pred1, m_Specific(V), m_Value()))` and `AddInst->getOperand(1) == Op1->getOperand(1)`, then
`steps`; else `return nullptr`. -/
def withAddSteps (steps : {u : Nat} → Pred → Pred → Flags → BitVec u → BitVec u → List (Step 1)) :
    Term 1 → Term 1 → List (Step 1)
  | .icmp _ p0 _ (.bin _ .add f v c0t) c1t, .icmp _ p1 _ v' c0t' =>
    match apint c0t, apint c1t with
    | some c0, some c1 => if same v v' && same c0t c0t' then steps p0 p1 f c0 c1 else []
    | _, _ => []
  | _, _ => []

/-- `simplifyAndOfICmpsWithAdd(Op0, Op1, IIQ)`, with `IIQ.UseInstrInfo` true. -/
def _root_.Peephole.IS.simplifyAndOfICmpsWithAdd (op0 op1 : Term 1) : Result 1 := run (withAddSteps andAddSteps op0 op1)

/-- `simplifyOrOfICmpsWithAdd(Op0, Op1, IIQ)`, with `IIQ.UseInstrInfo` true. -/
def _root_.Peephole.IS.simplifyOrOfICmpsWithAdd (op0 op1 : Term 1) : Result 1 := run (withAddSteps orAddSteps op0 op1)

theorem eq_add_ofNat {c0 c1 : BitVec u} {k : Nat} (h : (c1 - c0).toNat = k) : c1 = c0 + BitVec.ofNat u k := by
  have hk : k < 2 ^ u := h ▸ (c1 - c0).isLt
  have : c1 - c0 = BitVec.ofNat u k := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk])
  rw [← this, BitVec.add_comm, BitVec.sub_add_cancel]

theorem toInt_pos {c : BitVec u} (hm : c.msb = false) (h0 : c ≠ 0#u) : 0 < c.toInt := by
  rw [BitVec.toInt_eq_toNat_of_msb hm]
  have : c.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

/-- What both compares are, wherever neither is poison: `V + C0 P0 C1` and `V P1 C0`, the `add` not wrapping where
its flags say so. -/
theorem withAdd_val {ρ : Env} {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true) :
    ∀ a b, (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).denote ρ = some a →
      (Term.icmp id1 p1 s1 v' c0t').denote ρ = some b → ∃ av,
        a = BitVec.ofBool (test p0 (av + c0) c1) ∧ b = BitVec.ofBool (test p1 av c0) ∧
          (f.nuw = true → av.uaddOverflow c0 = false) ∧ (f.nsw = true → av.saddOverflow c0 = false) := by
  intro a b ha hb
  simp only [Bool.and_eq_true] at hm
  obtain ⟨hv, hc⟩ := hm
  obtain rfl := same_width hv
  rw [same_iff_specific] at hv hc
  obtain ⟨l0, r0, hl0, hr0, rfl⟩ := icmp_val cc0 ha
  obtain ⟨l1, r1, hl1, hr1, rfl⟩ := icmp_val cc1 hb
  have cadd := cc0.1
  simp only [Term.Consistent] at cadd
  obtain ⟨-, -, he⟩ := cadd
  have he' : Val.add (v.denote ρ) (c0t.denote ρ) f.nuw f.nsw = ρ u aid := ok_inj he
  have hl0' : ρ u aid = some l0 := hl0
  rw [hl0', apint_denote hk0] at he'
  obtain ⟨av, c0', hav, hc0, rfl, hu, hs⟩ := add_some he'
  have e0 := Option.some.inj hc0
  subst e0
  rw [apint_denote hk1] at hr0
  have e1 := Option.some.inj hr0
  subst e1
  rw [specific_denote hv, hav] at hl1
  rw [specific_denote hc, apint_denote hk0] at hr1
  have e2 := Option.some.inj hl1
  have e3 := Option.some.inj hr1
  subst e2 e3
  exact ⟨av, rfl, rfl, hu, hs⟩

/-- `IS.simplifyAndOfICmpsWithAdd.L1682`, `L1684`, `L1688`, `L1690`, `L1696` and `L1699`, which all say the two compares
aren't both true: `(V + C0 P0 C1) & (V P1 C0)` to false. -/
theorem andAdd_false {ρ : Env} {d : Bool} {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (hf : ∀ av : BitVec u, (f.nuw = true → av.uaddOverflow c0 = false) → (f.nsw = true → av.saddOverflow c0 = false) →
      (test p0 (av + c0) c1 && test p1 av c0) = false) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  refine logic_refines (boolR_eval ρ false) fun a b ha hb => ?_
  obtain ⟨av, rfl, rfl, hu, hs⟩ := withAdd_val cc0 cc1 hk0 hk1 hm a b ha hb
  simp only [ite_true, ofBool_and, hf av hu hs]

/-- The same for `or`: `(V + C0 P0 C1) | (V P1 C0)` to true, where the two compares aren't both false. -/
theorem orAdd_true {ρ : Env} {d : Bool} {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (hf : ∀ av : BitVec u, (f.nuw = true → av.uaddOverflow c0 = false) → (f.nsw = true → av.saddOverflow c0 = false) →
      (test (invP p0) (av + c0) c1 && test (invP p1) av c0) = false) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  refine logic_refines (boolR_eval ρ true) fun a b ha hb => ?_
  obtain ⟨av, rfl, rfl, hu, hs⟩ := withAdd_val cc0 cc1 hk0 hk1 hm a b ha hb
  have := hf av hu hs
  rw [test_inv, test_inv] at this
  simp only [Bool.false_eq_true, ite_false, ofBool_or]
  cases h0 : test p0 (av + c0) c1 <;> cases h1 : test p1 av c0 <;> simp_all

/-- `IS.simplifyAndOfICmpsWithAdd.L1682`: `(V + C0 <u C1) & (V >s C0)` to false, for `C0 >s 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1682 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .ult && p1 == .sgt) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ult_add_two_and_sgt (toInt_pos hm' h0)

/-- `IS.simplifyAndOfICmpsWithAdd.L1684`: `(V +nsw C0 <s C1) & (V >s C0)` to false, for `C0 >s 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1684 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .slt && p1 == .sgt && f.nsw) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩, hn⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.slt_add_two_and_sgt (toInt_pos hm' h0) (hs hn)

/-- `IS.simplifyAndOfICmpsWithAdd.L1688`: `(V + C0 <=u C1) & (V >s C0)` to false, for `C0 >s 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1688 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .ule && p1 == .sgt) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    rw [Bool.and_comm]
    exact Lemmas.ule_add_one_and_sgt (toInt_pos hm' h0)

/-- `IS.simplifyAndOfICmpsWithAdd.L1690`: `(V +nsw C0 <=s C1) & (V >s C0)` to false, for `C0 >s 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1690 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .sle && p1 == .sgt && f.nsw) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩, hn⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.sle_add_one_and_sgt (toInt_pos hm' h0) (hs hn)

/-- `IS.simplifyAndOfICmpsWithAdd.L1696`: `(V +nuw C0 <u C1) & (V >u C0)` to false, for `C0 != 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1696 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (c0 != 0#u && f.nuw && (c1 - c0).toNat == 2 && p0 == .ult && p1 == .ugt) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hn⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ult_add_two_and_ugt h0 (hu hn)

/-- `IS.simplifyAndOfICmpsWithAdd.L1699`: `(V +nuw C0 <=u C1) & (V >u C0)` to false, for `C0 != 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.L1699 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (c0 != 0#u && f.nuw && (c1 - c0).toNat == 1 && p0 == .ule && p1 == .ugt) = true) :
    Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hn⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact andAdd_false cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ule_add_one_and_ugt h0 (hu hn)

/-- `IS.simplifyOrOfICmpsWithAdd.L1772`: `(V + C0 >=u C1) | (V <=s C0)` to true, for `C0 >s 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1772 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .uge && p1 == .sle) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ult_add_two_and_sgt (toInt_pos hm' h0)

/-- `IS.simplifyOrOfICmpsWithAdd.L1774`: `(V +nsw C0 >=s C1) | (V <=s C0)` to true, for `C0 >s 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1774 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 2 && p0 == .sge && p1 == .sle && f.nsw) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩, hn⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.slt_add_two_and_sgt (toInt_pos hm' h0) (hs hn)

/-- `IS.simplifyOrOfICmpsWithAdd.L1778`: `(V + C0 >u C1) | (V <=s C0)` to true, for `C0 >s 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1778 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .ugt && p1 == .sle) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    rw [Bool.and_comm]
    exact Lemmas.ule_add_one_and_sgt (toInt_pos hm' h0)

/-- `IS.simplifyOrOfICmpsWithAdd.L1780`: `(V +nsw C0 >s C1) | (V <=s C0)` to true, for `C0 >s 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1780 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (!c0.msb && c0 != 0#u && (c1 - c0).toNat == 1 && p0 == .sgt && p1 == .sle && f.nsw) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hm', h0⟩, hd⟩, rfl⟩, rfl⟩, hn⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.sle_add_one_and_sgt (toInt_pos hm' h0) (hs hn)

/-- `IS.simplifyOrOfICmpsWithAdd.L1786`: `(V +nuw C0 >=u C1) | (V <=u C0)` to true, for `C0 != 0` and `C1 - C0 == 2`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1786 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (c0 != 0#u && f.nuw && (c1 - c0).toNat == 2 && p0 == .uge && p1 == .ule) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hn⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ult_add_two_and_ugt h0 (hu hn)

/-- `IS.simplifyOrOfICmpsWithAdd.L1789`: `(V +nuw C0 >u C1) | (V <=u C0)` to true, for `C0 != 0` and `C1 - C0 == 1`. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.L1789 (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true)
    (h : (c0 != 0#u && f.nuw && (c1 - c0).toNat == 1 && p0 == .ugt && p1 == .ule) = true) :
    Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
      ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hn⟩, hd⟩, rfl⟩, rfl⟩ := h
  exact orAdd_true cc0 cc1 hk0 hk1 hm fun av hu hs => by
    rw [eq_add_ofNat hd]
    exact Lemmas.ule_add_one_and_ugt h0 (hu hn)

theorem andAddSteps_sound (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true) :
    ∀ site r, Step.fire site r ∈ andAddSteps p0 p1 f c0 c1 →
      Refines ((logicSrc true d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
        (r.eval ρ) := by
  intro site r h
  simp only [andAddSteps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
    obtain ⟨-, rfl⟩ := h
  · exact simplifyAndOfICmpsWithAdd.L1682 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyAndOfICmpsWithAdd.L1684 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyAndOfICmpsWithAdd.L1688 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyAndOfICmpsWithAdd.L1690 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyAndOfICmpsWithAdd.L1696 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyAndOfICmpsWithAdd.L1699 ρ d cc0 cc1 hk0 hk1 hm (by assumption)

theorem orAddSteps_sound (ρ : Env) (d : Bool) {id0 id1 aid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {f : Flags}
    {v c0t c1t : Term u} {v' c0t' : Term u'} {c0 c1 : BitVec u}
    (cc0 : (Term.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 v' c0t').Consistent ρ) (hk0 : apint c0t = some c0) (hk1 : apint c1t = some c1)
    (hm : (same v v' && same c0t c0t') = true) :
    ∀ site r, Step.fire site r ∈ orAddSteps p0 p1 f c0 c1 →
      Refines ((logicSrc false d (.icmp id0 p0 s0 (.bin aid .add f v c0t) c1t) (.icmp id1 p1 s1 v' c0t')).eval ρ)
        (r.eval ρ) := by
  intro site r h
  simp only [orAddSteps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
    obtain ⟨-, rfl⟩ := h
  · exact simplifyOrOfICmpsWithAdd.L1772 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyOrOfICmpsWithAdd.L1774 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyOrOfICmpsWithAdd.L1778 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyOrOfICmpsWithAdd.L1780 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyOrOfICmpsWithAdd.L1786 ρ d cc0 cc1 hk0 hk1 hm (by assumption)
  · exact simplifyOrOfICmpsWithAdd.L1789 ρ d cc0 cc1 hk0 hk1 hm (by assumption)

/-- Theorem 1 for `simplifyAndOfICmpsWithAdd`: every value the model returns refines `and Op0, Op1`, at every width,
flag and `samesign` flag, poison included. Its six sites' value facts are `simplifyAndOfICmpsWithAdd.L1682` to
`L1699`. -/
theorem _root_.Peephole.IS.simplifyAndOfICmpsWithAdd.sound (ρ : Env) (d : Bool) (op0 op1 : Term 1) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) {r : Repl 1} (h : simplifyAndOfICmpsWithAdd op0 op1 = .value r) :
    Refines ((logicSrc true d op0 op1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ withAddSteps andAddSteps op0 op1 →
      Refines ((logicSrc true d op0 op1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold withAddSteps at hmem
  split at hmem
  · split at hmem
    · next k0 k1 hk0 hk1 =>
      split at hmem
      · next hm =>
        exact andAddSteps_sound ρ d c0 c1 hk0 hk1 hm site r hmem
      · simp at hmem
    · simp at hmem
  · simp at hmem

/-- Theorem 1 for `simplifyOrOfICmpsWithAdd`: every value the model returns refines `or [disjoint] Op0, Op1`, at every
width, flag and `samesign` flag, poison included. -/
theorem _root_.Peephole.IS.simplifyOrOfICmpsWithAdd.sound (ρ : Env) (d : Bool) (op0 op1 : Term 1) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) {r : Repl 1} (h : simplifyOrOfICmpsWithAdd op0 op1 = .value r) :
    Refines ((logicSrc false d op0 op1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ withAddSteps orAddSteps op0 op1 →
      Refines ((logicSrc false d op0 op1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold withAddSteps at hmem
  split at hmem
  · split at hmem
    · next k0 k1 hk0 hk1 =>
      split at hmem
      · next hm =>
        exact orAddSteps_sound ρ d c0 c1 hk0 hk1 hm site r hmem
      · simp at hmem
    · simp at hmem
  · simp at hmem

/-! ### `simplifyAndOrOfICmpsWithCtpop` -/

/-- `simplifyAndOrOfICmpsWithCtpop(Cmp0, Cmp1, IsAnd)`, step by step. -/
def _root_.Peephole.IS.simplifyAndOrOfICmpsWithCtpop.steps (cmp0 cmp1 : Term 1) (isAnd : Bool) : List (Step 1) :=
  match cmp0, cmp1 with
  | .icmp (w := u) _ p0 _ (.un _ .ctpop x) ct, .icmp id1 p1 s1 x' zt =>
    match apint ct with
    | some c =>
      if same x x' && zero zt && c != 0#u then
        [ -- (ctpop(X) == C) || (X != 0) --> X != 0 where C > 0
          if !isAnd && p0 == .eq && p1 == .ne then
            .fire "IS.simplifyAndOrOfICmpsWithCtpop.L1717" (.old (.icmp id1 p1 s1 x' zt))
          else .next,
          -- (ctpop(X) != C) && (X == 0) --> X == 0 where C > 0
          if isAnd && p0 == .ne && p1 == .eq then
            .fire "IS.simplifyAndOrOfICmpsWithCtpop.L1720" (.old (.icmp id1 p1 s1 x' zt))
          else .next ]
      else []
    | none => []
  | _, _ => []

def _root_.Peephole.IS.simplifyAndOrOfICmpsWithCtpop (cmp0 cmp1 : Term 1) (isAnd : Bool) : Result 1 :=
  run (simplifyAndOrOfICmpsWithCtpop.steps cmp0 cmp1 isAnd)

theorem ctpop_vals {ρ : Env} {id0 id1 cid : Nat} {p0 p1 : Pred} {s0 s1 : Bool} {x ct : Term u} {x' zt : Term u'}
    {c : BitVec u} (cc0 : (Term.icmp id0 p0 s0 (.un cid .ctpop x) ct).Consistent ρ)
    (cc1 : (Term.icmp id1 p1 s1 x' zt).Consistent ρ) (hct : apint ct = some c)
    (hm : (same x x' && zero zt) = true) :
    ∀ a b, (Term.icmp id0 p0 s0 (.un cid .ctpop x) ct).denote ρ = some a →
      (Term.icmp id1 p1 s1 x' zt).denote ρ = some b → ∃ xv : BitVec u,
        a = BitVec.ofBool (test p0 xv.cpop c) ∧ b = BitVec.ofBool (test p1 xv 0#u) := by
  intro a b ha hb
  simp only [Bool.and_eq_true] at hm
  obtain ⟨hx, hz⟩ := hm
  obtain rfl := same_width hx
  rw [same_iff_specific] at hx
  obtain ⟨l0, r0, hl0, hr0, rfl⟩ := icmp_val cc0 ha
  obtain ⟨l1, r1, hl1, hr1, rfl⟩ := icmp_val cc1 hb
  have cun := cc0.1
  simp only [Term.Consistent] at cun
  obtain ⟨-, he⟩ := cun
  have hl0' : ρ u cid = some l0 := hl0
  rw [← he] at hl0'
  cases hxd : x.denote ρ with
  | none => rw [hxd] at hl0'; cases hl0'
  | some xv =>
  rw [hxd] at hl0'
  simp only [UnIntr.eval, Val.ctpop, Val.map₁, Option.some.injEq] at hl0'
  subst hl0'
  rw [apint_denote hct] at hr0
  rw [specific_denote hx, hxd] at hl1
  rw [cst_eq hz] at hr1
  have e1 := Option.some.inj hr0
  have e2 := Option.some.inj hl1
  have e3 := Option.some.inj hr1
  subst e1 e2 e3
  exact ⟨xv, rfl, rfl⟩

/-- `IS.simplifyAndOrOfICmpsWithCtpop.L1717`: `(ctpop(X) == C) | (X != 0)` to `X != 0`, for `C != 0`. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithCtpop.L1717 (ρ : Env) (d : Bool) (id0 id1 cid : Nat) (p0 p1 : Pred) (s0 s1 : Bool)
    (x ct : Term u) (x' zt : Term u') (c : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 (.un cid .ctpop x) ct).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x' zt).Consistent ρ)
    (hct : apint ct = some c) (hm : (same x x' && zero zt && c != 0#u) = true)
    (h : (!isAnd && p0 == .eq && p1 == .ne) = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 (.un cid .ctpop x) ct) (.icmp id1 p1 s1 x' zt)).eval ρ)
      ((Repl.old (Term.icmp id1 p1 s1 x' zt)).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rw [Bool.and_eq_true, bne_iff_ne] at hm
  obtain ⟨hm, hc0⟩ := hm
  refine logic_refines_right fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := ctpop_vals cc0 cc1 hct hm a b ha hb
  simp only [Bool.false_eq_true, ite_false, ofBool_or]
  by_cases hx : xv = 0#u
  · subst hx
    simp only [test, BitVec.cpop_zero, bne_self_eq_false, Bool.or_false]
    congr 1
    simp only [beq_eq_false_iff_ne]
    exact fun h => hc0 h.symm
  · have hne : (xv != 0#u) = true := by simp [hx]
    simp only [test, hne, Bool.or_true]

/-- `IS.simplifyAndOrOfICmpsWithCtpop.L1720`: `(ctpop(X) != C) & (X == 0)` to `X == 0`, for `C != 0`. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithCtpop.L1720 (ρ : Env) (d : Bool) (id0 id1 cid : Nat) (p0 p1 : Pred) (s0 s1 : Bool)
    (x ct : Term u) (x' zt : Term u') (c : BitVec u) (isAnd : Bool)
    (cc0 : (Term.icmp id0 p0 s0 (.un cid .ctpop x) ct).Consistent ρ) (cc1 : (Term.icmp id1 p1 s1 x' zt).Consistent ρ)
    (hct : apint ct = some c) (hm : (same x x' && zero zt && c != 0#u) = true)
    (h : (isAnd && p0 == .ne && p1 == .eq) = true) :
    Refines ((logicSrc isAnd d (.icmp id0 p0 s0 (.un cid .ctpop x) ct) (.icmp id1 p1 s1 x' zt)).eval ρ)
      ((Repl.old (Term.icmp id1 p1 s1 x' zt)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rw [Bool.and_eq_true, bne_iff_ne] at hm
  obtain ⟨hm, hc0⟩ := hm
  refine logic_refines_right fun a b ha hb => ?_
  obtain ⟨xv, rfl, rfl⟩ := ctpop_vals cc0 cc1 hct hm a b ha hb
  simp only [ite_true, ofBool_and]
  by_cases hx : xv = 0#u
  · subst hx
    simp only [test, BitVec.cpop_zero, BEq.rfl, Bool.and_true]
    congr 1
    simp only [bne_iff_ne, ne_eq]
    exact fun h => hc0 h.symm
  · have heq : (xv == 0#u) = false := by simp [hx]
    simp only [test, heq, Bool.and_false]

/-- Theorem 1 for `simplifyAndOrOfICmpsWithCtpop`: every value the model returns refines `and Cmp0, Cmp1` or
`or [disjoint] Cmp0, Cmp1`, at every width and `samesign` flag, poison included. -/
theorem _root_.Peephole.IS.simplifyAndOrOfICmpsWithCtpop.sound (ρ : Env) (d : Bool) (cmp0 cmp1 : Term 1) (isAnd : Bool)
    (c0 : cmp0.Consistent ρ) (c1 : cmp1.Consistent ρ) {r : Repl 1}
    (h : simplifyAndOrOfICmpsWithCtpop cmp0 cmp1 isAnd = .value r) :
    Refines ((logicSrc isAnd d cmp0 cmp1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyAndOrOfICmpsWithCtpop.steps cmp0 cmp1 isAnd →
      Refines ((logicSrc isAnd d cmp0 cmp1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifyAndOrOfICmpsWithCtpop.steps at hmem
  split at hmem
  · split at hmem
    · next c hct =>
      split at hmem
      · next hm =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
          obtain ⟨-, rfl⟩ := h
        · exact simplifyAndOrOfICmpsWithCtpop.L1717 ρ d _ _ _ _ _ _ _ _ _ _ _ c isAnd c0 c1 hct hm (by assumption)
        · exact simplifyAndOrOfICmpsWithCtpop.L1720 ρ d _ _ _ _ _ _ _ _ _ _ _ c isAnd c0 c1 hct hm (by assumption)
      · simp at hmem
    · simp at hmem
  · simp at hmem

/-! ### `simplifyAndOfICmps` and `simplifyOrOfICmps` -/

/-- The `and`, or the `or` with or without `disjoint`, is `ICmp.andOrSrc` with those flags: what
`simplifyUnsignedRangeCheck`'s theorem is about. -/
theorem logicSrc_and (d : Bool) (a b : Term 1) : logicSrc true d a b = ICmp.andOrSrc true {} a b := rfl

theorem logicSrc_or (d : Bool) (a b : Term 1) : logicSrc false d a b = ICmp.andOrSrc false { disjoint := d } a b :=
  rfl

/-- `simplifyAndOfICmps(Op0, Op1, Q)`, step by step. -/
def _root_.Peephole.IS.simplifyAndOfICmps.steps (o : Oracle) (op0 op1 : Term 1) : List (Step 1) :=
  [ fwd "IS.simplifyUnsignedRangeCheck" (simplifyUnsignedRangeCheck o op0 op1 true),
    fwd "IS.simplifyUnsignedRangeCheck" (simplifyUnsignedRangeCheck o op1 op0 true),
    fwd "IS.simplifyAndOrOfICmpsWithConstants" (simplifyAndOrOfICmpsWithConstants op0 op1 true),
    fwd "IS.simplifyAndOrOfICmpsWithCtpop" (simplifyAndOrOfICmpsWithCtpop op0 op1 true),
    fwd "IS.simplifyAndOrOfICmpsWithCtpop" (simplifyAndOrOfICmpsWithCtpop op1 op0 true),
    fwd "IS.simplifyAndOfICmpsWithAdd" (simplifyAndOfICmpsWithAdd op0 op1),
    fwd "IS.simplifyAndOfICmpsWithAdd" (simplifyAndOfICmpsWithAdd op1 op0) ]

def _root_.Peephole.IS.simplifyAndOfICmps (o : Oracle) (op0 op1 : Term 1) : Result 1 :=
  run (simplifyAndOfICmps.steps o op0 op1)

/-- `simplifyOrOfICmps(Op0, Op1, Q)`, step by step. -/
def _root_.Peephole.IS.simplifyOrOfICmps.steps (o : Oracle) (op0 op1 : Term 1) : List (Step 1) :=
  [ fwd "IS.simplifyUnsignedRangeCheck" (simplifyUnsignedRangeCheck o op0 op1 false),
    fwd "IS.simplifyUnsignedRangeCheck" (simplifyUnsignedRangeCheck o op1 op0 false),
    fwd "IS.simplifyAndOrOfICmpsWithConstants" (simplifyAndOrOfICmpsWithConstants op0 op1 false),
    fwd "IS.simplifyAndOrOfICmpsWithCtpop" (simplifyAndOrOfICmpsWithCtpop op0 op1 false),
    fwd "IS.simplifyAndOrOfICmpsWithCtpop" (simplifyAndOrOfICmpsWithCtpop op1 op0 false),
    fwd "IS.simplifyOrOfICmpsWithAdd" (simplifyOrOfICmpsWithAdd op0 op1),
    fwd "IS.simplifyOrOfICmpsWithAdd" (simplifyOrOfICmpsWithAdd op1 op0) ]

def _root_.Peephole.IS.simplifyOrOfICmps (o : Oracle) (op0 op1 : Term 1) : Result 1 :=
  run (simplifyOrOfICmps.steps o op0 op1)

/-- Theorem 1 for `simplifyAndOfICmps`: every value the model returns refines `and Op0, Op1`, given sound
analyses. -/
theorem _root_.Peephole.IS.simplifyAndOfICmps.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : Bool)
    (op0 op1 : Term 1) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) {r : Repl 1}
    (h : simplifyAndOfICmps o op0 op1 = .value r) : Refines ((logicSrc true d op0 op1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyAndOfICmps.steps o op0 op1 →
      Refines ((logicSrc true d op0 op1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  simp only [simplifyAndOfICmps.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · rw [logicSrc_and]
    exact simplifyUnsignedRangeCheck.sound ρ o ho op0 op1 true {} c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_and]
    exact simplifyUnsignedRangeCheck.sound_swap ρ o ho op1 op0 true {} c1 c0 (fwd_fire h.symm)
  · exact simplifyAndOrOfICmpsWithConstants.sound ρ d op0 op1 true c0 c1 (fwd_fire h.symm)
  · exact simplifyAndOrOfICmpsWithCtpop.sound ρ d op0 op1 true c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_comm]; exact simplifyAndOrOfICmpsWithCtpop.sound ρ d op1 op0 true c1 c0 (fwd_fire h.symm)
  · exact simplifyAndOfICmpsWithAdd.sound ρ d op0 op1 c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_comm]; exact simplifyAndOfICmpsWithAdd.sound ρ d op1 op0 c1 c0 (fwd_fire h.symm)

/-- Theorem 1 for `simplifyOrOfICmps`: every value the model returns refines `or [disjoint] Op0, Op1`, given sound
analyses. -/
theorem _root_.Peephole.IS.simplifyOrOfICmps.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : Bool)
    (op0 op1 : Term 1) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) {r : Repl 1}
    (h : simplifyOrOfICmps o op0 op1 = .value r) : Refines ((logicSrc false d op0 op1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyOrOfICmps.steps o op0 op1 →
      Refines ((logicSrc false d op0 op1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  simp only [simplifyOrOfICmps.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h
  · rw [logicSrc_or]
    exact simplifyUnsignedRangeCheck.sound ρ o ho op0 op1 false _ c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_or]
    exact simplifyUnsignedRangeCheck.sound_swap ρ o ho op1 op0 false _ c1 c0 (fwd_fire h.symm)
  · exact simplifyAndOrOfICmpsWithConstants.sound ρ d op0 op1 false c0 c1 (fwd_fire h.symm)
  · exact simplifyAndOrOfICmpsWithCtpop.sound ρ d op0 op1 false c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_comm]; exact simplifyAndOrOfICmpsWithCtpop.sound ρ d op1 op0 false c1 c0 (fwd_fire h.symm)
  · exact simplifyOrOfICmpsWithAdd.sound ρ d op0 op1 c0 c1 (fwd_fire h.symm)
  · rw [logicSrc_comm]; exact simplifyOrOfICmpsWithAdd.sound ρ d op1 op0 c1 c0 (fwd_fire h.symm)

/-! ### `simplifyAndOrOfCmps` -/

/-- `IsAnd ? simplifyAndOfICmps(ICmp0, ICmp1, Q) : simplifyOrOfICmps(ICmp0, ICmp1, Q)`. -/
def andOrOfICmps (o : Oracle) (a b : Term 1) (isAnd : Bool) : Result 1 :=
  if isAnd then simplifyAndOfICmps o a b else simplifyOrOfICmps o a b

theorem andOrOfICmps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : Bool) (a b : Term 1)
    (isAnd : Bool) (ca : a.Consistent ρ) (cb : b.Consistent ρ) {r : Repl 1}
    (h : andOrOfICmps o a b isAnd = .value r) : Refines ((logicSrc isAnd d a b).eval ρ) (r.eval ρ) := by
  unfold andOrOfICmps at h
  cases isAnd
  · exact simplifyOrOfICmps.sound ρ o ho d a b ca cb h
  · exact simplifyAndOfICmps.sound ρ o ho d a b ca cb h

/-- After looking through two casts of one kind: `if (!V) return nullptr;`, and then, since `Cast0` isn't null,
`ConstantFoldCastOperand` of `V` where it's a `Constant`. `fold` is the cast on an `i1` constant. -/
def castSteps (fold : BitVec 1 → BitVec w) : Result 1 → List (Step w)
  | .null => [.decline]
  | .delegated c => [.delegate c]
  | .value (.const c) => [.fire "IS.simplifyAndOrOfCmps.L1933" (.const (fold c))]
  | .value .poison => [.fire "IS.simplifyAndOrOfCmps.L1933" .poison]
  | .value (.old t) => if t.isConstant then [.delegate "ConstantFoldCastOperand"] else [.decline]
  | .value _ => [.decline]

/-- `simplifyAndOrOfCmps(Q, Op0, Op1, IsAnd)`, step by step: two compares, or two casts of one kind from `i1`
compares, looked through. Anything else isn't a pair of `ICmpInst`s, after the look through or without it, and
declines. -/
def _root_.Peephole.IS.simplifyAndOrOfCmps.steps (o : Oracle) : {w : Nat} → Term w → Term w → Bool → List (Step w)
  | _, .icmp id0 p0 s0 a0 b0, .icmp id1 p1 s1 a1 b1, isAnd =>
    [fwd (if isAnd then "IS.simplifyAndOfICmps" else "IS.simplifyOrOfICmps")
      (andOrOfICmps o (.icmp id0 p0 s0 a0 b0) (.icmp id1 p1 s1 a1 b1) isAnd)]
  | w, .zext _ _ (.icmp id0 p0 s0 a0 b0), .zext _ _ (.icmp id1 p1 s1 a1 b1), isAnd =>
    castSteps (fun c => c.setWidth w) (andOrOfICmps o (.icmp id0 p0 s0 a0 b0) (.icmp id1 p1 s1 a1 b1) isAnd)
  | w, .sext _ (.icmp id0 p0 s0 a0 b0), .sext _ (.icmp id1 p1 s1 a1 b1), isAnd =>
    castSteps (fun c => c.signExtend w) (andOrOfICmps o (.icmp id0 p0 s0 a0 b0) (.icmp id1 p1 s1 a1 b1) isAnd)
  | w, .trunc _ _ _ (.icmp id0 p0 s0 a0 b0), .trunc _ _ _ (.icmp id1 p1 s1 a1 b1), isAnd =>
    castSteps (fun c => c.setWidth w) (andOrOfICmps o (.icmp id0 p0 s0 a0 b0) (.icmp id1 p1 s1 a1 b1) isAnd)
  | _, _, _, _ => []

def _root_.Peephole.IS.simplifyAndOrOfCmps (o : Oracle) (op0 op1 : Term w) (isAnd : Bool) : Result w :=
  run (simplifyAndOrOfCmps.steps o op0 op1 isAnd)

/-- A cast of an `i1` value: poison for poison, and for a value either poison, as `zext nneg` and `trunc nuw` can be,
or the cast of the value, which commutes with `and` and `or`. -/
structure CastOk (cv : Val 1 → Val w) (fold : BitVec 1 → BitVec w) : Prop where
  ofNone : cv Option.none = Option.none
  ofSome : ∀ x, cv (Option.some x) = Option.none ∨ cv (Option.some x) = Option.some (fold x)
  foldAnd : ∀ x y, fold (x &&& y) = fold x &&& fold y
  foldOr : ∀ x y, fold (x ||| y) = fold x ||| fold y

theorem zext_ok (nneg : Bool) : CastOk (fun a => Val.zext w a nneg) (fun c => c.setWidth w) where
  ofNone := rfl
  ofSome x := by
    simp only [Val.zext]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  foldAnd _ _ := BitVec.setWidth_and
  foldOr x y := Lemmas.setWidth_or x y

theorem sext_ok : CastOk (fun a => Val.sext w a) (fun c => c.signExtend w) where
  ofNone := rfl
  ofSome _ := Or.inr rfl
  foldAnd _ _ := BitVec.signExtend_and
  foldOr x y := Lemmas.signExtend_or x y

theorem trunc_ok (nuw nsw : Bool) : CastOk (fun a => Val.trunc w a nuw nsw) (fun c => c.setWidth w) where
  ofNone := rfl
  ofSome x := by
    simp only [Val.trunc]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
  foldAnd _ _ := BitVec.setWidth_and
  foldOr x y := Lemmas.setWidth_or x y

/-- `IS.simplifyAndOrOfCmps.L1933`: `cast(A) op cast(B)` to `cast(V)` where `A op B` simplified to the constant `V`,
for `op` `and` or `or` and a cast of one kind, folded as `ConstantFoldCastOperand` does. -/
theorem _root_.Peephole.IS.simplifyAndOrOfCmps.L1933 {ρ : Env} {isAnd d : Bool} {a b : Term 1} {op0 op1 : Term w}
    {cv0 cv1 : Val 1 → Val w} {fold : BitVec 1 → BitVec w} (k0 : CastOk cv0 fold) (k1 : CastOk cv1 fold)
    (h0 : op0.denote ρ = cv0 (a.denote ρ)) (h1 : op1.denote ρ = cv1 (b.denote ρ)) {r : Repl 1}
    (hv : Refines ((logicSrc isAnd false a b).eval ρ) (r.eval ρ))
    (hr : r = .poison ∨ ∃ c, r = .const c) {r' : Repl w}
    (hr' : (r = .poison ∧ r' = .poison) ∨ ∃ c, r = .const c ∧ r' = .const (fold c)) :
    Refines ((logicSrc isAnd d op0 op1).eval ρ) (r'.eval ρ) := by
  rw [logicSrc_eval] at hv ⊢
  rw [h0, h1]
  cases ha : a.denote ρ with
  | none =>
    rw [k0.ofNone, logicVal_none_left]
    rcases hr' with ⟨-, rfl⟩ | ⟨c, -, rfl⟩ <;> exact refines_ok (Refine.val_none _)
  | some x =>
  cases hb : b.denote ρ with
  | none =>
    rw [k1.ofNone, logicVal_none_right]
    rcases hr' with ⟨-, rfl⟩ | ⟨c, -, rfl⟩ <;> exact refines_ok (Refine.val_none _)
  | some y =>
  rw [ha, hb, logicVal_plain] at hv
  rcases hr' with ⟨rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · exact absurd ((Refine.outcome_ok_ok _ _).1 hv) (by simp [Refine.val_some])
  · have hc := (Refine.val_some _ _).1 ((Refine.outcome_ok_ok _ _).1 hv)
    simp only [Option.some.injEq] at hc
    refine refines_ok ?_
    rcases k0.ofSome x with hx | hx <;> rw [hx]
    · rw [logicVal_none_left]; exact Refine.val_none _
    rcases k1.ofSome y with hy | hy <;> rw [hy]
    · rw [logicVal_none_right]; exact Refine.val_none _
    rcases logicVal_some isAnd d (fold x) (fold y) with h' | h' <;> rw [h']
    · exact Refine.val_none _
    · rw [hc]
      cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, k0.foldAnd, k0.foldOr] <;>
        exact Refine.refl_val _

theorem castSteps_sound {ρ : Env} {isAnd d : Bool} {a b : Term 1} {op0 op1 : Term w}
    {cv0 cv1 : Val 1 → Val w} {fold : BitVec 1 → BitVec w} (k0 : CastOk cv0 fold) (k1 : CastOk cv1 fold)
    (h0 : op0.denote ρ = cv0 (a.denote ρ)) (h1 : op1.denote ρ = cv1 (b.denote ρ)) {res : Result 1}
    (hres : ∀ r, res = .value r → Refines ((logicSrc isAnd false a b).eval ρ) (r.eval ρ)) :
    ∀ site r', Step.fire site r' ∈ castSteps fold res → Refines ((logicSrc isAnd d op0 op1).eval ρ) (r'.eval ρ) := by
  intro site r' hmem
  unfold castSteps at hmem
  split at hmem
  · simp at hmem
  · simp at hmem
  · next c =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, Step.fire.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact simplifyAndOrOfCmps.L1933 k0 k1 h0 h1 (hres _ rfl) (Or.inr ⟨c, rfl⟩) (Or.inr ⟨c, rfl, rfl⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Step.fire.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact simplifyAndOrOfCmps.L1933 k0 k1 h0 h1 (hres _ rfl) (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)
  · split at hmem <;> simp at hmem
  · simp at hmem

theorem zextCase_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d isAnd : Bool) (id0 id1 : Nat)
    (n0 n1 : Bool) (a b : Term 1) (ca : a.Consistent ρ) (cb : b.Consistent ρ)
    (ha : Val.zext w (a.denote ρ) n0 = ρ w id0) (hb : Val.zext w (b.denote ρ) n1 = ρ w id1) :
    ∀ site r, Step.fire site r ∈ castSteps (fun c => c.setWidth w) (andOrOfICmps o a b isAnd) →
      Refines ((logicSrc isAnd d (.zext id0 n0 a) (.zext id1 n1 b)).eval ρ) (r.eval ρ) :=
  castSteps_sound (w := w) (ρ := ρ) (a := a) (b := b) (op0 := .zext id0 n0 a) (op1 := .zext id1 n1 b) (zext_ok n0)
    (zext_ok n1) ha.symm hb.symm
    (fun _ h => andOrOfICmps_sound ρ o ho false a b isAnd ca cb h)

theorem sextCase_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d isAnd : Bool) (id0 id1 : Nat)
    (a b : Term 1) (ca : a.Consistent ρ) (cb : b.Consistent ρ)
    (ha : Val.sext w (a.denote ρ) = ρ w id0) (hb : Val.sext w (b.denote ρ) = ρ w id1) :
    ∀ site r, Step.fire site r ∈ castSteps (fun c => c.signExtend w) (andOrOfICmps o a b isAnd) →
      Refines ((logicSrc isAnd d (.sext id0 a) (.sext id1 b)).eval ρ) (r.eval ρ) :=
  castSteps_sound (w := w) (ρ := ρ) (a := a) (b := b) (op0 := .sext id0 a) (op1 := .sext id1 b) sext_ok sext_ok ha.symm
    hb.symm
    (fun _ h => andOrOfICmps_sound ρ o ho false a b isAnd ca cb h)

theorem truncCase_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d isAnd : Bool) (id0 id1 : Nat)
    (u0 s0 u1 s1 : Bool) (a b : Term 1) (ca : a.Consistent ρ) (cb : b.Consistent ρ)
    (ha : Val.trunc w (a.denote ρ) u0 s0 = ρ w id0) (hb : Val.trunc w (b.denote ρ) u1 s1 = ρ w id1) :
    ∀ site r, Step.fire site r ∈ castSteps (fun c => c.setWidth w) (andOrOfICmps o a b isAnd) →
      Refines ((logicSrc isAnd d (.trunc id0 u0 s0 a) (.trunc id1 u1 s1 b)).eval ρ) (r.eval ρ) :=
  castSteps_sound (w := w) (ρ := ρ) (a := a) (b := b) (op0 := .trunc id0 u0 s0 a) (op1 := .trunc id1 u1 s1 b)
    (trunc_ok u0 s0) (trunc_ok u1 s1) ha.symm hb.symm
    (fun _ h => andOrOfICmps_sound ρ o ho false a b isAnd ca cb h)

/-- Theorem 1 for `simplifyAndOrOfCmps`: every value the model returns refines `and Op0, Op1` or `or [disjoint] Op0,
Op1`, at every width, poison included, given sound analyses. -/
theorem _root_.Peephole.IS.simplifyAndOrOfCmps.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : Bool)
    (op0 op1 : Term w) (isAnd : Bool) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) {r : Repl w}
    (h : simplifyAndOrOfCmps o op0 op1 isAnd = .value r) :
    Refines ((logicSrc isAnd d op0 op1).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyAndOrOfCmps.steps o op0 op1 isAnd →
      Refines ((logicSrc isAnd d op0 op1).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifyAndOrOfCmps.steps at hmem
  split at hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    exact andOrOfICmps_sound ρ o ho d _ _ isAnd c0 c1 (fwd_fire hmem.symm)
  · obtain ⟨ca, ha⟩ := c0
    obtain ⟨cb, hb⟩ := c1
    exact zextCase_sound ρ o ho d isAnd _ _ _ _ _ _ ca cb ha hb site r hmem
  · obtain ⟨ca, ha⟩ := c0
    obtain ⟨cb, hb⟩ := c1
    exact sextCase_sound ρ o ho d isAnd _ _ _ _ ca cb ha hb site r hmem
  · obtain ⟨ca, ha⟩ := c0
    obtain ⟨cb, hb⟩ := c1
    exact truncCase_sound ρ o ho d isAnd _ _ _ _ _ _ _ _ ca cb ha hb site r hmem
  · simp at hmem

end Peephole.IS.ICmpB
