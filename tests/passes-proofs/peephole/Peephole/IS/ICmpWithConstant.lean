import Peephole.IS.ICmpConstantRange

/-! # InstSimplify's `simplifyICmpWithConstant`, and its rewrites for every input

`simplifyICmpWithConstant` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3104-3153` at `llvmorg-23.1.3`: an `icmp`
against a constant `C`, decided by the range of values the predicate allows against `C`, by the range
`computeConstantRange` gives the left operand, by a multiplication that can't reach `C`, or by `isKnownNonZero`.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpWithConstant.L3120` | `icmp slt (bitcast (uitofp X)), 0` and the like: floating point, not modelled |
| `IS.simplifyICmpWithConstant.L3126` | `icmp p X, C` to false, where no value satisfies `p` against `C` (`ult 0` and the like) |
| `IS.simplifyICmpWithConstant.L3128` | `icmp p X, C` to true, where every value does (`uge 0` and the like) |
| `IS.simplifyICmpWithConstant.L3133` | `icmp p X, C` to true, where `computeConstantRange(X)` is inside the values that satisfy it |
| `IS.simplifyICmpWithConstant.L3135` | `icmp p X, C` to false, where it's outside them |
| `IS.simplifyICmpWithConstant.L3146` | `(mul nuw/nsw X, MulC) == C` to false and `!=` to true, where `C` isn't a multiple of `MulC` |
| `IS.simplifyICmpWithConstant.L3149` | `X >=u 1` to true, where `X` is known non-zero |

The ranges are `ConstantRange`s, `Peephole.IS.ICmp.CR`, and `computeConstantRange` comes from `ICmp.Ext`. The model
reads them only at a positive width: LLVM has no `i0`, where the full and empty ranges are the same pair. -/

namespace Peephole.IS

open IRLean ICmp

variable {w : Nat}

/-! ### Helpers -/

/-- `match(LHS, m_NUWMul(m_Value(), m_APIntAllowPoison(MulC))) && *MulC != 0 && C->urem(*MulC) != 0`. -/
def simplifyICmpWithConstant.nuwMulNotMultiple (lhs : Term w) (c : BitVec w) : Bool :=
  match binop? .mul lhs with
  | some (f, _, m) =>
    f.nuw &&
      match apint m with
      | some mc => mc != 0#w && c % mc != 0#w
      | none => false
  | none => false

/-- `match(LHS, m_NSWMul(m_Value(), m_APIntAllowPoison(MulC))) && *MulC != 0 && C->srem(*MulC) != 0`. -/
def simplifyICmpWithConstant.nswMulNotMultiple (lhs : Term w) (c : BitVec w) : Bool :=
  match binop? .mul lhs with
  | some (f, _, m) =>
    f.nsw &&
      match apint m with
      | some mc => mc != 0#w && c.srem mc != 0#w
      | none => false
  | none => false

/-! ### The model -/

/-- `simplifyICmpWithConstant(Pred, LHS, RHS, Q)`, step by step. `Q.IIQ.UseInstrInfo` is true in InstSimplify's
queries. -/
def simplifyICmpWithConstant.steps (o : Oracle) (e : Ext) (p : Pred) (lhs rhs : Term w) : List (Step 1) :=
  match apint rhs with
  | none => [.decline]
  | some c =>
    -- ConstantRange::makeExactICmpRegion(Pred, *C), and computeConstantRange(LHS, CmpInst::isSigned(Pred), Q)
    let rhsCR := CR.makeExactICmpRegion p c
    let lhsCR := e.constRange (isSigned p) lhs
    [ -- Sign-bit checks can be optimized to true/false after unsigned floating-point casts: `Term` has no
      -- floating point, so `m_ElementWiseBitCast(m_UIToFP(m_Value(X)))` never matches.
      .next,
      -- Rule out tautological comparisons (eg., ult 0 or uge 0).
      if w != 0 && rhsCR.isEmptySet then .fire "IS.simplifyICmpWithConstant.L3126" getFalse else .next,
      if w != 0 && rhsCR.isFullSet then .fire "IS.simplifyICmpWithConstant.L3128" getTrue else .next,
      -- if (!LHS_CR.isFullSet()) { if (RHS_CR.contains(LHS_CR)) return getTrue
      if w != 0 && !lhsCR.isFullSet && rhsCR.containsRange lhsCR then
        .fire "IS.simplifyICmpWithConstant.L3133" getTrue
      else .next,
      -- if (RHS_CR.inverse().contains(LHS_CR)) return getFalse
      if w != 0 && !lhsCR.isFullSet && rhsCR.inverse.containsRange lhsCR then
        .fire "IS.simplifyICmpWithConstant.L3135" getFalse
      else .next,
      -- (mul nuw/nsw X, MulC) != C --> true  (if C is not a multiple of MulC)
      -- (mul nuw/nsw X, MulC) == C --> false (if C is not a multiple of MulC)
      if isEquality p && (nuwMulNotMultiple lhs c || nswMulNotMultiple lhs c) then
        .fire "IS.simplifyICmpWithConstant.L3146" (getBool (p == .ne))
      else .next,
      if p == .uge && c == 1#w && o.nonZero lhs then .fire "IS.simplifyICmpWithConstant.L3149" getTrue else .next ]

def simplifyICmpWithConstant (o : Oracle) (e : Ext) (p : Pred) (lhs rhs : Term w) : Result 1 :=
  run (simplifyICmpWithConstant.steps o e p lhs rhs)

/-! ### The rewrites, one theorem each -/

/-- `IS.simplifyICmpWithConstant.L3126`: `icmp p X, C` to false, where `makeExactICmpRegion(p, C)` is empty. -/
theorem simplifyICmpWithConstant.L3126 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (hw : 0 < w) (hc : apint rhs = some c) (he : (CR.makeExactICmpRegion p c).isEmptySet = true) :
    Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [apint_denote hc] at hy; cases hy
  rw [← CR.makeExact_contains hw, CR.isEmptySet_contains hw he]

/-- `IS.simplifyICmpWithConstant.L3128`: `icmp p X, C` to true, where `makeExactICmpRegion(p, C)` is full. -/
theorem simplifyICmpWithConstant.L3128 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (hw : 0 < w) (hc : apint rhs = some c) (hf : (CR.makeExactICmpRegion p c).isFullSet = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [apint_denote hc] at hy; cases hy
  rw [← CR.makeExact_contains hw, CR.isFullSet_contains hf]

/-- `IS.simplifyICmpWithConstant.L3133`: `icmp p X, C` to true, where `computeConstantRange(X)` is inside
`makeExactICmpRegion(p, C)`. -/
theorem simplifyICmpWithConstant.L3133 (ρ : Env) (e : Ext) (he : e.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (c : BitVec w) (hw : 0 < w) (hc : apint rhs = some c)
    (h : (CR.makeExactICmpRegion p c).containsRange (e.constRange (isSigned p) lhs) = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [apint_denote hc] at hy; cases hy
  rw [← CR.makeExact_contains hw]
  exact CR.containsRange_sound hw h (he.constRange _ lhs x hx)

/-- `IS.simplifyICmpWithConstant.L3135`: `icmp p X, C` to false, where `computeConstantRange(X)` is inside the
inverse of `makeExactICmpRegion(p, C)`. -/
theorem simplifyICmpWithConstant.L3135 (ρ : Env) (e : Ext) (he : e.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (c : BitVec w) (hw : 0 < w) (hc : apint rhs = some c)
    (h : (CR.makeExactICmpRegion p c).inverse.containsRange (e.constRange (isSigned p) lhs) = true) :
    Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [apint_denote hc] at hy; cases hy
  rw [← CR.makeExact_contains hw]
  exact CR.inverse_contains hw (CR.containsRange_sound hw h (he.constRange _ lhs x hx))

namespace ICmp

theorem mul_some {a b : Val w} {nuw nsw : Bool} {z : BitVec w} (h : Val.mul a b nuw nsw = some z) :
    ∃ x y, a = some x ∧ b = some y ∧ (nuw = true → x.umulOverflow y = false) ∧
      (nsw = true → x.smulOverflow y = false) ∧ z = x * y := by
  cases a <;> cases b <;> simp only [Val.mul, reduceCtorEq] at h
  next x y =>
  split at h
  · cases h
  · next hc =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, not_or, not_and, Bool.not_eq_true] at hc
    exact ⟨x, y, rfl, rfl, hc.1, hc.2, (Option.some.inj h).symm⟩

/-- The value of an `icmp` operand that `nuwMulNotMultiple` or `nswMulNotMultiple` matches isn't `C`. -/
theorem mulNotMultiple_ne {ρ : Env} {lhs : Term w} {c x : BitVec w} (hc : lhs.Consistent ρ)
    (h : (simplifyICmpWithConstant.nuwMulNotMultiple lhs c || simplifyICmpWithConstant.nswMulNotMultiple lhs c) = true)
    (hx : lhs.denote ρ = some x) : x ≠ c := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold simplifyICmpWithConstant.nuwMulNotMultiple at h
    split at h
    · next f a m hm =>
      simp only [Bool.and_eq_true] at h
      split at h
      · next mc hmc =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        have hd := ok_inj (binop?_consistent hm hc).2.2
        rw [hx, apint_denote hmc] at hd
        obtain ⟨a', b', -, hb, hov, -, rfl⟩ := mul_some hd
        cases hb
        exact Lemmas.mul_ne_of_umod_ne (hov h.1) h.2.2
      · simp at h
    · cases h
  · unfold simplifyICmpWithConstant.nswMulNotMultiple at h
    split at h
    · next f a m hm =>
      simp only [Bool.and_eq_true] at h
      split at h
      · next mc hmc =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        have hd := ok_inj (binop?_consistent hm hc).2.2
        rw [hx, apint_denote hmc] at hd
        obtain ⟨a', b', -, hb, -, hov, rfl⟩ := mul_some hd
        cases hb
        exact Lemmas.mul_ne_of_srem_ne (hov h.1) h.2.2
      · simp at h
    · cases h

end ICmp

/-- `IS.simplifyICmpWithConstant.L3146`: `(mul nuw X, MulC) == C` and `(mul nsw X, MulC) == C` to false, and `!=` to
true, where `C` isn't a multiple of `MulC`, unsigned or signed. -/
theorem simplifyICmpWithConstant.L3146 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) (c : BitVec w)
    (c0 : lhs.Consistent ρ) (hc : apint rhs = some c) (hp : isEquality p = true)
    (h : (nuwMulNotMultiple lhs c || nswMulNotMultiple lhs c) = true) :
    Refines ((src p s lhs rhs).eval ρ) ((getBool (p == .ne)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [apint_denote hc] at hy; cases hy
  have hne := mulNotMultiple_ne c0 h hx
  cases p <;> simp only [isEquality, Bool.false_eq_true] at hp
  · show (x == c) = false
    simpa using hne
  · show (x != c) = true
    simpa using hne

/-- `IS.simplifyICmpWithConstant.L3149`: `X >=u 1` to true, where `X` is known non-zero. -/
theorem simplifyICmpWithConstant.L3149 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (s : Bool) (lhs rhs : Term w)
    (hc : apint rhs = some 1#w) (hnz : o.nonZero lhs = true) :
    Refines ((src .uge s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [apint_denote hc] at hy; cases hy
  have hne := ho.nonZero lhs x hnz hx
  have : 0 < x.toNat := by
    refine Nat.pos_of_ne_zero fun h0 => hne (BitVec.eq_of_toNat_eq ?_)
    simp [h0]
  have := Nat.mod_le 1 (2 ^ w)
  simp only [test, BitVec.ule_eq_decide, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

/-! ### The fold -/

/-- Every step of `simplifyICmpWithConstant` that fires is right. -/
theorem simplifyICmpWithConstant.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ)
    (p : Pred) (s : Bool) (lhs rhs : Term w) (c0 : lhs.Consistent ρ) :
    ∀ site r, Step.fire site r ∈ simplifyICmpWithConstant.steps o e p lhs rhs →
      Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  unfold steps at hmem
  split at hmem
  · simp at hmem
  · next c hc =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h
    · cases h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
      exact L3126 ρ p s lhs rhs c (Nat.pos_of_ne_zero hcond.1) hc hcond.2
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
      exact L3128 ρ p s lhs rhs c (Nat.pos_of_ne_zero hcond.1) hc hcond.2
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
      exact L3133 ρ e he p s lhs rhs c (Nat.pos_of_ne_zero hcond.1.1) hc hcond.2
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
      exact L3135 ρ e he p s lhs rhs c (Nat.pos_of_ne_zero hcond.1.1) hc hcond.2
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true] at hcond
      exact L3146 ρ p s lhs rhs c c0 hc hcond.1 hcond.2
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hcond =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨rfl, rfl⟩, hnz⟩ := hcond
      exact L3149 ρ o ho s lhs rhs hc hnz

/-- Theorem 1 for `simplifyICmpWithConstant`: every value the model returns refines the `icmp`, with or without
`samesign`, at every width, in every run its operands are consistent with, poison included, given sound analyses,
`computeConstantRange` among them. -/
theorem simplifyICmpWithConstant.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (e : Ext) (he : e.Sound ρ)
    (p : Pred) (s : Bool) (lhs rhs : Term w) (c0 : lhs.Consistent ρ) {r : Repl 1}
    (h : simplifyICmpWithConstant o e p lhs rhs = .value r) : Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) :=
  run_sound (steps_sound ρ o ho e he p s lhs rhs c0) h

end Peephole.IS
