import Peephole.IS.ICmpBase

/-! # InstSimplify's `simplifyICmpWithZero`, and its rewrites for every input

`simplifyICmpWithZero` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3043-3101` at `llvmorg-23.1.3`, with
`matchEquivZeroRHS` before it: an `icmp` against 0, or against -1 or 1 where that's a comparison against 0 with
another predicate, decided from what `isKnownNonZero` and `computeKnownBits` say about the left operand.

| ID | Rewrite, after `matchEquivZeroRHS` |
| --- | --- |
| `IS.simplifyICmpWithZero.L3054` | `X <u 0` to false |
| `IS.simplifyICmpWithZero.L3056` | `X >=u 0` to true |
| `IS.simplifyICmpWithZero.L3060` | `X == 0` and `X <=u 0` to false, where `X` is known non-zero |
| `IS.simplifyICmpWithZero.L3065` | `X != 0` and `X >u 0` to true, where `X` is known non-zero |
| `IS.simplifyICmpWithZero.L3070` | `X <s 0` to true, where `X` is known negative |
| `IS.simplifyICmpWithZero.L3072` | `X <s 0` to false, where `X` is known non-negative |
| `IS.simplifyICmpWithZero.L3078` | `X <=s 0` to true, where `X` is known negative |
| `IS.simplifyICmpWithZero.L3080` | `X <=s 0` to false, where `X` is known non-negative and non-zero |
| `IS.simplifyICmpWithZero.L3086` | `X >=s 0` to false, where `X` is known negative |
| `IS.simplifyICmpWithZero.L3088` | `X >=s 0` to true, where `X` is known non-negative |
| `IS.simplifyICmpWithZero.L3094` | `X >s 0` to false, where `X` is known negative |
| `IS.simplifyICmpWithZero.L3096` | `X >s 0` to true, where `X` is known non-negative and non-zero |

`KnownBits::isNegative` is the sign bit of the known ones, and `isNonNegative` that of the known zeros.

`m_Zero` matches a null pointer too, so a compare of a pointer against null reaches every step here, and `Term` has
no pointers: the theorems prove the integer instance, not every input, and `folds/is-icmp.json` lists each site
unproved. -/

namespace Peephole.IS

open IRLean ICmp

variable {w : Nat}

/-! ### Helpers -/

/-- `matchEquivZeroRHS(Pred, RHS)`: the predicate `Pred` becomes if `icmp Pred X, RHS` is a comparison against 0,
or none. `m_AllOnes` is tried before `m_One`, which matters in `i1`, where they're the same constant. -/
def simplifyICmpWithZero.matchEquivZeroRHS (p : Pred) (rhs : Term w) : Option Pred :=
  -- icmp [pred] X, 0 --> as-is
  if zero rhs then some p
  -- Handle comparisons with -1 (all ones)
  else if allOnes rhs then
    match p with
    | .sgt => some .sge -- icmp sgt X, -1 --> icmp sge X, 0
    | .sle => some .slt -- icmp sle X, -1 --> icmp slt X, 0
    | _ => none
  -- Handle comparisons with 1
  else if one rhs then
    match p with
    | .sge => some .sgt -- icmp sge X, 1 --> icmp sgt X, 0
    | .uge => some .ugt -- icmp uge X, 1 --> icmp ugt X, 0
    | .slt => some .sle -- icmp slt X, 1 --> icmp sle X, 0
    | .ult => some .ule -- icmp ult X, 1 --> icmp ule X, 0
    | _ => none
  else none

namespace ICmp

theorem cst_ne {t : Term w} {c d : BitVec w} (h : cst (· == c) t = true) (hn : cst (· == d) t = false) : c ≠ d := by
  intro he
  subst he
  rw [h] at hn
  cases hn

theorem pos_of_allOnes_ne_zero (h : BitVec.allOnes w ≠ 0#w) : 0 < w := by
  cases w
  · exact absurd rfl h
  · omega

theorem one_lt_of_one_ne (h0 : 1#w ≠ 0#w) (h1 : 1#w ≠ BitVec.allOnes w) : 1 < w := by
  rcases w with _ | _ | w
  · exact absurd rfl h0
  · exact absurd rfl h1
  · omega

/-- What `matchEquivZeroRHS` says: `icmp Pred X, RHS` is `icmp Pred' X, 0` on every value of `X`. -/
theorem matchEquivZeroRHS_test {ρ : Env} {p p' : Pred} {rhs : Term w}
    (hm : simplifyICmpWithZero.matchEquivZeroRHS p rhs = some p') {y : BitVec w} (hy : rhs.denote ρ = some y)
    (x : BitVec w) : test p x y = test p' x 0#w := by
  unfold simplifyICmpWithZero.matchEquivZeroRHS at hm
  split at hm
  · next hz =>
    cases hm
    rw [cst_eq hz] at hy; cases hy; rfl
  · next hz =>
    have hz' : zero rhs = false := by simpa using hz
    split at hm
    · next ha =>
      rw [cst_eq ha] at hy; cases hy
      have hw := pos_of_allOnes_ne_zero (cst_ne ha (by
        have : cst (· == 0#w) rhs = false := hz'
        exact this))
      split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm <;> subst hm
      · exact Lemmas.allOnes_slt x hw
      · exact Lemmas.sle_allOnes x hw
    · next ha =>
      have ha' : allOnes rhs = false := by simpa using ha
      split at hm
      · next ho =>
        rw [cst_eq ho] at hy; cases hy
        have h0 : (1#w) ≠ 0#w := cst_ne ho hz'
        have h1 : (1#w) ≠ BitVec.allOnes w := cst_ne ho ha'
        have hw := one_lt_of_one_ne h0 h1
        split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm <;> subst hm
        · exact Lemmas.one_sle x hw
        · exact Lemmas.one_ule x (by omega)
        · exact Lemmas.slt_one x hw
        · exact Lemmas.ult_one x (by omega)
      · cases hm

theorem ne_zero_iff_toNat {x : BitVec w} : x ≠ 0#w ↔ 0 < x.toNat := by
  rw [Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]; omega

/-- What the oracle's known bits say about the sign. -/
theorem msb_of_knownOne {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {t : Term w} {x : BitVec w}
    (hx : t.denote ρ = some x) (h : (o.knownOne t).msb = true) : x.msb = true :=
  Lemmas.msb_true_of_and_eq (ho.knownOne t x hx) h

theorem msb_of_knownZero {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {t : Term w} {x : BitVec w}
    (hx : t.denote ρ = some x) (h : (o.knownZero t).msb = true) : x.msb = false :=
  Lemmas.msb_false_of_and_eq_zero (ho.knownZero t x hx) h

end ICmp

/-! ### The model -/

/-- `simplifyICmpWithZero(Pred, LHS, RHS, Q)`, step by step: after `matchEquivZeroRHS`, a step for each `return` in
its switch on the predicate. -/
def simplifyICmpWithZero.steps (o : Oracle) (p : Pred) (lhs rhs : Term w) : List (Step 1) :=
  -- Check if RHS is zero or can be transformed to an equivalent zero comparison
  match matchEquivZeroRHS p rhs with
  | none => [.decline]
  | some p =>
    -- KnownBits::isNegative and isNonNegative of computeKnownBits(LHS, Q)
    let isNegative := (o.knownOne lhs).msb
    let isNonNegative := (o.knownZero lhs).msb
    [ -- case ICmpInst::ICMP_ULT: return getFalse(ITy);
      if p == .ult then .fire "IS.simplifyICmpWithZero.L3054" getFalse else .next,
      -- case ICmpInst::ICMP_UGE: return getTrue(ITy);
      if p == .uge then .fire "IS.simplifyICmpWithZero.L3056" getTrue else .next,
      -- case ICmpInst::ICMP_EQ: case ICmpInst::ICMP_ULE: if (isKnownNonZero(LHS, Q)) return getFalse(ITy);
      if (p == .eq || p == .ule) && o.nonZero lhs then .fire "IS.simplifyICmpWithZero.L3060" getFalse else .next,
      -- case ICmpInst::ICMP_NE: case ICmpInst::ICMP_UGT: if (isKnownNonZero(LHS, Q)) return getTrue(ITy);
      if (p == .ne || p == .ugt) && o.nonZero lhs then .fire "IS.simplifyICmpWithZero.L3065" getTrue else .next,
      -- case ICmpInst::ICMP_SLT
      if p == .slt && isNegative then .fire "IS.simplifyICmpWithZero.L3070" getTrue else .next,
      if p == .slt && isNonNegative then .fire "IS.simplifyICmpWithZero.L3072" getFalse else .next,
      -- case ICmpInst::ICMP_SLE
      if p == .sle && isNegative then .fire "IS.simplifyICmpWithZero.L3078" getTrue else .next,
      if p == .sle && isNonNegative && o.nonZero lhs then .fire "IS.simplifyICmpWithZero.L3080" getFalse
      else .next,
      -- case ICmpInst::ICMP_SGE
      if p == .sge && isNegative then .fire "IS.simplifyICmpWithZero.L3086" getFalse else .next,
      if p == .sge && isNonNegative then .fire "IS.simplifyICmpWithZero.L3088" getTrue else .next,
      -- case ICmpInst::ICMP_SGT
      if p == .sgt && isNegative then .fire "IS.simplifyICmpWithZero.L3094" getFalse else .next,
      if p == .sgt && isNonNegative && o.nonZero lhs then .fire "IS.simplifyICmpWithZero.L3096" getTrue
      else .next ]

def simplifyICmpWithZero (o : Oracle) (p : Pred) (lhs rhs : Term w) : Result 1 :=
  run (simplifyICmpWithZero.steps o p lhs rhs)

/-! ### The rewrites, one theorem each

Each takes `matchEquivZeroRHS`'s answer `p'` and the facts its step tests. -/

/-- `IS.simplifyICmpWithZero.L3054`: `X <u 0` to false. -/
theorem simplifyICmpWithZero.L3054 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (hm : matchEquivZeroRHS p rhs = some .ult) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [matchEquivZeroRHS_test hm hy]
  simp [test, BitVec.ult_eq_decide]

/-- `IS.simplifyICmpWithZero.L3056`: `X >=u 0` to true. -/
theorem simplifyICmpWithZero.L3056 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (hm : matchEquivZeroRHS p rhs = some .uge) : Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [matchEquivZeroRHS_test hm hy]
  simp [test, BitVec.ule_eq_decide]

/-- `IS.simplifyICmpWithZero.L3060`: `X == 0` and `X <=u 0` to false, where `X` is known non-zero. -/
theorem simplifyICmpWithZero.L3060 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p p' : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some p') (hp : p' = .eq ∨ p' = .ule)
    (hnz : o.nonZero lhs = true) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy]
  have := ne_zero_iff_toNat.1 (ho.nonZero lhs x hnz hx)
  rcases hp with rfl | rfl
  · simp [test, BitVec.toNat_eq]; omega
  · simp [test, BitVec.ule_eq_decide]; omega

/-- `IS.simplifyICmpWithZero.L3065`: `X != 0` and `X >u 0` to true, where `X` is known non-zero. -/
theorem simplifyICmpWithZero.L3065 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p p' : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some p') (hp : p' = .ne ∨ p' = .ugt)
    (hnz : o.nonZero lhs = true) : Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy]
  have := ne_zero_iff_toNat.1 (ho.nonZero lhs x hnz hx)
  rcases hp with rfl | rfl
  · simp [test, BitVec.toNat_eq]; omega
  · simp [test, BitVec.ult_eq_decide]; omega

/-- `IS.simplifyICmpWithZero.L3070`: `X <s 0` to true, where `X` is known negative. -/
theorem simplifyICmpWithZero.L3070 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .slt) (hn : (o.knownOne lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.slt_zero_eq_msb, msb_of_knownOne ho hx hn]

/-- `IS.simplifyICmpWithZero.L3072`: `X <s 0` to false, where `X` is known non-negative. -/
theorem simplifyICmpWithZero.L3072 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .slt) (hn : (o.knownZero lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.slt_zero_eq_msb, msb_of_knownZero ho hx hn]

/-- `IS.simplifyICmpWithZero.L3078`: `X <=s 0` to true, where `X` is known negative. -/
theorem simplifyICmpWithZero.L3078 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sle) (hn : (o.knownOne lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.sle_eq_slt_or_eq, BitVec.slt_zero_eq_msb,
    msb_of_knownOne ho hx hn, Bool.true_or]

/-- `IS.simplifyICmpWithZero.L3080`: `X <=s 0` to false, where `X` is known non-negative and non-zero. -/
theorem simplifyICmpWithZero.L3080 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sle) (hn : (o.knownZero lhs).msb = true)
    (hnz : o.nonZero lhs = true) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.sle_eq_slt_or_eq, BitVec.slt_zero_eq_msb,
    msb_of_knownZero ho hx hn, Bool.false_or]
  simpa using ho.nonZero lhs x hnz hx

/-- `IS.simplifyICmpWithZero.L3086`: `X >=s 0` to false, where `X` is known negative. -/
theorem simplifyICmpWithZero.L3086 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sge) (hn : (o.knownOne lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.zero_sle_eq_not_msb, msb_of_knownOne ho hx hn, Bool.not_true]

/-- `IS.simplifyICmpWithZero.L3088`: `X >=s 0` to true, where `X` is known non-negative. -/
theorem simplifyICmpWithZero.L3088 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sge) (hn : (o.knownZero lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test, BitVec.zero_sle_eq_not_msb, msb_of_knownZero ho hx hn, Bool.not_false]

/-- `IS.simplifyICmpWithZero.L3094`: `X >s 0` to false, where `X` is known negative. -/
theorem simplifyICmpWithZero.L3094 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sgt) (hn : (o.knownOne lhs).msb = true) :
    Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test]
  have h := BitVec.zero_sle_eq_not_msb (x := x)
  rw [msb_of_knownOne ho hx hn, Bool.not_true, BitVec.sle_eq_slt_or_eq] at h
  simp only [Bool.or_eq_false_iff] at h
  exact h.1

/-- `IS.simplifyICmpWithZero.L3096`: `X >s 0` to true, where `X` is known non-negative and non-zero. -/
theorem simplifyICmpWithZero.L3096 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (hm : matchEquivZeroRHS p rhs = some .sgt) (hn : (o.knownZero lhs).msb = true)
    (hnz : o.nonZero lhs = true) : Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  rw [matchEquivZeroRHS_test hm hy, test]
  have h := BitVec.zero_sle_eq_not_msb (x := x)
  rw [msb_of_knownZero ho hx hn, Bool.not_false, BitVec.sle_eq_slt_or_eq] at h
  have hne : (0#w == x) = false := by
    rw [beq_eq_false_iff_ne]; exact fun he => (ho.nonZero lhs x hnz hx) he.symm
  rw [hne, Bool.or_false] at h
  exact h

/-! ### The fold -/

/-- Every step of `simplifyICmpWithZero` that fires is right. -/
theorem simplifyICmpWithZero.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) :
    ∀ site r, Step.fire site r ∈ simplifyICmpWithZero.steps o p lhs rhs →
      Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  unfold steps at hmem
  split at hmem
  · simp at hmem
  · next p' hm =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;>
      (split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h) <;>
      (obtain ⟨-, rfl⟩ := h) <;> rename_i hc <;>
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    · subst hc; exact L3054 ρ p s lhs rhs hm
    · subst hc; exact L3056 ρ p s lhs rhs hm
    · exact L3060 ρ o ho p p' s lhs rhs hm hc.1 hc.2
    · exact L3065 ρ o ho p p' s lhs rhs hm hc.1 hc.2
    · obtain ⟨rfl, hc⟩ := hc; exact L3070 ρ o ho p s lhs rhs hm hc
    · obtain ⟨rfl, hc⟩ := hc; exact L3072 ρ o ho p s lhs rhs hm hc
    · obtain ⟨rfl, hc⟩ := hc; exact L3078 ρ o ho p s lhs rhs hm hc
    · obtain ⟨⟨rfl, hc⟩, hz⟩ := hc; exact L3080 ρ o ho p s lhs rhs hm hc hz
    · obtain ⟨rfl, hc⟩ := hc; exact L3086 ρ o ho p s lhs rhs hm hc
    · obtain ⟨rfl, hc⟩ := hc; exact L3088 ρ o ho p s lhs rhs hm hc
    · obtain ⟨rfl, hc⟩ := hc; exact L3094 ρ o ho p s lhs rhs hm hc
    · obtain ⟨⟨rfl, hc⟩, hz⟩ := hc; exact L3096 ρ o ho p s lhs rhs hm hc hz

/-- Theorem 1 for `simplifyICmpWithZero`: every value the model returns refines the `icmp`, with or without
`samesign`, at every width, in every run, poison included, given sound analyses. -/
theorem simplifyICmpWithZero.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) {r : Repl 1} (h : simplifyICmpWithZero o p lhs rhs = .value r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) :=
  run_sound (steps_sound ρ o ho p s lhs rhs) h

end Peephole.IS
