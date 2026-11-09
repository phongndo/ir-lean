import Peephole.IS.ICmpBase

/-! # InstSimplify's `simplifyICmpOfBools`, and its rewrites for every input

`simplifyICmpOfBools` is at `llvm/lib/Analysis/InstructionSimplify.cpp:2885-2982` at `llvmorg-23.1.3`: an `icmp` of
two `i1`s, against 0 or 1, or where one operand implies the other. `simplifyICmpInst` calls it on every `icmp`, after
putting a lone constant on the right.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpOfBools.L2908` | `X != 0`, `X >u 0` and `X <s 0` to `X` |
| `IS.simplifyICmpOfBools.ExtractNotLHS.L2899` | `not(X) == 0`, `<=u 0`, `>=s 0`, `!= 1`, `<u 1` and `>s 1` to `X` |
| `IS.simplifyICmpOfBools.L2919` | `X <u 0` and `X >s 0` to false |
| `IS.simplifyICmpOfBools.L2923` | `X >=u 0` and `X <=s 0` to true |
| `IS.simplifyICmpOfBools.L2933` | `X == 1`, `X >=u 1` and `X <=s 1` to `X` |
| `IS.simplifyICmpOfBools.L2944` | `X >u 1` and `X <s 1` to false |
| `IS.simplifyICmpOfBools.L2948` | `X <=u 1` and `X >=s 1` to true |
| `IS.simplifyICmpOfBools.L2960` | `X >=u Y` to true, where `Y` implies `X` |
| `IS.simplifyICmpOfBools.L2971` | `X >=s Y` to true, where `X` implies `Y` |
| `IS.simplifyICmpOfBools.L2975` | `X <=u Y` to true, where `X` implies `Y` |
| `IS.simplifyICmpOfBools.L2980` | `X <=s Y` to true, where `Y` implies `X` |

In `i1`, 1 is -1, so `<=s 1` is `<=s -1`. `ExtractNotLHS` is the lambda that matches `not(X)`; the rewrite through
it is its `return X`, whichever of the six cases called it. -/

namespace Peephole.IS

open IRLean ICmp

/-! ### Helpers -/

/-- The lambda `ExtractNotLHS` in `simplifyICmpOfBools`: `X` if `V` is `m_Not(m_Value(X))`. -/
def simplifyICmpOfBools.ExtractNotLHS (v : Term 1) : Option (Term 1) := not? v

namespace ICmp

theorem bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have h : x.toNat < 2 := by simpa using x.isLt
  have : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases this with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
  · exact Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))

theorem allOnes_one : BitVec.allOnes 1 = 1#1 := rfl

/-- What `m_Not(m_Value(X))` says about values: the operand is `X` with its bit flipped. -/
theorem not?_denote {ρ : Env} {t x : Term 1} (h : not? t = some x) (hc : t.Consistent ρ) :
    t.denote ρ = Val.xor (x.denote ρ) (some 1#1) := by
  unfold not? at h
  split at h
  · next f a b hx =>
    have hd := (ok_inj (binop?_consistent hx hc).2.2).symm
    split at h
    · next ha =>
      cases h
      rw [hd, cst_eq ha]
      cases x.denote ρ <;> simp [Val.xor, Val.map₂, BitVec.xor_comm, allOnes_one]
    · split at h
      · next hb =>
        cases h
        rw [hd, cst_eq hb, allOnes_one]
      · cases h
  · cases h
where
  cst_eq {ρ : Env} {t : Term 1} {c : BitVec 1} (h : cst (· == c) t = true) : t.denote ρ = some c := by
    obtain ⟨c', hc', hd⟩ := cst_denote (ρ := ρ) h
    simp only [beq_iff_eq] at hc'
    rw [hd, hc']

end ICmp

/-! ### The model -/

/-- `simplifyICmpOfBools` on `i1` operands, a step for each statement that can end it. -/
def simplifyICmpOfBools.boolSteps (o : Oracle) (p : Pred) (lhs rhs : Term 1) : List (Step 1) :=
  [ -- X !=  0 -> X;  X >u  0 -> X;  X <s  0 -> X
    if zero rhs && (p == .ne || p == .ugt || p == .slt) then .fire "IS.simplifyICmpOfBools.L2908" (.old lhs)
    else .next,
    -- not(X) ==  0 -> X != 0 -> X;  not(X) <=u 0 -> X >u 0 -> X;  not(X) >=s 0 -> X <s 0 -> X
    if zero rhs && (p == .eq || p == .ule || p == .sge) then
      match ExtractNotLHS lhs with
      | some x => .fire "IS.simplifyICmpOfBools.ExtractNotLHS.L2899" (.old x)
      | none => .next
    else .next,
    -- X <u  0 -> false;  X >s  0 -> false
    if zero rhs && (p == .ult || p == .sgt) then .fire "IS.simplifyICmpOfBools.L2919" getFalse else .next,
    -- X >=u 0 -> true;  X <=s 0 -> true
    if zero rhs && (p == .uge || p == .sle) then .fire "IS.simplifyICmpOfBools.L2923" getTrue else .next,
    -- X ==   1 -> X;  X >=u  1 -> X;  X <=s -1 -> X
    if !zero rhs && one rhs && (p == .eq || p == .uge || p == .sle) then
      .fire "IS.simplifyICmpOfBools.L2933" (.old lhs)
    else .next,
    -- not(X) !=  1 -> X ==   1 -> X;  not(X) <=u 1 -> X >=u  1 -> X;  not(X) >s  1 -> X <=s -1 -> X
    if !zero rhs && one rhs && (p == .ne || p == .ult || p == .sgt) then
      match ExtractNotLHS lhs with
      | some x => .fire "IS.simplifyICmpOfBools.ExtractNotLHS.L2899" (.old x)
      | none => .next
    else .next,
    -- X >u   1 -> false;  X <s  -1 -> false
    if !zero rhs && one rhs && (p == .ugt || p == .slt) then .fire "IS.simplifyICmpOfBools.L2944" getFalse
    else .next,
    -- X <=u  1 -> true;  X >=s -1 -> true
    if !zero rhs && one rhs && (p == .ule || p == .sge) then .fire "IS.simplifyICmpOfBools.L2948" getTrue
    else .next,
    -- ICMP_UGE: if (isImpliedCondition(RHS, LHS, Q.DL).value_or(false))
    if p == .uge && o.implies rhs lhs == some true then .fire "IS.simplifyICmpOfBools.L2960" getTrue else .next,
    -- ICMP_SGE: for signed comparison, the values for an i1 are 0 and -1 ...
    if p == .sge && o.implies lhs rhs == some true then .fire "IS.simplifyICmpOfBools.L2971" getTrue else .next,
    -- ICMP_ULE
    if p == .ule && o.implies lhs rhs == some true then .fire "IS.simplifyICmpOfBools.L2975" getTrue else .next,
    -- ICMP_SLE: SLE follows the same logic as SGE with the LHS and RHS swapped.
    if p == .sle && o.implies rhs lhs == some true then .fire "IS.simplifyICmpOfBools.L2980" getTrue else .next ]

/-- `simplifyICmpOfBools(Pred, LHS, RHS, Q)`, step by step. Its first statement, `if
(!OpTy->isIntOrIntVectorTy(1)) return nullptr;`, is the choice between the two lists: the rest only runs on `i1`. -/
def simplifyICmpOfBools.steps (o : Oracle) (p : Pred) {w : Nat} (lhs rhs : Term w) : List (Step 1) :=
  if h : w = 1 then boolSteps o p (h ▸ lhs) (h ▸ rhs) else [.decline]

def simplifyICmpOfBools (o : Oracle) (p : Pred) {w : Nat} (lhs rhs : Term w) : Result 1 :=
  run (simplifyICmpOfBools.steps o p lhs rhs)

/-! ### The rewrites, one theorem each -/

namespace ICmp

theorem cst_one {ρ : Env} {t : Term 1} (h : one t = true) : t.denote ρ = some 1#1 := not?_denote.cst_eq h
theorem cst_zero {ρ : Env} {t : Term 1} (h : zero t = true) : t.denote ρ = some 0#1 := not?_denote.cst_eq h

end ICmp

/-- `IS.simplifyICmpOfBools.L2908`: `X != 0`, `X >u 0` and `X <s 0` to `X`, in `i1`. -/
theorem simplifyICmpOfBools.L2908 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (hz : zero rhs = true)
    (hp : p = .ne ∨ p = .ugt ∨ p = .slt) : Refines ((src p s lhs rhs).eval ρ) ((Repl.old lhs).eval ρ) := by
  rw [src_eval, Repl.eval_old, cst_zero hz]
  refine refines_ok (eval_refines fun x y hx hy => ?_)
  cases hy
  rw [hx]
  rcases hp with rfl | rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- The six cases that return `ExtractNotLHS(LHS)`: against 0, `==`, `<=u` and `>=s`; against 1, `!=`, `<u` and
`>s`. -/
def simplifyICmpOfBools.notCases (p : Pred) (rhs : Term 1) : Prop :=
  (zero rhs = true ∧ (p = .eq ∨ p = .ule ∨ p = .sge)) ∨ (one rhs = true ∧ (p = .ne ∨ p = .ult ∨ p = .sgt))

/-- `IS.simplifyICmpOfBools.ExtractNotLHS.L2899`: `not(X) == 0`, `not(X) <=u 0`, `not(X) >=s 0`, `not(X) != 1`,
`not(X) <u 1` and `not(X) >s 1` to `X`, in `i1`. -/
theorem simplifyICmpOfBools.ExtractNotLHS.L2899 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs x : Term 1)
    (c0 : lhs.Consistent ρ) (hp : simplifyICmpOfBools.notCases p rhs) (hx : ExtractNotLHS lhs = some x) :
    Refines ((src p s lhs rhs).eval ρ) ((Repl.old x).eval ρ) := by
  rw [src_eval, Repl.eval_old, not?_denote hx c0]
  refine refines_ok (eval_refines fun a b ha hb => ?_)
  cases hxd : x.denote ρ with
  | none => rw [hxd] at ha; simp [Val.xor, Val.map₂] at ha
  | some a' =>
  rw [hxd] at ha
  simp only [Val.xor, Val.map₂, Option.some.injEq] at ha
  subst ha
  rcases hp with ⟨hz, hp⟩ | ⟨ho, hp⟩
  · rw [cst_zero hz] at hb; cases hb
    rcases hp with rfl | rfl | rfl <;> rcases bv1_cases a' with rfl | rfl <;> decide
  · rw [cst_one ho] at hb; cases hb
    rcases hp with rfl | rfl | rfl <;> rcases bv1_cases a' with rfl | rfl <;> decide

/-- `IS.simplifyICmpOfBools.L2919`: `X <u 0` and `X >s 0` to false, in `i1`. -/
theorem simplifyICmpOfBools.L2919 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (hz : zero rhs = true)
    (hp : p = .ult ∨ p = .sgt) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [cst_zero hz] at hy; cases hy
  rcases hp with rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- `IS.simplifyICmpOfBools.L2923`: `X >=u 0` and `X <=s 0` to true, in `i1`. -/
theorem simplifyICmpOfBools.L2923 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (hz : zero rhs = true)
    (hp : p = .uge ∨ p = .sle) : Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [cst_zero hz] at hy; cases hy
  rcases hp with rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- `IS.simplifyICmpOfBools.L2933`: `X == 1`, `X >=u 1` and `X <=s -1` to `X`, in `i1`. -/
theorem simplifyICmpOfBools.L2933 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (ho : one rhs = true)
    (hp : p = .eq ∨ p = .uge ∨ p = .sle) : Refines ((src p s lhs rhs).eval ρ) ((Repl.old lhs).eval ρ) := by
  rw [src_eval, Repl.eval_old, cst_one ho]
  refine refines_ok (eval_refines fun x y hx hy => ?_)
  cases hy
  rw [hx]
  rcases hp with rfl | rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- `IS.simplifyICmpOfBools.L2944`: `X >u 1` and `X <s -1` to false, in `i1`. -/
theorem simplifyICmpOfBools.L2944 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (ho : one rhs = true)
    (hp : p = .ugt ∨ p = .slt) : Refines ((src p s lhs rhs).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [cst_one ho] at hy; cases hy
  rcases hp with rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- `IS.simplifyICmpOfBools.L2948`: `X <=u 1` and `X >=s -1` to true, in `i1`. -/
theorem simplifyICmpOfBools.L2948 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term 1) (ho : one rhs = true)
    (hp : p = .ule ∨ p = .sge) : Refines ((src p s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y _ hy => ?_
  rw [cst_one ho] at hy; cases hy
  rcases hp with rfl | rfl <;> rcases bv1_cases x with rfl | rfl <;> decide

/-- Where `A` implies `B` for the oracle, `B` is 1 whenever `A` is and neither is poison. -/
theorem ICmp.implied {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {a b : Term 1} (h : o.implies a b = some true)
    {x y : BitVec 1} (hx : a.denote ρ = some x) (hy : b.denote ρ = some y) : x = 1#1 → y = 1#1 := by
  intro h1
  subst h1
  rcases ho.implies a b true h hx with hb | hb <;> rw [hy] at hb <;> simp_all

/-- `IS.simplifyICmpOfBools.L2960`: `X >=u Y` to true in `i1`, where `Y` implies `X`. -/
theorem simplifyICmpOfBools.L2960 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (s : Bool) (lhs rhs : Term 1)
    (h : o.implies rhs lhs = some true) : Refines ((src .uge s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  have := ICmp.implied ho h hy hx
  rcases bv1_cases x with rfl | rfl <;> rcases bv1_cases y with rfl | rfl <;> simp_all <;> decide

/-- `IS.simplifyICmpOfBools.L2971`: `X >=s Y` to true in `i1`, where `X` implies `Y`. -/
theorem simplifyICmpOfBools.L2971 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (s : Bool) (lhs rhs : Term 1)
    (h : o.implies lhs rhs = some true) : Refines ((src .sge s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  have := ICmp.implied ho h hx hy
  rcases bv1_cases x with rfl | rfl <;> rcases bv1_cases y with rfl | rfl <;> simp_all <;> decide

/-- `IS.simplifyICmpOfBools.L2975`: `X <=u Y` to true in `i1`, where `X` implies `Y`. -/
theorem simplifyICmpOfBools.L2975 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (s : Bool) (lhs rhs : Term 1)
    (h : o.implies lhs rhs = some true) : Refines ((src .ule s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  have := ICmp.implied ho h hx hy
  rcases bv1_cases x with rfl | rfl <;> rcases bv1_cases y with rfl | rfl <;> simp_all <;> decide

/-- `IS.simplifyICmpOfBools.L2980`: `X <=s Y` to true in `i1`, where `Y` implies `X`. -/
theorem simplifyICmpOfBools.L2980 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (s : Bool) (lhs rhs : Term 1)
    (h : o.implies rhs lhs = some true) : Refines ((src .sle s lhs rhs).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine src_refines_const fun x y hx hy => ?_
  have := ICmp.implied ho h hy hx
  rcases bv1_cases x with rfl | rfl <;> rcases bv1_cases y with rfl | rfl <;> simp_all <;> decide

/-! ### The fold -/

/-- Every step of `simplifyICmpOfBools` on `i1` that fires is right. -/
theorem simplifyICmpOfBools.boolSteps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term 1) (c0 : lhs.Consistent ρ) :
    ∀ site r, Step.fire site r ∈ simplifyICmpOfBools.boolSteps o p lhs rhs →
      Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [boolSteps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hc
    exact L2908 ρ p s lhs rhs hc.1 hc.2
  · split at h
    · next hc =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next x hx =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hc
      exact ExtractNotLHS.L2899 ρ p s lhs rhs x c0 (Or.inl ⟨hc.1, hc.2⟩) hx
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L2919 ρ p s lhs rhs hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L2923 ρ p s lhs rhs hc.1 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hc
    exact L2933 ρ p s lhs rhs hc.1.2 hc.2
  · split at h
    · next hc =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next x hx =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at hc
      exact ExtractNotLHS.L2899 ρ p s lhs rhs x c0 (Or.inr ⟨hc.1.2, hc.2⟩) hx
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L2944 ρ p s lhs rhs hc.1.2 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    exact L2948 ρ p s lhs rhs hc.1.2 hc.2
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hi⟩ := hc
    exact L2960 ρ o ho s lhs rhs hi
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hi⟩ := hc
    exact L2971 ρ o ho s lhs rhs hi
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hi⟩ := hc
    exact L2975 ρ o ho s lhs rhs hi
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hi⟩ := hc
    exact L2980 ρ o ho s lhs rhs hi

/-- Theorem 1 for `simplifyICmpOfBools`: every value the model returns refines the `icmp`, with or without
`samesign`, at every width (it only answers on `i1`), in every run its operands are consistent with, poison
included, given sound analyses. -/
theorem simplifyICmpOfBools.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool) {w : Nat}
    (lhs rhs : Term w) (c0 : lhs.Consistent ρ) {r : Repl 1} (h : simplifyICmpOfBools o p lhs rhs = .value r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  unfold simplifyICmpOfBools simplifyICmpOfBools.steps at h
  split at h
  · next hw =>
    subst hw
    exact run_sound (boolSteps_sound ρ o ho p s lhs rhs c0) h
  · simp [run] at h

end Peephole.IS
