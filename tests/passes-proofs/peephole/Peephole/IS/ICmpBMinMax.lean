import Peephole.IS.ICmpB

/-! # InstSimplify's `simplifyICmpWithMinMax` and `simplifyICmpWithIntrinsicOnLHS`, and their rewrites for every input

At `llvmorg-23.1.3`, in `llvm/lib/Analysis/InstructionSimplify.cpp`: `extractEquivalentCondition` at 2620-2635,
`simplifyICmpWithMinMax` at 3606-3789 and `simplifyICmpWithIntrinsicOnLHS` at 3814-3845. `simplifyICmpInst` forwards to
the last two, the second twice, with the operands and predicate swapped; `simplifyICmpWithMinMax` forwards to the first.
Each step that rewrites carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of
that name:

| ID | Rewrite |
| --- | --- |
| `IS.extractEquivalentCondition.L2630` | the compare `LHS Pred RHS` to a `select`'s condition that is that compare |
| `IS.extractEquivalentCondition.L2633` | the same, with the condition's operands swapped |
| `IS.simplifyICmpWithMinMax.L3680` | `smax(A, B) >=s A`, and its three other forms with `smax` and `smin`, to true |
| `IS.simplifyICmpWithMinMax.L3683` | `smax(A, B) <s A`, and its other forms, to false |
| `IS.simplifyICmpWithMinMax.L3753` | `umax(A, B) >=u A`, and its other forms, to true |
| `IS.simplifyICmpWithMinMax.L3755` | `umax(A, B) <u A`, and its other forms, to false |
| `IS.simplifyICmpWithMinMax.L3773` | `smax(A, B) >=s smin(A, D)`, sharing any operand, to true |
| `IS.simplifyICmpWithMinMax.L3776` | `smax(A, B) <s smin(A, D)` to false |
| `IS.simplifyICmpWithMinMax.L3782` | `umax(A, B) >=u umin(A, D)` to true |
| `IS.simplifyICmpWithMinMax.L3785` | `umax(A, B) <u umin(A, D)` to false |
| `IS.simplifyICmpWithIntrinsicOnLHS.L3826` | `uadd.sat(X, Y) >=u X + Y` to true |
| `IS.simplifyICmpWithIntrinsicOnLHS.L3828` | `uadd.sat(X, Y) <u X + Y` to false |
| `IS.simplifyICmpWithIntrinsicOnLHS.L3836` | `usub.sat(X, Y) <=u X - Y` to true |
| `IS.simplifyICmpWithIntrinsicOnLHS.L3838` | `usub.sat(X, Y) >u X - Y` to false |

At this pin `m_SMax` and the like match only the intrinsics, so `extractEquivalentCondition`, which looks for a `select`,
finds one only in the operand that isn't the min or max: `A` itself, a `select` whose condition compares `A`. In SSA
that's unreachable code. Its theorem holds anyway: it needs the `select` not to be poison, which the compare it replaces
gives where it isn't poison itself.

`simplifyICmpWithMinMax` also asks the recursive `simplifyICmpInst` about `A EqP B`, without `samesign`; its theorem
takes that call's soundness as a hypothesis, `ICmpSimp.Sound`. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w u : Nat}

/-! ### `extractEquivalentCondition` -/

/-- `extractEquivalentCondition(V, Pred, LHS, RHS)`, step by step: `V` a `select` whose condition is a compare. -/
def extractEquivalentCondition.steps (v : Term w) (p : Pred) (a b : Term w) : List (Step 1) :=
  match v with
  | .select _ (.icmp cid cp cs cl cr) _ _ =>
    [ if p == cp && same a cl && same b cr then
        .fire "IS.extractEquivalentCondition.L2630" (.old (.icmp cid cp cs cl cr))
      else .next,
      if p == swapP cp && same a cr && same b cl then
        .fire "IS.extractEquivalentCondition.L2633" (.old (.icmp cid cp cs cl cr))
      else .next ]
  | _ => []

def extractEquivalentCondition (v : Term w) (p : Pred) (a b : Term w) : Result 1 :=
  run (extractEquivalentCondition.steps v p a b)

theorem select_ne_none {c : Val 1} {t e : Val w} (h : IRLean.select c t e ≠ none) : c ≠ none := by
  intro hc
  subst hc
  exact h rfl

/-- A compare with `samesign` that isn't poison is the one without. -/
theorem eval_plain_le {p : Pred} {a b : Val w} {s : Bool} (h : p.eval a b s ≠ none) :
    Refine.le (p.eval a b false) (p.eval a b s) := by
  cases a with
  | none => exact absurd (eval_none_left p _ s) h
  | some x =>
  cases b with
  | none => exact absurd (eval_none_right p _ s) h
  | some y =>
  rw [eval_some] at h ⊢
  rw [eval_some]
  split at h
  · exact absurd rfl h
  · next hs =>
    simp only [hs, Bool.false_and, Bool.false_eq_true, ite_false]
    exact Refine.refl_val _

theorem cond_val {ρ : Env} {id cid : Nat} {cp : Pred} {cs : Bool} {cl cr : Term u} {t e : Term w}
    (cv : (Term.select id (.icmp cid cp cs cl cr) t e).Consistent ρ)
    (hv : (Term.select id (.icmp cid cp cs cl cr) t e).denote ρ ≠ none) :
    (Term.icmp cid cp cs cl cr).denote ρ = cp.eval (cl.denote ρ) (cr.denote ρ) cs ∧
      cp.eval (cl.denote ρ) (cr.denote ρ) cs ≠ none := by
  simp only [Term.Consistent] at cv
  obtain ⟨⟨-, -, hc⟩, -, -, hs⟩ := cv
  have hv' : ρ w id ≠ none := hv
  rw [← hs] at hv'
  have := select_ne_none hv'
  refine ⟨hc.symm, ?_⟩
  rw [hc]
  exact this

/-- `IS.extractEquivalentCondition.L2630`: the compare `LHS Pred RHS`, without `samesign`, to the `select`'s condition
`icmp Pred LHS RHS`, where the `select` isn't poison. -/
theorem extractEquivalentCondition.L2630 (ρ : Env) (p : Pred) (a b : Term w) (id cid : Nat) (cp : Pred) (cs : Bool)
    (cl cr : Term u) (t e : Term w) (cv : (Term.select id (.icmp cid cp cs cl cr) t e).Consistent ρ)
    (hv : (Term.select id (.icmp cid cp cs cl cr) t e).denote ρ ≠ none)
    (h : (p == cp && same a cl && same b cr) = true) :
    Refines ((icmpSrc p false a b).eval ρ) ((Repl.old (Term.icmp cid cp cs cl cr)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, ha⟩, hb⟩ := h
  obtain rfl := same_width ha
  rw [same_iff_specific] at ha hb
  obtain ⟨hcv, hne⟩ := cond_val cv hv
  rw [icmpSrc_eval, Repl.eval_old, hcv, ← specific_denote ha, ← specific_denote hb]
  exact refines_ok (eval_plain_le hne)

/-- `IS.extractEquivalentCondition.L2633`: the same, where the condition is `icmp (swapped Pred) RHS LHS`. -/
theorem extractEquivalentCondition.L2633 (ρ : Env) (p : Pred) (a b : Term w) (id cid : Nat) (cp : Pred) (cs : Bool)
    (cl cr : Term u) (t e : Term w) (cv : (Term.select id (.icmp cid cp cs cl cr) t e).Consistent ρ)
    (hv : (Term.select id (.icmp cid cp cs cl cr) t e).denote ρ ≠ none)
    (h : (p == swapP cp && same a cr && same b cl) = true) :
    Refines ((icmpSrc p false a b).eval ρ) ((Repl.old (Term.icmp cid cp cs cl cr)).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, ha⟩, hb⟩ := h
  obtain rfl := same_width ha
  rw [same_iff_specific] at ha hb
  obtain ⟨hcv, hne⟩ := cond_val cv hv
  rw [icmpSrc_eval, Repl.eval_old, hcv, ← specific_denote ha, ← specific_denote hb, eval_swap]
  exact refines_ok (eval_plain_le hne)

theorem extractEquivalentCondition_old {v : Term w} {p : Pred} {a b : Term w} {r : Repl 1}
    (h : extractEquivalentCondition v p a b = .value r) : ∃ t, r = .old t := by
  obtain ⟨pre, site, post, hs, -⟩ := run_value h
  have hmem : Step.fire site r ∈ extractEquivalentCondition.steps v p a b := by rw [hs]; simp
  unfold extractEquivalentCondition.steps at hmem
  split at hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
      exact ⟨_, h.2⟩
  · simp at hmem

/-- Theorem 1 for `extractEquivalentCondition`: what it returns refines the compare `LHS Pred RHS` without `samesign`,
where `V` is consistent with the run and isn't poison. -/
theorem extractEquivalentCondition.sound (ρ : Env) (v : Term w) (p : Pred) (a b : Term w) (cv : v.Consistent ρ)
    (hv : v.denote ρ ≠ none) {r : Repl 1} (h : extractEquivalentCondition v p a b = .value r) :
    Refines ((icmpSrc p false a b).eval ρ) (r.eval ρ) := by
  have hs : ∀ site r, Step.fire site r ∈ extractEquivalentCondition.steps v p a b →
      Refines ((icmpSrc p false a b).eval ρ) (r.eval ρ) := by
    intro site r hmem
    unfold extractEquivalentCondition.steps at hmem
    split at hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact extractEquivalentCondition.L2630 ρ p a b _ _ _ _ _ _ _ _ cv hv (by assumption)
      · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact extractEquivalentCondition.L2633 ρ p a b _ _ _ _ _ _ _ _ cv hv (by assumption)
    · simp at hmem
  exact run_sound hs h

/-! ### Min and max -/

/-- `match(V, m_F(m_Value(A), m_Value(B)))` for a min or max intrinsic `F`. -/
def minmax? (f : BinIntr) : Term w → Option (Term w × Term w)
  | .bi _ f' a b => if f' = f then some (a, b) else none
  | _ => none

/-- `match(L, m_F(m_Value(A), m_Value(B))) && (A == R || B == R)`, then `if (A != R) std::swap(A, B);`. -/
def mmCase (f : BinIntr) (l r : Term w) : Option (Term w × Term w) :=
  match minmax? f l with
  | some (a, b) => if specific r a then some (a, b) else if specific r b then some (b, a) else none
  | none => none

/-- The four-way `if`/`else if` that picks `A`, `B`, `EqP` and `P`, for `smax`/`smin` with `sge`/`sle`, or
`umax`/`umin` with `uge`/`ule`: "max(A, B) P A" in each case. `P` is a plain predicate. -/
def mmSel (fmax fmin : BinIntr) (geP leP : Pred) (p : Pred) (lhs rhs : Term w) :
    Option (Term w × Term w × Pred × Pred) :=
  match mmCase fmax lhs rhs with
  | some (a, b) => some (a, b, geP, p)
  | none =>
    match mmCase fmax rhs lhs with
    | some (a, b) => some (a, b, geP, swapP p)
    | none =>
      match mmCase fmin lhs rhs with
      | some (a, b) => some (a, b, leP, swapP p)
      | none =>
        match mmCase fmin rhs lhs with
        | some (a, b) => some (a, b, leP, p)
        | none => none

/-- The `switch (P)` after one of the two selections: `leP` and `gtP` are `sle` and `sgt`, or `ule` and `ugt`;
`geP` and `ltP` are `sge` and `slt`, or `uge` and `ult`. -/
def mmGroup.steps (simp : ICmpSimp) (sel : Option (Term w × Term w × Pred × Pred)) (leP gtP geP ltP : Pred)
    (siteT siteF : String) (lhs rhs : Term w) (n : Nat) : List (Step 1) :=
  match sel with
  | some (a, b, eqp, pp) =>
    [ -- Equivalent to "A EqP B".  This may be the same as the condition tested
      -- in the max/min; if so, we can just return that.
      if pp == .eq || pp == leP then fwd "IS.extractEquivalentCondition" (extractEquivalentCondition lhs eqp a b)
      else .next,
      if pp == .eq || pp == leP then fwd "IS.extractEquivalentCondition" (extractEquivalentCondition rhs eqp a b)
      else .next,
      -- Otherwise, see if "A EqP B" simplifies.
      if (pp == .eq || pp == leP) && n != 0 then fwd "simplifyICmpInst" (simp eqp false a b (n - 1)) else .next,
      -- Equivalent to "A InvEqP B".  This may be the same as the condition
      -- tested in the max/min; if so, we can just return that.
      if pp == .ne || pp == gtP then
        fwd "IS.extractEquivalentCondition" (extractEquivalentCondition lhs (invP eqp) a b)
      else .next,
      if pp == .ne || pp == gtP then
        fwd "IS.extractEquivalentCondition" (extractEquivalentCondition rhs (invP eqp) a b)
      else .next,
      -- Otherwise, see if "A InvEqP B" simplifies.
      if (pp == .ne || pp == gtP) && n != 0 then fwd "simplifyICmpInst" (simp (invP eqp) false a b (n - 1))
      else .next,
      -- Always true.
      if pp == geP then .fire siteT (boolR true) else .next,
      -- Always false.
      if pp == ltP then .fire siteF (boolR false) else .next ]
  | none => []

/-- Comparing 1 each of min/max with a common operand? Canonicalize min operand to RHS. -/
def mmCanon (p : Pred) (lhs rhs : Term w) : Pred × Term w × Term w :=
  if (minmax? .umin lhs).isSome || (minmax? .smin lhs).isSome then (swapP p, rhs, lhs) else (p, lhs, rhs)

/-- `match(LHS, m_Max(m_Value(A), m_Value(B))) && match(RHS, m_Min(m_Value(C), m_Value(D))) &&
(A == C || A == D || B == C || B == D)`. -/
def mmCommon (fmax fmin : BinIntr) (l r : Term w) : Bool :=
  match minmax? fmax l, minmax? fmin r with
  | some (a, b), some (c, d) => specific a c || specific a d || specific b c || specific b d
  | _, _ => false

/-- The last part of `simplifyICmpWithMinMax`, after the canonicalization. -/
def mmCommon.steps (p : Pred) (l r : Term w) : List (Step 1) :=
  [ -- smax(A, B) >=s smin(A, D) --> true
    if mmCommon .smax .smin l r && p == .sge then .fire "IS.simplifyICmpWithMinMax.L3773" (boolR true) else .next,
    -- smax(A, B) <s smin(A, D) --> false
    if mmCommon .smax .smin l r && p == .slt then .fire "IS.simplifyICmpWithMinMax.L3776" (boolR false) else .next,
    -- umax(A, B) >=u umin(A, D) --> true
    if !mmCommon .smax .smin l r && mmCommon .umax .umin l r && p == .uge then
      .fire "IS.simplifyICmpWithMinMax.L3782" (boolR true)
    else .next,
    -- umax(A, B) <u umin(A, D) --> false
    if !mmCommon .smax .smin l r && mmCommon .umax .umin l r && p == .ult then
      .fire "IS.simplifyICmpWithMinMax.L3785" (boolR false)
    else .next ]

/-- `simplifyICmpWithMinMax(Pred, LHS, RHS, Q, MaxRecurse)`, step by step: the signed variants, the unsigned ones, and
min against max. `simp` is the recursive `simplifyICmpInst`. -/
def simplifyICmpWithMinMax.steps (simp : ICmpSimp) (p : Pred) (lhs rhs : Term w) (n : Nat) : List (Step 1) :=
  mmGroup.steps simp (mmSel .smax .smin .sge .sle p lhs rhs) .sle .sgt .sge .slt
      "IS.simplifyICmpWithMinMax.L3680" "IS.simplifyICmpWithMinMax.L3683" lhs rhs n ++
    mmGroup.steps simp (mmSel .umax .umin .uge .ule p lhs rhs) .ule .ugt .uge .ult
      "IS.simplifyICmpWithMinMax.L3753" "IS.simplifyICmpWithMinMax.L3755" lhs rhs n ++
    mmCommon.steps (mmCanon p lhs rhs).1 (mmCanon p lhs rhs).2.1 (mmCanon p lhs rhs).2.2

def simplifyICmpWithMinMax (simp : ICmpSimp) (p : Pred) (lhs rhs : Term w) (n : Nat) : Result 1 :=
  run (simplifyICmpWithMinMax.steps simp p lhs rhs n)

/-! ### What a min or max is -/

/-- What the analysis needs of a max and min intrinsic and the predicates `geP` and `leP`: both commute, give poison
for poison, `max(a, b) geP a`, `max(a, b) == a` and `max(a, b) leP a` exactly when `a geP b`, and the duals for min. -/
structure MMKind (fmax fmin : BinIntr) (geP leP : Pred) : Prop where
  comm_max : ∀ {w : Nat} (a b : Val w), fmax.eval a b = fmax.eval b a
  comm_min : ∀ {w : Nat} (a b : Val w), fmin.eval a b = fmin.eval b a
  strict_max : ∀ {w : Nat} (a b : Val w) (x : BitVec w), fmax.eval a b = some x → ∃ av bv, a = some av ∧ b = some bv
  strict_min : ∀ {w : Nat} (a b : Val w) (x : BitVec w), fmin.eval a b = some x → ∃ av bv, a = some av ∧ b = some bv
  max : ∀ {w : Nat} (a b x : BitVec w), fmax.eval (some a) (some b) = some x →
    test geP x a = true ∧ (x == a) = test geP a b ∧ test leP x a = test geP a b
  min : ∀ {w : Nat} (a b x : BitVec w), fmin.eval (some a) (some b) = some x →
    test geP a x = true ∧ (a == x) = test leP a b ∧ test leP a x = test leP a b

theorem map₂_strict {f : BitVec w → BitVec w → BitVec w} {a b : Val w} {x : BitVec w}
    (h : Val.map₂ f a b = some x) : ∃ av bv, a = some av ∧ b = some bv := by
  cases a <;> cases b <;> simp_all [Val.map₂]

theorem signedKind : MMKind .smax .smin .sge .sle where
  comm_max a b := by
    cases a <;> cases b <;> simp only [BinIntr.eval, Val.smax, Val.map₂]
    rename_i x y
    congr 1
    simp only [BitVec.sle, decide_eq_true_eq]
    split <;> split <;> first | rfl | (apply BitVec.eq_of_toInt_eq; omega)
  comm_min a b := by
    cases a <;> cases b <;> simp only [BinIntr.eval, Val.smin, Val.map₂]
    rename_i x y
    congr 1
    simp only [BitVec.sle, decide_eq_true_eq]
    split <;> split <;> first | rfl | (apply BitVec.eq_of_toInt_eq; omega)
  strict_max _ _ _ h := map₂_strict h
  strict_min _ _ _ h := map₂_strict h
  max a b x h := by
    simp only [BinIntr.eval, Val.smax, Val.map₂, Option.some.injEq] at h
    subst h
    exact ⟨Lemmas.sle_smax a b, Lemmas.smax_beq a b, Lemmas.smax_sle a b⟩
  min a b x h := by
    simp only [BinIntr.eval, Val.smin, Val.map₂, Option.some.injEq] at h
    subst h
    exact ⟨Lemmas.smin_sle a b, Lemmas.beq_smin a b, Lemmas.sle_smin a b⟩

theorem unsignedKind : MMKind .umax .umin .uge .ule where
  comm_max a b := by
    cases a <;> cases b <;> simp only [BinIntr.eval, Val.umax, Val.map₂]
    rename_i x y
    congr 1
    simp only [BitVec.ule, decide_eq_true_eq]
    split <;> split <;> first | rfl | (apply BitVec.eq_of_toNat_eq; omega)
  comm_min a b := by
    cases a <;> cases b <;> simp only [BinIntr.eval, Val.umin, Val.map₂]
    rename_i x y
    congr 1
    simp only [BitVec.ule, decide_eq_true_eq]
    split <;> split <;> first | rfl | (apply BitVec.eq_of_toNat_eq; omega)
  strict_max _ _ _ h := map₂_strict h
  strict_min _ _ _ h := map₂_strict h
  max a b x h := by
    simp only [BinIntr.eval, Val.umax, Val.map₂, Option.some.injEq] at h
    subst h
    exact ⟨Lemmas.ule_umax a b, Lemmas.umax_beq a b, Lemmas.umax_ule a b⟩
  min a b x h := by
    simp only [BinIntr.eval, Val.umin, Val.map₂, Option.some.injEq] at h
    subst h
    exact ⟨Lemmas.umin_ule a b, Lemmas.beq_umin a b, Lemmas.ule_umin a b⟩

theorem minmax?_val {ρ : Env} {f : BinIntr} {t a b : Term w} (h : minmax? f t = some (a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ t.denote ρ = f.eval (a.denote ρ) (b.denote ρ) ∧
      (t.hasUndef = false → a.hasUndef = false ∧ b.hasUndef = false) := by
  unfold minmax? at h
  split at h
  · next id f' a' b' =>
    split at h
    · next hf =>
      subst hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Term.Consistent] at hc
      obtain ⟨ha, hb, he⟩ := hc
      refine ⟨ha, hb, he.symm, fun hu => ?_⟩
      simpa [Term.hasUndef] using hu
    · cases h
  · cases h

theorem mmCase_val {ρ : Env} {f : BinIntr} {l r a b : Term w} (hcomm : ∀ (x y : Val w), f.eval x y = f.eval y x)
    (h : mmCase f l r = some (a, b)) (hc : l.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ l.denote ρ = f.eval (a.denote ρ) (b.denote ρ) ∧ r.denote ρ = a.denote ρ ∧
      (l.hasUndef = false → a.hasUndef = false ∧ b.hasUndef = false) := by
  unfold mmCase at h
  split at h
  · next a' b' hm =>
    obtain ⟨ha, hb, he, hu⟩ := minmax?_val hm hc
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ha, hb, he, (specific_denote hs).symm, hu⟩
    · split at h
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hb, ha, by rw [he, hcomm], (specific_denote hs).symm, fun h => (hu h).symm⟩
      · cases h
  · cases h

/-- What `mmSel` picks says about the compare: wherever neither operand is poison, `A` and `B` aren't, and the
compare is `u P v` for a pair with `u geP v`, `u == v` exactly when `A EqP B`, and `u leP v` exactly when `A EqP B`. -/
theorem mmSel_val {ρ : Env} {fmax fmin : BinIntr} {geP leP : Pred} (hk : MMKind fmax fmin geP leP) {p : Pred}
    {lhs rhs a b : Term w} {eqp pp : Pred} (h : mmSel fmax fmin geP leP p lhs rhs = some (a, b, eqp, pp))
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧
      (lhs.hasUndef = false → rhs.hasUndef = false → a.hasUndef = false ∧ b.hasUndef = false) ∧
      ∀ x y, lhs.denote ρ = some x → rhs.denote ρ = some y → ∃ av bv uv vv : BitVec w, a.denote ρ = some av ∧
        b.denote ρ = some bv ∧ test p x y = test pp uv vv ∧ test geP uv vv = true ∧
        (uv == vv) = test eqp av bv ∧ test leP uv vv = test eqp av bv := by
  unfold mmSel at h
  split at h
  · next a' b' hm =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ha, hb, hl, hr, hu⟩ := mmCase_val (hk.comm_max) hm cl
    refine ⟨ha, hb, fun h1 _ => hu h1, fun x y hx hy => ?_⟩
    rw [hl] at hx
    obtain ⟨av, bv, hav, hbv⟩ := hk.strict_max _ _ _ hx
    rw [hav, hbv] at hx
    rw [hr, hav] at hy
    have hy' : av = y := Option.some.inj hy
    subst hy'
    obtain ⟨h1, h2, h3⟩ := hk.max av bv x hx
    exact ⟨av, bv, x, av, hav, hbv, rfl, h1, h2, h3⟩
  · split at h
    · next a' b' hm =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨ha, hb, hl, hr, hu⟩ := mmCase_val (hk.comm_max) hm cr
      refine ⟨ha, hb, fun _ h2 => hu h2, fun x y hx hy => ?_⟩
      rw [hl] at hy
      obtain ⟨av, bv, hav, hbv⟩ := hk.strict_max _ _ _ hy
      rw [hav, hbv] at hy
      rw [hr, hav] at hx
      have hx' : av = x := Option.some.inj hx
      subst hx'
      obtain ⟨h1, h2, h3⟩ := hk.max av bv y hy
      exact ⟨av, bv, y, av, hav, hbv, (test_swap p _ _).symm, h1, h2, h3⟩
    · split at h
      · next a' b' hm =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        obtain ⟨ha, hb, hl, hr, hu⟩ := mmCase_val (hk.comm_min) hm cl
        refine ⟨ha, hb, fun h1 _ => hu h1, fun x y hx hy => ?_⟩
        rw [hl] at hx
        obtain ⟨av, bv, hav, hbv⟩ := hk.strict_min _ _ _ hx
        rw [hav, hbv] at hx
        rw [hr, hav] at hy
        have hy' : av = y := Option.some.inj hy
        subst hy'
        obtain ⟨h1, h2, h3⟩ := hk.min av bv x hx
        exact ⟨av, bv, av, x, hav, hbv, (test_swap p _ _).symm, h1, h2, h3⟩
      · split at h
        · next a' b' hm =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          obtain ⟨ha, hb, hl, hr, hu⟩ := mmCase_val (hk.comm_min) hm cr
          refine ⟨ha, hb, fun _ h2 => hu h2, fun x y hx hy => ?_⟩
          rw [hl] at hy
          obtain ⟨av, bv, hav, hbv⟩ := hk.strict_min _ _ _ hy
          rw [hav, hbv] at hy
          rw [hr, hav] at hx
          have hx' : av = x := Option.some.inj hx
          subst hx'
          obtain ⟨h1, h2, h3⟩ := hk.min av bv y hy
          exact ⟨av, bv, av, y, hav, hbv, rfl, h1, h2, h3⟩
        · cases h

/-- A compare that's another wherever neither operand is poison refines the other without `samesign`. -/
theorem icmpSrc_le {ρ : Env} {p q : Pred} {s : Bool} {x1 y1 x2 y2 : Term w}
    (h : ∀ x y, x1.denote ρ = some x → y1.denote ρ = some y →
      ∃ a b, x2.denote ρ = some a ∧ y2.denote ρ = some b ∧ test p x y = test q a b) :
    Refines ((icmpSrc p s x1 y1).eval ρ) ((icmpSrc q false x2 y2).eval ρ) := by
  rw [icmpSrc_eval, icmpSrc_eval]
  refine refines_ok ?_
  cases hx : x1.denote ρ with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some x =>
  cases hy : y1.denote ρ with
  | none => rw [eval_none_right]; exact Refine.val_none _
  | some y =>
  obtain ⟨a, b, ha, hb, he⟩ := h x y hx hy
  rw [ha, hb, eval_some, eval_some, he]
  split
  · exact Refine.val_none _
  · simp only [Bool.false_and, Bool.false_eq_true, ite_false]
    exact Refine.refl_val _

/-- `mmSel`'s compare, under `P` from `{eq, leP}`, is `A EqP B`, and under `P` from `{ne, gtP}`, `A InvEqP B`. -/
theorem mm_eqp {pp eqp leP gtP : Pred} {uv vv av bv : BitVec w} (hgt : gtP = invP leP)
    (h2 : (uv == vv) = test eqp av bv) (h3 : test leP uv vv = test eqp av bv) :
    ((pp == .eq || pp == leP) = true → test pp uv vv = test eqp av bv) ∧
      ((pp == .ne || pp == gtP) = true → test pp uv vv = test (invP eqp) av bv) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact h2
    · exact h3
  · simp only [Bool.or_eq_true, beq_iff_eq] at h
    rw [test_inv]
    rcases h with rfl | rfl
    · simp only [test, bne, h2]
    · rw [hgt, test_inv, h3]

/-- Every step of one group of `simplifyICmpWithMinMax` that fires is right. -/
theorem mmGroup.steps_sound (ρ : Env) {fmax fmin : BinIntr} {geP leP gtP ltP : Pred}
    (hk : MMKind fmax fmin geP leP) (hgt : gtP = invP leP) (hlt : ltP = invP geP) (simp : ICmpSimp)
    (hsimp : simp.Sound ρ) (p : Pred) (s : Bool) (lhs rhs : Term w) (n : Nat) (siteT siteF : String)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false) (ur : rhs.hasUndef = false) :
    ∀ site r, Step.fire site r ∈
      mmGroup.steps simp (mmSel fmax fmin geP leP p lhs rhs) leP gtP geP ltP siteT siteF lhs rhs n →
      Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  unfold mmGroup.steps at hmem
  split at hmem
  · next a b eqp pp hsel =>
    obtain ⟨ca, cb, hu, hv⟩ := mmSel_val hk hsel cl cr
    obtain ⟨ua, ub⟩ := hu ul ur
    -- the compare against `A EqP B` and `A InvEqP B`
    have heq : (pp == .eq || pp == leP) = true →
        Refines ((icmpSrc p s lhs rhs).eval ρ) ((icmpSrc eqp false a b).eval ρ) := fun hp =>
      icmpSrc_le fun x y hx hy => by
        obtain ⟨av, bv, uv, vv, ha, hb, he, -, h2, h3⟩ := hv x y hx hy
        exact ⟨av, bv, ha, hb, by rw [he, (mm_eqp hgt h2 h3).1 hp]⟩
    have hne : (pp == .ne || pp == gtP) = true →
        Refines ((icmpSrc p s lhs rhs).eval ρ) ((icmpSrc (invP eqp) false a b).eval ρ) := fun hp =>
      icmpSrc_le fun x y hx hy => by
        obtain ⟨av, bv, uv, vv, ha, hb, he, -, h2, h3⟩ := hv x y hx hy
        exact ⟨av, bv, ha, hb, by rw [he, (mm_eqp hgt h2 h3).2 hp]⟩
    -- a forward through `extractEquivalentCondition` on `lhs` or `rhs`
    have hext : ∀ (v : Term w) (q : Pred) (r : Repl 1), v.Consistent ρ →
        (v.denote ρ = none → (icmpSrc p s lhs rhs).eval ρ = Outcome.ok none) →
        Refines ((icmpSrc p s lhs rhs).eval ρ) ((icmpSrc q false a b).eval ρ) →
        extractEquivalentCondition v q a b = .value r → Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
      intro v q r cv hpoison hle hr
      by_cases hvn : v.denote ρ = none
      · rw [hpoison hvn]
        obtain ⟨t, rfl⟩ := extractEquivalentCondition_old hr
        exact refines_ok (Refine.val_none _)
      · exact Refines.trans hle (extractEquivalentCondition.sound ρ v q a b cv hvn hr)
    have hpl : lhs.denote ρ = none → (icmpSrc p s lhs rhs).eval ρ = Outcome.ok none := fun h => by
      rw [icmpSrc_eval, h, eval_none_left]
    have hpr : rhs.denote ρ = none → (icmpSrc p s lhs rhs).eval ρ = Outcome.ok none := fun h => by
      rw [icmpSrc_eval, h, eval_none_right]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h
    · split at h
      · next hp => exact hext lhs eqp r cl hpl (heq hp) (fwd_fire h.symm)
      · cases h
    · split at h
      · next hp => exact hext rhs eqp r cr hpr (heq hp) (fwd_fire h.symm)
      · cases h
    · split at h
      · next hp =>
        simp only [Bool.and_eq_true] at hp
        exact Refines.trans (heq hp.1) (hsimp eqp false a b (n - 1) r ca cb ua ub (fwd_fire h.symm))
      · cases h
    · split at h
      · next hp => exact hext lhs (invP eqp) r cl hpl (hne hp) (fwd_fire h.symm)
      · cases h
    · split at h
      · next hp => exact hext rhs (invP eqp) r cr hpr (hne hp) (fwd_fire h.symm)
      · cases h
    · split at h
      · next hp =>
        simp only [Bool.and_eq_true] at hp
        exact Refines.trans (hne hp.1) (hsimp (invP eqp) false a b (n - 1) r ca cb ua ub (fwd_fire h.symm))
      · cases h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hp =>
      obtain ⟨-, rfl⟩ := h
      rw [beq_iff_eq] at hp
      subst hp
      refine refines_bool fun x y hx hy => ?_
      obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
      rw [he, h1]
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hp =>
      obtain ⟨-, rfl⟩ := h
      rw [beq_iff_eq] at hp
      subst hp
      refine refines_bool fun x y hx hy => ?_
      obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
      rw [he, hlt, test_inv, h1]; rfl
  · simp at hmem

/-- `IS.simplifyICmpWithMinMax.L3680`: "max(A, B) sge A" to true, for `smax(A, B) >=s A`, `A <=s smax(A, B)`,
`smin(A, B) <=s A` and `A >=s smin(A, B)`. Proved, with `L3683`, by `mmGroup.steps_sound`. -/
theorem simplifyICmpWithMinMax.L3680 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs a b : Term w) (eqp : Pred)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (hsel : mmSel .smax .smin .sge .sle p lhs rhs = some (a, b, eqp, .sge)) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  obtain ⟨-, -, -, hv⟩ := mmSel_val signedKind hsel cl cr
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
  rw [he, h1]

/-- `IS.simplifyICmpWithMinMax.L3683`: "max(A, B) slt A" to false. -/
theorem simplifyICmpWithMinMax.L3683 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs a b : Term w) (eqp : Pred)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (hsel : mmSel .smax .smin .sge .sle p lhs rhs = some (a, b, eqp, .slt)) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  obtain ⟨-, -, -, hv⟩ := mmSel_val signedKind hsel cl cr
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
  rw [he, show Pred.slt = invP .sge from rfl, test_inv, h1]; rfl

/-- `IS.simplifyICmpWithMinMax.L3753`: "max(A, B) uge A" to true. -/
theorem simplifyICmpWithMinMax.L3753 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs a b : Term w) (eqp : Pred)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (hsel : mmSel .umax .umin .uge .ule p lhs rhs = some (a, b, eqp, .uge)) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR true).eval ρ) := by
  obtain ⟨-, -, -, hv⟩ := mmSel_val unsignedKind hsel cl cr
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
  rw [he, h1]

/-- `IS.simplifyICmpWithMinMax.L3755`: "max(A, B) ult A" to false. -/
theorem simplifyICmpWithMinMax.L3755 (ρ : Env) (p : Pred) (s : Bool) (lhs rhs a b : Term w) (eqp : Pred)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ)
    (hsel : mmSel .umax .umin .uge .ule p lhs rhs = some (a, b, eqp, .ult)) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) ((boolR false).eval ρ) := by
  obtain ⟨-, -, -, hv⟩ := mmSel_val unsignedKind hsel cl cr
  refine refines_bool fun x y hx hy => ?_
  obtain ⟨av, bv, uv, vv, -, -, he, h1, -, -⟩ := hv x y hx hy
  rw [he, show Pred.ult = invP .uge from rfl, test_inv, h1]; rfl

theorem mmCanon_eval (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w) :
    (icmpSrc (mmCanon p lhs rhs).1 s (mmCanon p lhs rhs).2.1 (mmCanon p lhs rhs).2.2).eval ρ =
      (icmpSrc p s lhs rhs).eval ρ := by
  unfold mmCanon
  split
  · exact icmpSrc_swap ρ p s lhs rhs
  · rfl

theorem mmCanon_consistent {ρ : Env} {p : Pred} {lhs rhs : Term w} (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) :
    (mmCanon p lhs rhs).2.1.Consistent ρ ∧ (mmCanon p lhs rhs).2.2.Consistent ρ := by
  unfold mmCanon
  split
  · exact ⟨cr, cl⟩
  · exact ⟨cl, cr⟩

theorem mmCommon_val {ρ : Env} {l r : Term w} (cl : l.Consistent ρ) (cr : r.Consistent ρ) :
    (mmCommon .smax .smin l r = true → ∀ x y, l.denote ρ = some x → r.denote ρ = some y → BitVec.sle y x = true) ∧
      (mmCommon .umax .umin l r = true → ∀ x y, l.denote ρ = some x → r.denote ρ = some y →
        BitVec.ule y x = true) := by
  refine ⟨fun h x y hx hy => ?_, fun h x y hx hy => ?_⟩ <;> unfold mmCommon at h <;> split at h
  · next a b c d hl hr =>
    obtain ⟨-, -, hle, -⟩ := minmax?_val hl cl
    obtain ⟨-, -, hre, -⟩ := minmax?_val hr cr
    rw [hle] at hx
    rw [hre] at hy
    obtain ⟨av, bv, ha, hb⟩ := map₂_strict hx
    obtain ⟨cv, dv, hc, hd⟩ := map₂_strict hy
    rw [ha, hb] at hx
    rw [hc, hd] at hy
    simp only [BinIntr.eval, Val.smax, Val.smin, Val.map₂, Option.some.injEq] at hx hy
    subst hx hy
    apply Lemmas.smin_sle_smax
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · left; rw [← Option.some.inj (hc.symm.trans ((specific_denote h).trans ha))]
    · right; left; rw [← Option.some.inj (hd.symm.trans ((specific_denote h).trans ha))]
    · right; right; left; rw [← Option.some.inj (hc.symm.trans ((specific_denote h).trans hb))]
    · right; right; right; rw [← Option.some.inj (hd.symm.trans ((specific_denote h).trans hb))]
  · cases h
  · next a b c d hl hr =>
    obtain ⟨-, -, hle, -⟩ := minmax?_val hl cl
    obtain ⟨-, -, hre, -⟩ := minmax?_val hr cr
    rw [hle] at hx
    rw [hre] at hy
    obtain ⟨av, bv, ha, hb⟩ := map₂_strict hx
    obtain ⟨cv, dv, hc, hd⟩ := map₂_strict hy
    rw [ha, hb] at hx
    rw [hc, hd] at hy
    simp only [BinIntr.eval, Val.umax, Val.umin, Val.map₂, Option.some.injEq] at hx hy
    subst hx hy
    apply Lemmas.umin_ule_umax
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · left; rw [← Option.some.inj (hc.symm.trans ((specific_denote h).trans ha))]
    · right; left; rw [← Option.some.inj (hd.symm.trans ((specific_denote h).trans ha))]
    · right; right; left; rw [← Option.some.inj (hc.symm.trans ((specific_denote h).trans hb))]
    · right; right; right; rw [← Option.some.inj (hd.symm.trans ((specific_denote h).trans hb))]
  · cases h

/-- `IS.simplifyICmpWithMinMax.L3773`: `smax(A, B) >=s smin(C, D)` to true, where they share an operand, after the
min is put on the right. -/
theorem simplifyICmpWithMinMax.L3773 (ρ : Env) (p : Pred) (s : Bool) (l r : Term w) (cl : l.Consistent ρ)
    (cr : r.Consistent ρ) (h : (mmCommon .smax .smin l r && p == .sge) = true) :
    Refines ((icmpSrc p s l r).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  exact refines_bool fun x y hx hy => (mmCommon_val cl cr).1 h x y hx hy

/-- `IS.simplifyICmpWithMinMax.L3776`: `smax(A, B) <s smin(C, D)` to false. -/
theorem simplifyICmpWithMinMax.L3776 (ρ : Env) (p : Pred) (s : Bool) (l r : Term w) (cl : l.Consistent ρ)
    (cr : r.Consistent ρ) (h : (mmCommon .smax .smin l r && p == .slt) = true) :
    Refines ((icmpSrc p s l r).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  have := (mmCommon_val cl cr).1 h x y hx hy
  simp only [test, BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-- `IS.simplifyICmpWithMinMax.L3782`: `umax(A, B) >=u umin(C, D)` to true. -/
theorem simplifyICmpWithMinMax.L3782 (ρ : Env) (p : Pred) (s : Bool) (l r : Term w) (cl : l.Consistent ρ)
    (cr : r.Consistent ρ) (h : (!mmCommon .smax .smin l r && mmCommon .umax .umin l r && p == .uge) = true) :
    Refines ((icmpSrc p s l r).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h⟩, rfl⟩ := h
  exact refines_bool fun x y hx hy => (mmCommon_val cl cr).2 h x y hx hy

/-- `IS.simplifyICmpWithMinMax.L3785`: `umax(A, B) <u umin(C, D)` to false. -/
theorem simplifyICmpWithMinMax.L3785 (ρ : Env) (p : Pred) (s : Bool) (l r : Term w) (cl : l.Consistent ρ)
    (cr : r.Consistent ρ) (h : (!mmCommon .smax .smin l r && mmCommon .umax .umin l r && p == .ult) = true) :
    Refines ((icmpSrc p s l r).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h⟩, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  have := (mmCommon_val cl cr).2 h x y hx hy
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

theorem mmCommon.steps_sound (ρ : Env) (p : Pred) (s : Bool) (l r : Term w) (cl : l.Consistent ρ)
    (cr : r.Consistent ρ) :
    ∀ site rr, Step.fire site rr ∈ mmCommon.steps p l r → Refines ((icmpSrc p s l r).eval ρ) (rr.eval ρ) := by
  intro site rr hmem
  simp only [mmCommon.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
    obtain ⟨-, rfl⟩ := h
  · exact simplifyICmpWithMinMax.L3773 ρ p s l r cl cr (by assumption)
  · exact simplifyICmpWithMinMax.L3776 ρ p s l r cl cr (by assumption)
  · exact simplifyICmpWithMinMax.L3782 ρ p s l r cl cr (by assumption)
  · exact simplifyICmpWithMinMax.L3785 ρ p s l r cl cr (by assumption)

/-- Theorem 1 for `simplifyICmpWithMinMax`: every value the model returns refines `icmp [samesign] Pred LHS, RHS`, at
every width, predicate, `samesign` flag and recursion budget, in every run the operands are consistent with, poison
included, where the recursive `simplifyICmpInst` is sound. It says nothing about operands that reach an `undef`. -/
theorem simplifyICmpWithMinMax.sound (ρ : Env) (simp : ICmpSimp) (hsimp : simp.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (n : Nat) (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) (ul : lhs.hasUndef = false)
    (ur : rhs.hasUndef = false) {r : Repl 1} (h : simplifyICmpWithMinMax simp p lhs rhs n = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
  have hs : ∀ site r, Step.fire site r ∈ simplifyICmpWithMinMax.steps simp p lhs rhs n →
      Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
    intro site r hmem
    simp only [simplifyICmpWithMinMax.steps, List.mem_append] at hmem
    rcases hmem with (hm | hm) | hm
    · exact mmGroup.steps_sound ρ signedKind rfl rfl simp hsimp p s lhs rhs n _ _ cl cr ul ur site r hm
    · exact mmGroup.steps_sound ρ unsignedKind rfl rfl simp hsimp p s lhs rhs n _ _ cl cr ul ur site r hm
    · rw [← mmCanon_eval]
      exact mmCommon.steps_sound ρ _ s _ _ (mmCanon_consistent cl cr).1 (mmCanon_consistent cl cr).2 site r hm
  exact run_sound hs h

/-! ### `simplifyICmpWithIntrinsicOnLHS` -/

/-- `m_c_Add(m_Specific(A), m_Specific(B))`. -/
def addOf (v a b : Term w) : Bool :=
  match binop? .add v with
  | some (_, x, y) => (specific a x && specific b y) || (specific a y && specific b x)
  | none => false

/-- `m_Sub(m_Specific(A), m_Specific(B))`. -/
def subOfBoth (v a b : Term w) : Bool :=
  match binop? .sub v with
  | some (_, x, y) => specific a x && specific b y
  | none => false

/-- `simplifyICmpWithIntrinsicOnLHS(Pred, LHS, RHS)`, step by step. -/
def simplifyICmpWithIntrinsicOnLHS.steps (p : Pred) (lhs rhs : Term w) : List (Step 1) :=
  match lhs with
  | .bi _ .uaddSat a b =>
    [ -- uadd.sat(X, Y) uge X + Y
      if addOf rhs a b && p == .uge then .fire "IS.simplifyICmpWithIntrinsicOnLHS.L3826" (boolR true) else .next,
      if addOf rhs a b && p == .ult then .fire "IS.simplifyICmpWithIntrinsicOnLHS.L3828" (boolR false) else .next ]
  | .bi _ .usubSat a b =>
    [ -- usub.sat(X, Y) ule X - Y
      if subOfBoth rhs a b && p == .ule then .fire "IS.simplifyICmpWithIntrinsicOnLHS.L3836" (boolR true)
      else .next,
      if subOfBoth rhs a b && p == .ugt then .fire "IS.simplifyICmpWithIntrinsicOnLHS.L3838" (boolR false)
      else .next ]
  | _ => []

def simplifyICmpWithIntrinsicOnLHS (p : Pred) (lhs rhs : Term w) : Result 1 :=
  run (simplifyICmpWithIntrinsicOnLHS.steps p lhs rhs)

theorem uaddSat_add_val {ρ : Env} {id : Nat} {a b rhs : Term w} (cl : (Term.bi id .uaddSat a b).Consistent ρ)
    (cr : rhs.Consistent ρ) (h : addOf rhs a b = true) :
    ∀ x y, (Term.bi id .uaddSat a b).denote ρ = some x → rhs.denote ρ = some y → BitVec.ule y x = true := by
  intro x y hx hy
  simp only [Term.Consistent] at cl
  obtain ⟨-, -, he⟩ := cl
  have hx' : ρ w id = some x := hx
  rw [← he] at hx'
  obtain ⟨av, bv, ha, hb⟩ := map₂_strict hx'
  rw [ha, hb] at hx'
  simp only [BinIntr.eval, Val.uaddSat, Val.map₂, Option.some.injEq] at hx'
  subst hx'
  unfold addOf at h
  split at h
  · next f x' y' hadd =>
    have he' := ok_inj (bin_val hadd cr)
    rw [hy] at he'
    obtain ⟨px, py, hpx, hpy, rfl, -, -⟩ := add_some he'
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [specific_denote h1, ha] at hpx
      rw [specific_denote h2, hb] at hpy
      cases hpx; cases hpy
      exact Lemmas.add_ule_uaddSat _ _
    · rw [specific_denote h2, hb] at hpx
      rw [specific_denote h1, ha] at hpy
      cases hpx; cases hpy
      rw [BitVec.add_comm]
      exact Lemmas.add_ule_uaddSat _ _
  · cases h

theorem usubSat_sub_val {ρ : Env} {id : Nat} {a b rhs : Term w} (cl : (Term.bi id .usubSat a b).Consistent ρ)
    (cr : rhs.Consistent ρ) (h : subOfBoth rhs a b = true) :
    ∀ x y, (Term.bi id .usubSat a b).denote ρ = some x → rhs.denote ρ = some y → BitVec.ule x y = true := by
  intro x y hx hy
  simp only [Term.Consistent] at cl
  obtain ⟨-, -, he⟩ := cl
  have hx' : ρ w id = some x := hx
  rw [← he] at hx'
  obtain ⟨av, bv, ha, hb⟩ := map₂_strict hx'
  rw [ha, hb] at hx'
  simp only [BinIntr.eval, Val.usubSat, Val.map₂, Option.some.injEq] at hx'
  subst hx'
  unfold subOfBoth at h
  split at h
  · next f x' y' hsub =>
    have he' := ok_inj (bin_val hsub cr)
    rw [hy] at he'
    obtain ⟨px, py, hpx, hpy, rfl⟩ := sub_some he'
    simp only [Bool.and_eq_true] at h
    rw [specific_denote h.1, ha] at hpx
    rw [specific_denote h.2, hb] at hpy
    cases hpx; cases hpy
    exact Lemmas.usubSat_ule_sub _ _
  · cases h

/-- `IS.simplifyICmpWithIntrinsicOnLHS.L3826`: `uadd.sat(X, Y) >=u X + Y` to true. -/
theorem simplifyICmpWithIntrinsicOnLHS.L3826 (ρ : Env) (p : Pred) (s : Bool) (id : Nat) (a b rhs : Term w)
    (cl : (Term.bi id .uaddSat a b).Consistent ρ) (cr : rhs.Consistent ρ) (h : (addOf rhs a b && p == .uge) = true) :
    Refines ((icmpSrc p s (.bi id .uaddSat a b) rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  exact refines_bool (uaddSat_add_val cl cr h)

/-- `IS.simplifyICmpWithIntrinsicOnLHS.L3828`: `uadd.sat(X, Y) <u X + Y` to false. -/
theorem simplifyICmpWithIntrinsicOnLHS.L3828 (ρ : Env) (p : Pred) (s : Bool) (id : Nat) (a b rhs : Term w)
    (cl : (Term.bi id .uaddSat a b).Consistent ρ) (cr : rhs.Consistent ρ) (h : (addOf rhs a b && p == .ult) = true) :
    Refines ((icmpSrc p s (.bi id .uaddSat a b) rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  have := uaddSat_add_val cl cr h x y hx hy
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-- `IS.simplifyICmpWithIntrinsicOnLHS.L3836`: `usub.sat(X, Y) <=u X - Y` to true. -/
theorem simplifyICmpWithIntrinsicOnLHS.L3836 (ρ : Env) (p : Pred) (s : Bool) (id : Nat) (a b rhs : Term w)
    (cl : (Term.bi id .usubSat a b).Consistent ρ) (cr : rhs.Consistent ρ)
    (h : (subOfBoth rhs a b && p == .ule) = true) :
    Refines ((icmpSrc p s (.bi id .usubSat a b) rhs).eval ρ) ((boolR true).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  exact refines_bool (usubSat_sub_val cl cr h)

/-- `IS.simplifyICmpWithIntrinsicOnLHS.L3838`: `usub.sat(X, Y) >u X - Y` to false. -/
theorem simplifyICmpWithIntrinsicOnLHS.L3838 (ρ : Env) (p : Pred) (s : Bool) (id : Nat) (a b rhs : Term w)
    (cl : (Term.bi id .usubSat a b).Consistent ρ) (cr : rhs.Consistent ρ)
    (h : (subOfBoth rhs a b && p == .ugt) = true) :
    Refines ((icmpSrc p s (.bi id .usubSat a b) rhs).eval ρ) ((boolR false).eval ρ) := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, rfl⟩ := h
  refine refines_bool fun x y hx hy => ?_
  have := usubSat_sub_val cl cr h x y hx hy
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
  omega

/-- Theorem 1 for `simplifyICmpWithIntrinsicOnLHS`: every value the model returns refines `icmp [samesign] Pred LHS,
RHS`, at every width, predicate and `samesign` flag, in every run the operands are consistent with, poison
included. -/
theorem simplifyICmpWithIntrinsicOnLHS.sound (ρ : Env) (p : Pred) (s : Bool) (lhs rhs : Term w)
    (cl : lhs.Consistent ρ) (cr : rhs.Consistent ρ) {r : Repl 1}
    (h : simplifyICmpWithIntrinsicOnLHS p lhs rhs = .value r) :
    Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifyICmpWithIntrinsicOnLHS.steps p lhs rhs →
      Refines ((icmpSrc p s lhs rhs).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifyICmpWithIntrinsicOnLHS.steps at hmem
  split at hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
      obtain ⟨-, rfl⟩ := h
    · exact simplifyICmpWithIntrinsicOnLHS.L3826 ρ p s _ _ _ rhs cl cr (by assumption)
    · exact simplifyICmpWithIntrinsicOnLHS.L3828 ρ p s _ _ _ rhs cl cr (by assumption)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h <;>
      obtain ⟨-, rfl⟩ := h
    · exact simplifyICmpWithIntrinsicOnLHS.L3836 ρ p s _ _ _ rhs cl cr (by assumption)
    · exact simplifyICmpWithIntrinsicOnLHS.L3838 ρ p s _ _ _ rhs cl cr (by assumption)
  · simp at hmem

end Peephole.IS.ICmpB
