import Peephole.IS.ICmpBSelect

/-! # InstSimplify's `simplifySelectWithICmpCond`, and its rewrites for every input

`simplifySelectWithICmpCond` is at `llvm/lib/Analysis/InstructionSimplify.cpp:4826-4941` at `llvmorg-23.1.3`;
`simplifySelectInst` forwards to it. It forwards to `simplifyCmpSelOfMaxMin`, which `ICmpBSelect` models and proves.
Each step that rewrites carries its ID from `tests/llvm_scope/rewrites/instsimplify.json`, and each proved one has a
theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifySelectWithICmpCond.L4857` | `X > MIN_INT ? X : MIN_INT` to `X`, and the like: delegated, see below |
| `IS.simplifySelectWithICmpCond.L4876` | `(ShAmt == 0) ? fshl(X, *, ShAmt) : X` and the `fshr` form to `X` |
| `IS.simplifySelectWithICmpCond.L4890` | `(ShAmt == 0) ? X : fshl(X, X, ShAmt)` and the `fshr` form to the rotate |
| `IS.simplifySelectWithICmpCond.L4896` | `X == 0 ? abs(X) : -abs(X)` to `-abs(X)` |
| `IS.simplifySelectWithICmpCond.L4900` | `X == 0 ? -abs(X) : abs(X)` to `abs(X)` |

The inventory tags the last four `fp`, from names on their path, but they're about integers only: funnel shifts and
`abs`. L4857 rests on `matchDecomposedSelectPattern`, ValueTracking's recognizer of min/max `select`s, which this
family doesn't model: the model takes whether the C++ returns `X` there as a parameter, `SPLimit`, and delegates.
`simplifySelectBitTest` is modelled only as far as whether it answers, which is delegated, and
`simplifySelectWithEquivalence`, which needs `simplifyWithOpsReplaced`, is delegated where it's called.

`simplifySelectWithICmpCond.sound` puts the rest together: every value the model returns refines the `select`, at every
positive width, predicate and `samesign` flag, poison included. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w u : Nat}

/-! ### Matchers -/

/-- `m_And(m_Value(X), m_APInt(Y))`, binding `X` and `Y`. -/
def andConst? (t : Term w) : Option (Term w × BitVec w) :=
  match binop? .and t with
  | some (_, x, yc) =>
    match apint yc with
    | some y => some (x, y)
    | none => none
  | none => none

/-- `match(V, m_And(m_Specific(X), m_APInt(C))) && *Y == ~*C`. -/
def andNotOf (v x : Term w) (y : BitVec w) : Bool :=
  match binop? .and v with
  | some (_, a, ct) => specific x a && (match apint ct with | some c => y == ~~~c | none => false)
  | none => false

/-- `match(V, m_Or(m_Specific(X), m_APInt(C))) && *Y == *C`. -/
def orOf (v x : Term w) (y : BitVec w) : Bool :=
  match binop? .or v with
  | some (_, a, ct) => specific x a && (match apint ct with | some c => y == c | none => false)
  | none => false

/-- `cast<PossiblyDisjointInst>(V)->isDisjoint()`. -/
def disjointFlag : Term w → Bool
  | .bin _ _ f .. => f.disjoint
  | _ => false

/-- Whether `simplifySelectBitTest(TrueVal, FalseVal, X, Y, TrueWhenUnset)` answers, rather than returning `nullptr`.
What it answers is delegated. -/
def selectBitTestAnswers (tv fv x : Term w) (y : BitVec w) (twu : Bool) : Bool :=
  (specific x fv && andNotOf tv x y) || (specific x tv && andNotOf fv x y) ||
    (decide y.toNat.isPowerOfTwo &&
      (if specific x fv && orOf tv x y then !(twu && disjointFlag tv)
       else specific x tv && orOf fv x y && !(!twu && disjointFlag fv)))

/-- `m_CombineOr(m_FShl(m_Value(X), m_Value(), m_Value(ShAmt)), m_FShr(m_Value(), m_Value(X), m_Value(ShAmt)))`,
binding `X` and `ShAmt`. -/
def isFsh? : Term w → Option (Term w × Term w)
  | .fsh _ true x _ sh => some (x, sh)
  | .fsh _ false _ x sh => some (x, sh)
  | _ => none

/-- `m_CombineOr(m_FShl(m_Value(X), m_Deferred(X), m_Value(ShAmt)), m_FShr(...))`, binding `X` and `ShAmt`. -/
def isRotate? : Term w → Option (Term w × Term w)
  | .fsh _ _ x y sh => if specific x y then some (x, sh) else none
  | _ => none

/-- `m_Intrinsic<Intrinsic::abs>(m_Specific(V))`, either flag. -/
def absOf (v t : Term w) : Bool :=
  match t with
  | .un _ (.abs _) a => specific v a
  | _ => false

/-- `m_Neg(m_Intrinsic<Intrinsic::abs>(m_Specific(V)))`. -/
def negAbsOf (v t : Term w) : Bool :=
  match neg? t with
  | some a => absOf v a
  | none => false

/-- `matchDecomposedSelectPattern`'s min/max limit test, which this family doesn't model: whether
`SelectPatternResult::isMinOrMax(SPF) && Pred == getMinMaxPred(SPF)` and `Y` is `getMinMaxLimit` of the inverse flavor,
so that the C++ returns `X`. Given the compare and the arms after `ne` is made `eq`; its answers are delegated. -/
abbrev SPLimit := Term 1 → {w : Nat} → Term w → Term w → Bool

/-! ### The model -/

/-- The steps under `Pred == ICMP_EQ && match(CmpRHS, m_Zero())`, once the compare's operands and the arms have one
width. With other widths none of them can match: `X`, `ShAmt` and `abs`'s operand would be one pointer at two types. -/
def selCondSame.steps (p : Pred) (cl cr tv fv : Term w) : List (Step w) :=
  if p == .eq && zero cr then
    [ match andConst? cl with
      | some (x, y) => if selectBitTestAnswers tv fv x y true then .delegate "simplifySelectBitTest" else .next
      | none => .next,
      -- (ShAmt == 0) ? fshl(X, *, ShAmt) : X --> X
      -- (ShAmt == 0) ? fshr(*, X, ShAmt) : X --> X
      match isFsh? tv with
      | some (x, sh) =>
        if specific x fv && specific sh cl then .fire "IS.simplifySelectWithICmpCond.L4876" (.old x) else .next
      | none => .next,
      -- (ShAmt == 0) ? X : fshl(X, X, ShAmt) --> fshl(X, X, ShAmt)
      -- (ShAmt == 0) ? X : fshr(X, X, ShAmt) --> fshr(X, X, ShAmt)
      match isRotate? fv with
      | some (x, sh) =>
        if specific x tv && specific sh cl && p == .eq then .fire "IS.simplifySelectWithICmpCond.L4890" (.old fv)
        else .next
      | none => .next,
      -- X == 0 ? abs(X) : -abs(X) --> -abs(X)
      if absOf cl tv && negAbsOf cl fv then .fire "IS.simplifySelectWithICmpCond.L4896" (.old fv) else .next,
      -- X == 0 ? -abs(X) : abs(X) --> abs(X)
      if negAbsOf cl tv && absOf cl fv then .fire "IS.simplifySelectWithICmpCond.L4900" (.old fv) else .next ]
  else []

/-- `simplifySelectWithICmpCond(CondVal, TrueVal, FalseVal, Q, MaxRecurse)`, step by step. -/
def _root_.Peephole.IS.simplifySelectWithICmpCond.steps (spl : SPLimit) (cond : Term 1) (tv fv : Term w) :
    List (Step w) :=
  match cond with
  | .icmp (w := u) cid p s cl cr =>
    -- Canonicalize ne to eq predicate.
    let p' := if p == .ne then Pred.eq else p
    let tv' := if p == .ne then fv else tv
    let fv' := if p == .ne then tv else fv
    [ fwd "IS.simplifyCmpSelOfMaxMin" (simplifyCmpSelOfMaxMin cl cr p tv fv),
      -- Check for integer min/max with a limit constant:
      -- X > MIN_INT ? X : MIN_INT --> X
      -- X < MAX_INT ? X : MAX_INT --> X
      if spl (.icmp cid p s cl cr) tv' fv' then .delegate "matchDecomposedSelectPattern" else .next ] ++
    (if h : u = w then selCondSame.steps p' (h ▸ cl) (h ▸ cr) tv' fv' else []) ++
    [ -- If we have a scalar equality comparison, then we know the value in one of
      -- the arms of the select. See if substituting this value into the arm and
      -- simplifying the result yields the same value as the other arm.
      if p' == .eq then .delegate "simplifySelectWithEquivalence" else .next ]
  | _ => []

def _root_.Peephole.IS.simplifySelectWithICmpCond (spl : SPLimit) (cond : Term 1) (tv fv : Term w) : Result w :=
  run (simplifySelectWithICmpCond.steps spl cond tv fv)

/-! ### The rewrites, one theorem each -/

theorem select_ofBool (b : Bool) (t e : Val w) :
    IRLean.select (some (BitVec.ofBool b)) t e = if b then t else e := by
  cases b <;> rfl

/-- `select (X == 0), T, E` refines `R` where it's `R` wherever `X` is 0 and `E` isn't poison, and `E` refines `R`
wherever `X` isn't 0. -/
theorem eqZero_refines {ρ : Env} {s : Bool} {cl cr tv fv : Term w} {r : Repl w} (hz : zero cr = true)
    (hr : ∃ v, r.eval ρ = Outcome.ok v ∧
      (cl.denote ρ = some 0#w → Refine.le (tv.denote ρ) v) ∧
      (∀ k, cl.denote ρ = some k → k ≠ 0#w → Refine.le (fv.denote ρ) v)) :
    Refines ((selSrc .eq s cl cr tv fv).eval ρ) (r.eval ρ) := by
  obtain ⟨v, hv, h0, h1⟩ := hr
  rw [selSrc_eval, hv, cst_eq hz]
  refine refines_ok ?_
  cases hk : cl.denote ρ with
  | none => rw [eval_none_left]; exact Refine.val_none _
  | some k =>
  rw [eval_some]
  split
  · exact Refine.val_none _
  · rw [select_ofBool]
    by_cases hk0 : k = 0#w
    · subst hk0
      simp only [test, BEq.rfl, ite_true]
      exact h0 hk
    · have : (k == 0#w) = false := by simp [hk0]
      simp only [test, this, Bool.false_eq_true, ite_false]
      exact h1 k hk hk0

theorem isFsh?_val {ρ : Env} {t x sh : Term w} (hf : isFsh? t = some (x, sh)) (ct : t.Consistent ρ)
    (h0 : sh.denote ρ = some 0#w) : Refine.le (t.denote ρ) (x.denote ρ) := by
  cases t with
  | fsh id l a b c =>
    simp only [Term.Consistent] at ct
    obtain ⟨-, -, -, he⟩ := ct
    show Refine.le (ρ w id) _
    rw [← he]
    cases l
    · simp only [isFsh?, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [h0]
      cases ha : a.denote ρ <;> cases hb : b.denote ρ <;>
        simp only [Bool.false_eq_true, ite_false, Val.fshr] <;> try exact Refine.val_none _
      simp [Val.fshrRaw]
      exact Refine.refl_val _
    · simp only [isFsh?, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [h0]
      cases ha : a.denote ρ <;> cases hb : b.denote ρ <;>
        simp only [ite_true, Val.fshl] <;> try exact Refine.val_none _
      simp [Val.fshlRaw]
      exact Refine.refl_val _
  | _ => simp [isFsh?] at hf

theorem isRotate?_val {ρ : Env} {t x sh : Term w} (hf : isRotate? t = some (x, sh)) (ct : t.Consistent ρ)
    (h0 : sh.denote ρ = some 0#w) : Refine.le (x.denote ρ) (t.denote ρ) := by
  cases t with
  | fsh id l a b c =>
    simp only [isRotate?] at hf
    split at hf
    · next hab =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Term.Consistent] at ct
      obtain ⟨-, -, -, he⟩ := ct
      show Refine.le _ (ρ w id)
      rw [← he, h0, specific_denote hab]
      cases ha : a.denote ρ
      · exact Refine.val_none _
      · cases l <;> simp [Val.fshl, Val.fshr, Val.fshlRaw, Val.fshrRaw] <;> exact Refine.refl_val _
    · cases hf
  | _ => simp [isRotate?] at hf

/-- `IS.simplifySelectWithICmpCond.L4876`: `(ShAmt == 0) ? fshl(X, *, ShAmt) : X` and
`(ShAmt == 0) ? fshr(*, X, ShAmt) : X` to `X`, after `ne` is made `eq`. -/
theorem _root_.Peephole.IS.simplifySelectWithICmpCond.L4876 (ρ : Env) (s : Bool) (cl cr tv fv x sh : Term w)
    (ct : tv.Consistent ρ) (hz : zero cr = true) (hf : isFsh? tv = some (x, sh))
    (h : (specific x fv && specific sh cl) = true) :
    Refines ((selSrc .eq s cl cr tv fv).eval ρ) ((Repl.old x).eval ρ) := by
  rw [Bool.and_eq_true] at h
  obtain ⟨hx, hs⟩ := h
  refine eqZero_refines hz ⟨x.denote ρ, rfl, fun h0 => ?_, fun k _ _ => ?_⟩
  · rw [specific_denote hs] at h0
    exact isFsh?_val hf ct h0
  · rw [specific_denote hx]
    exact Refine.refl_val _

/-- `IS.simplifySelectWithICmpCond.L4890`: `(ShAmt == 0) ? X : fshl(X, X, ShAmt)` and the `fshr` form to the rotate,
after `ne` is made `eq`. -/
theorem _root_.Peephole.IS.simplifySelectWithICmpCond.L4890 (ρ : Env) (s : Bool) (cl cr tv fv x sh : Term w)
    (cf : fv.Consistent ρ) (hz : zero cr = true) (hf : isRotate? fv = some (x, sh))
    (h : (specific x tv && specific sh cl && (Pred.eq == .eq)) = true) :
    Refines ((selSrc .eq s cl cr tv fv).eval ρ) ((Repl.old fv).eval ρ) := by
  simp only [Bool.and_eq_true, BEq.rfl, and_true] at h
  obtain ⟨hx, hs⟩ := h
  refine eqZero_refines hz ⟨fv.denote ρ, rfl, fun h0 => ?_, fun _ _ _ => Refine.refl_val _⟩
  rw [specific_denote hs] at h0
  rw [specific_denote hx]
  exact isRotate?_val hf cf h0

theorem abs_zero (hw : 0 < w) (f : Bool) : Val.abs (some 0#w) f = some 0#w := by
  have : (0#w == BitVec.intMin w) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.toNat_intMin] at this
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))] at this
    have := Nat.two_pow_pos (w - 1)
    omega
  simp [Val.abs, this]

theorem absOf_zero {ρ : Env} {v t : Term w} (hw : 0 < w) (h : absOf v t = true) (ct : t.Consistent ρ)
    (hv : v.denote ρ = some 0#w) : t.denote ρ = some 0#w := by
  unfold absOf at h
  split at h
  · next id f a =>
    simp only [Term.Consistent] at ct
    obtain ⟨-, he⟩ := ct
    rw [show Term.denote ρ (Term.un id (.abs f) a) = ρ w id from rfl, ← he, specific_denote h, hv]
    exact abs_zero hw f
  · cases h

theorem negAbsOf_zero {ρ : Env} {v t : Term w} (hw : 0 < w) (h : negAbsOf v t = true) (ct : t.Consistent ρ)
    (hv : v.denote ρ = some 0#w) : t.denote ρ = some 0#w := by
  unfold negAbsOf neg? at h
  split at h
  · next a hn =>
    split at hn
    · next f z b hb =>
      split at hn
      · next hz =>
        simp only [Option.some.injEq] at hn
        subst hn
        have he := ok_inj (bin_val hb ct)
        have hc := (binop?_consistent hb ct).2.1
        rw [cst_eq hz, absOf_zero hw h hc hv] at he
        rw [← he]
        simp [Val.sub, BitVec.ssubOverflow_eq, BitVec.usubOverflow_eq]
      · cases hn
    · cases hn
  · cases h

/-- `IS.simplifySelectWithICmpCond.L4896`: `X == 0 ? abs(X) : -abs(X)` to `-abs(X)`, at a positive width. -/
theorem _root_.Peephole.IS.simplifySelectWithICmpCond.L4896 (ρ : Env) (s : Bool) (cl cr tv fv : Term w) (hw : 0 < w)
    (ct : tv.Consistent ρ) (cf : fv.Consistent ρ) (hz : zero cr = true) (h : (absOf cl tv && negAbsOf cl fv) = true) :
    Refines ((selSrc .eq s cl cr tv fv).eval ρ) ((Repl.old fv).eval ρ) := by
  rw [Bool.and_eq_true] at h
  refine eqZero_refines hz ⟨fv.denote ρ, rfl, fun h0 => ?_, fun _ _ _ => Refine.refl_val _⟩
  rw [absOf_zero hw h.1 ct h0, negAbsOf_zero hw h.2 cf h0]
  exact Refine.refl_val _

/-- `IS.simplifySelectWithICmpCond.L4900`: `X == 0 ? -abs(X) : abs(X)` to `abs(X)`, at a positive width. -/
theorem _root_.Peephole.IS.simplifySelectWithICmpCond.L4900 (ρ : Env) (s : Bool) (cl cr tv fv : Term w) (hw : 0 < w)
    (ct : tv.Consistent ρ) (cf : fv.Consistent ρ) (hz : zero cr = true) (h : (negAbsOf cl tv && absOf cl fv) = true) :
    Refines ((selSrc .eq s cl cr tv fv).eval ρ) ((Repl.old fv).eval ρ) := by
  rw [Bool.and_eq_true] at h
  refine eqZero_refines hz ⟨fv.denote ρ, rfl, fun h0 => ?_, fun _ _ _ => Refine.refl_val _⟩
  rw [negAbsOf_zero hw h.1 ct h0, absOf_zero hw h.2 cf h0]
  exact Refine.refl_val _

/-! ### The fold -/

theorem ite_delegate_ne_fire {c : Prop} [Decidable c] {d site : String} {r : Repl w} :
    (if c then Step.delegate d else Step.next : Step w) ≠ Step.fire site r := by
  split <;> simp

/-- The `select` the fold replaces: `select CondVal, TrueVal, FalseVal`. -/
def selectSrc (c : Term 1) (tv fv : Term w) : Repl w := .select (.old c) (.old tv) (.old fv)

theorem selectSrc_eval (ρ : Env) (c : Term 1) (tv fv : Term w) :
    (selectSrc c tv fv).eval ρ = Outcome.ok (IRLean.select (c.denote ρ) (tv.denote ρ) (fv.denote ρ)) := rfl

theorem selCondSame.steps_sound (ρ : Env) (p : Pred) (s : Bool) (cl cr tv fv : Term w) (hw : 0 < w)
    (ct : tv.Consistent ρ) (cf : fv.Consistent ρ) :
    ∀ site r, Step.fire site r ∈ selCondSame.steps p cl cr tv fv →
      Refines ((selSrc p s cl cr tv fv).eval ρ) (r.eval ρ) := by
  intro site r hmem
  unfold selCondSame.steps at hmem
  split at hmem
  · next hp =>
    rw [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hz⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h
    · split at h
      · split at h <;> cases h
      · cases h
    · split at h
      · next x sh hf =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact simplifySelectWithICmpCond.L4876 ρ s cl cr tv fv x sh ct hz hf (by assumption)
      · cases h
    · split at h
      · next x sh hf =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := h
        exact simplifySelectWithICmpCond.L4890 ρ s cl cr tv fv x sh cf hz hf (by assumption)
      · cases h
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifySelectWithICmpCond.L4896 ρ s cl cr tv fv hw ct cf hz (by assumption)
    · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifySelectWithICmpCond.L4900 ρ s cl cr tv fv hw ct cf hz (by assumption)
  · simp at hmem

/-- Theorem 1 for `simplifySelectWithICmpCond`: every value the model returns refines
`select CondVal, TrueVal, FalseVal`, at every positive width, predicate and `samesign` flag, in every run the operands
are consistent with, poison included, for whatever `matchDecomposedSelectPattern` answers. -/
theorem _root_.Peephole.IS.simplifySelectWithICmpCond.sound (ρ : Env) (spl : SPLimit) (cond : Term 1) (tv fv : Term w)
    (hw : 0 < w) (cc : cond.Consistent ρ) (ct : tv.Consistent ρ) (cf : fv.Consistent ρ) {r : Repl w}
    (h : simplifySelectWithICmpCond spl cond tv fv = .value r) :
    Refines ((selectSrc cond tv fv).eval ρ) (r.eval ρ) := by
  suffices hs : ∀ site r, Step.fire site r ∈ simplifySelectWithICmpCond.steps spl cond tv fv →
      Refines ((selectSrc cond tv fv).eval ρ) (r.eval ρ) from run_sound hs h
  intro site r hmem
  unfold simplifySelectWithICmpCond.steps at hmem
  split at hmem
  · next u cid p s cl cr =>
    simp only [Term.Consistent] at cc
    obtain ⟨-, -, hcond⟩ := cc
    have hsrc : (selectSrc (.icmp cid p s cl cr) tv fv).eval ρ = (selSrc p s cl cr tv fv).eval ρ := by
      rw [selectSrc_eval, selSrc_eval]
      rw [show Term.denote ρ (Term.icmp cid p s cl cr) = ρ 1 cid from rfl, ← hcond]
    rw [hsrc]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact simplifyCmpSelOfMaxMin.sound ρ p s cl cr tv fv ct cf (fwd_fire h.symm)
    · exact absurd h.symm ite_delegate_ne_fire
    · split at h
      · next hu =>
        subst hu
        -- the `select` with `ne` made `eq` and its arms swapped
        have hcanon : (selSrc p s cl cr tv fv).eval ρ =
            (selSrc (if p == .ne then Pred.eq else p) s cl cr (if p == .ne then fv else tv)
              (if p == .ne then tv else fv)).eval ρ := by
          split
          · next hp =>
            rw [beq_iff_eq] at hp
            subst hp
            rw [selSrc_eval, selSrc_eval, ← select_inv .eq]
            rfl
          · rfl
        rw [hcanon]
        exact selCondSame.steps_sound ρ _ s cl cr _ _ hw
          (by split <;> assumption) (by split <;> assumption) site r h
      · simp at h
    · exact absurd h.symm ite_delegate_ne_fire
  · simp at hmem

end Peephole.IS.ICmpB
