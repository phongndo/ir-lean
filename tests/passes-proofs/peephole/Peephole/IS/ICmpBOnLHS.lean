import Peephole.IS.ICmpB

/-! # InstSimplify's `simplifyICmpWithBinOpOnLHS`, and its rewrites for every input

`simplifyICmpWithBinOpOnLHS` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3227-3332` at `llvmorg-23.1.3`. It
answers for `icmp Pred LBO, RHS` where `LBO` is a binary operator, and `simplifyICmpWithBinOp` forwards to it twice, the
second time with the operands and the predicate swapped. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpWithBinOpOnLHS.L3239` | `(X \| Y) <s X` to true, `>=s` to false, where `X >= 0` and `Y < 0` are known |
| `IS.simplifyICmpWithBinOpOnLHS.L3241` | `(X \| Y) <s X` to false, `>=s` to true, where `X < 0` or `Y >= 0` is known |
| `IS.simplifyICmpWithBinOpOnLHS.L3260` | `(X urem Y) == Y`, `>u`, `>=u`, and `>s`, `>=s` where `Y >= 0` is known, to false |
| `IS.simplifyICmpWithBinOpOnLHS.L3271` | `(X urem Y) != Y`, `<u`, `<=u`, and `<s`, `<=s` where `Y >= 0` is known, to true |
| `IS.simplifyICmpWithBinOpOnLHS.L3295` | `X >>u C` or `X udiv C` against a known non-zero `X`: `==`, `>=u`, `>u` to false |
| `IS.simplifyICmpWithBinOpOnLHS.L3299` | the same: `!=`, `<u`, `<=u` to true |
| `IS.simplifyICmpWithBinOpOnLHS.L3321` | `(X * C1) udiv C2 >u X`, and the shift forms, to false |
| `IS.simplifyICmpWithBinOpOnLHS.L3323` | `(X * C1) udiv C2 <=u X`, and the shift forms, to true |
| `IS.simplifyICmpWithBinOpOnLHS.L3330` | `(C - X) == X` to false and `!=` to true, for odd `C` |

`simplifyICmpWithBinOpOnLHS.sound` puts them together: every value the model returns refines the compare, at every
width, predicate and `samesign` flag, poison included. It rests on the oracle's answers being sound, PASS-01's. -/

namespace Peephole.IS.ICmpB

open IRLean

variable {w : Nat}

/-! ### Matchers -/

/-- `m_c_Or(m_Value(Y), m_Specific(S))` on `V`, binding `Y`: operand 0 if operand 1 is `S`, else operand 1 if operand
0 is. -/
def orOther (v s : Term w) : Option (Term w) :=
  match binop? .or v with
  | some (_, a, b) => if specific s b then some a else if specific s a then some b else none
  | none => none

/-- `m_URem(m_Value(), m_Specific(S))`. -/
def uremOf (v s : Term w) : Bool :=
  match binop? .urem v with
  | some (_, _, b) => specific s b
  | none => false

/-- `match(V, m_LShr(m_Specific(S), m_APInt(C))) && *C != 0`. -/
def lshrOf (v s : Term w) : Bool :=
  match binop? .lshr v with
  | some (_, a, c) => specific s a && (match apint c with | some c => c.toNat != 0 | none => false)
  | none => false

/-- `match(V, m_UDiv(m_Specific(S), m_APInt(C))) && *C != 1`. -/
def udivOf (v s : Term w) : Bool :=
  match binop? .udiv v with
  | some (_, a, c) => specific s a && (match apint c with | some c => c.toNat != 1 | none => false)
  | none => false

/-- `match(V, m_UDiv(m_Mul(m_Specific(S), m_APInt(C1)), m_APInt(C2))) && C1->ule(*C2)`. -/
def mulUDiv (v s : Term w) : Bool :=
  match binop? .udiv v with
  | some (_, m, c2) =>
    match binop? .mul m, apint c2 with
    | some (_, x, c1), some c2 => specific s x && (match apint c1 with | some c1 => c1.ule c2 | none => false)
    | _, _ => false
  | none => false

/-- `match(V, m_LShr(m_Mul(m_Specific(S), m_APInt(C1)), m_APInt(C2))) && C1->ule(APInt(W, 1) << *C2)`. `APInt`'s
`<<` by an amount past the width gives 0, as `BitVec`'s does. -/
def mulLShr (v s : Term w) : Bool :=
  match binop? .lshr v with
  | some (_, m, c2) =>
    match binop? .mul m, apint c2 with
    | some (_, x, c1), some c2 =>
      specific s x && (match apint c1 with | some c1 => c1.ule (1#w <<< c2) | none => false)
    | _, _ => false
  | none => false

/-- `match(V, m_UDiv(m_Shl(m_Specific(S), m_APInt(C1)), m_APInt(C2))) && (APInt(W, 1) << *C1).ule(*C2)`. -/
def shlUDiv (v s : Term w) : Bool :=
  match binop? .udiv v with
  | some (_, m, c2) =>
    match binop? .shl m, apint c2 with
    | some (_, x, c1), some c2 =>
      specific s x && (match apint c1 with | some c1 => (1#w <<< c1).ule c2 | none => false)
    | _, _ => false
  | none => false

/-- `match(V, m_Sub(m_APIntAllowPoison(C), m_Specific(S))) && (*C & 1) == 1`. -/
def subOdd (v s : Term w) : Bool :=
  match binop? .sub v with
  | some (_, c, x) => specific s x && (match apint c with | some c => (c &&& 1#w).toNat == 1 | none => false)
  | none => false

/-! ### The model -/

/-- `simplifyICmpWithBinOpOnLHS(Pred, LBO, RHS, Q, MaxRecurse)`, step by step. `MaxRecurse` isn't read. A known-bits
query is `o.knownZero` and `o.knownOne`: `isNonNegative` is the sign bit known zero, `isNegative` known one.
`isKnownNonZero` is `o.nonZero`. -/
def _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.steps (o : Oracle) (p : Pred) (lbo rhs : Term w) : List (Step 1) :=
  [ -- icmp pred (or X, Y), X
    match orOther lbo rhs with
    | some y =>
      if (p == .slt || p == .sge) && (o.knownZero rhs).msb && (o.knownOne y).msb then
        .fire "IS.simplifyICmpWithBinOpOnLHS.L3239" (boolR (p == .slt))
      else .next
    | none => .next,
    match orOther lbo rhs with
    | some y =>
      if (p == .slt || p == .sge) && ((o.knownOne rhs).msb || (o.knownZero y).msb) then
        .fire "IS.simplifyICmpWithBinOpOnLHS.L3241" (boolR (!(p == .slt)))
      else .next
    | none => .next,
    -- icmp pred (urem X, Y), Y: `sgt` and `sge` fall through to `false` where `Y` is known non-negative.
    if uremOf lbo rhs &&
        (p == .eq || p == .ugt || p == .uge || ((p == .sgt || p == .sge) && (o.knownZero rhs).msb)) then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3260" (boolR false)
    else .next,
    -- `slt` and `sle` fall through to `true` where `Y` is known non-negative.
    if uremOf lbo rhs &&
        (p == .ne || p == .ult || p == .ule || ((p == .slt || p == .sle) && (o.knownZero rhs).msb)) then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3271" (boolR true)
    else .next,
    -- If x is nonzero:
    -- x >>u C <u  x --> true  for C != 0.
    -- x >>u C !=  x --> true  for C != 0.
    -- x >>u C >=u x --> false for C != 0.
    -- x >>u C ==  x --> false for C != 0.
    -- x udiv C <u  x --> true  for C != 1.
    -- x udiv C !=  x --> true  for C != 1.
    -- x udiv C >=u x --> false for C != 1.
    -- x udiv C ==  x --> false for C != 1.
    if (lshrOf lbo rhs || udivOf lbo rhs) && o.nonZero rhs && (p == .eq || p == .uge || p == .ugt) then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3295" (boolR false)
    else .next,
    if (lshrOf lbo rhs || udivOf lbo rhs) && o.nonZero rhs && (p == .ne || p == .ult || p == .ule) then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3299" (boolR true)
    else .next,
    -- (x*C1)/C2 <= x for C1 <= C2.
    -- (x*C1)>>C2 <= x for C1 < 2**C2.
    -- (x<<C1)/C2 <= x for 2**C1 < C2.
    if (mulUDiv lbo rhs || mulLShr lbo rhs || shlUDiv lbo rhs) && p == .ugt then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3321" (boolR false)
    else .next,
    if (mulUDiv lbo rhs || mulLShr lbo rhs || shlUDiv lbo rhs) && p == .ule then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3323" (boolR true)
    else .next,
    -- (sub C, X) == X, C is odd  --> false
    -- (sub C, X) != X, C is odd  --> true
    if subOdd lbo rhs && isEquality p then
      .fire "IS.simplifyICmpWithBinOpOnLHS.L3330" (boolR (!(p == .eq)))
    else .next ]

/-- `simplifyICmpWithBinOpOnLHS(Pred, LBO, RHS, Q, MaxRecurse)`. `LBO` is a `BinaryOperator`; the model takes it as
an operand, which every matcher here asks for a binary operator anyway. -/
def _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS (o : Oracle) (p : Pred) (lbo rhs : Term w) (_maxRecurse : Nat) : Result 1 :=
  run (simplifyICmpWithBinOpOnLHS.steps o p lbo rhs)

/-! ### The rewrites, one theorem each -/

theorem orOther_val {ρ : Env} {v s y : Term w} {x : BitVec w} (h : orOther v s = some y) (hc : v.Consistent ρ)
    (hx : v.denote ρ = some x) : ∃ yv sv, y.denote ρ = some yv ∧ s.denote ρ = some sv ∧ x = yv ||| sv := by
  unfold orOther at h
  split at h
  · next f a b hb =>
    have he := ok_inj (bin_val hb hc)
    rw [hx] at he
    obtain ⟨pa, pb, ha, hb', hxe⟩ := or_some he
    split at h
    · next hs =>
      cases h
      exact ⟨pa, pb, ha, by rw [← specific_denote hs, hb'], hxe⟩
    · split at h
      · next hs =>
        cases h
        exact ⟨pb, pa, hb', by rw [← specific_denote hs, ha], by rw [hxe, BitVec.or_comm]⟩
      · cases h
  · cases h

/-- `IS.simplifyICmpWithBinOpOnLHS.L3239`: `(X | Y) <s X` to true and `>=s` to false, where `X`'s sign bit is known
zero and `Y`'s known one. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3239 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs y : Term w) (cl : lbo.Consistent ρ) (hy : orOther lbo rhs = some y)
    (hc : ((p == .slt || p == .sge) && (o.knownZero rhs).msb && (o.knownOne y).msb) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR (p == .slt)).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hp, hz⟩, hn⟩ := hc
  refine refines_bool fun x z hx hz' => ?_
  obtain ⟨yv, sv, hyv, hsv, rfl⟩ := orOther_val hy cl hx
  rw [hz'] at hsv
  cases hsv
  have h1 : (yv ||| z).msb = true := by
    rw [BitVec.msb_or, neg_of_knownOne ho hyv hn, Bool.true_or]
  have h2 := Lemmas.slt_of_msb h1 (nonneg_of_knownZero ho hz' hz)
  rcases hp with rfl | rfl
  · exact h2
  · simp only [test, Lemmas.sle_eq_not_slt, h2]; rfl

/-- `IS.simplifyICmpWithBinOpOnLHS.L3241`: `(X | Y) <s X` to false and `>=s` to true, where `X`'s sign bit is known
one or `Y`'s known zero. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3241 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs y : Term w) (cl : lbo.Consistent ρ) (hy : orOther lbo rhs = some y)
    (hc : ((p == .slt || p == .sge) && ((o.knownOne rhs).msb || (o.knownZero y).msb)) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR (!(p == .slt))).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hp, hk⟩ := hc
  refine refines_bool fun x z hx hz' => ?_
  obtain ⟨yv, sv, hyv, hsv, rfl⟩ := orOther_val hy cl hx
  rw [hz'] at hsv
  cases hsv
  have h2 : BitVec.sle z (yv ||| z) = true := by
    apply Lemmas.sle_or_right
    rcases hk with hk | hk
    · exact Or.inl (neg_of_knownOne ho hz' hk)
    · exact Or.inr (nonneg_of_knownZero ho hyv hk)
  rcases hp with rfl | rfl
  · simp only [test]
    rw [← Bool.not_not (BitVec.slt _ _), ← Lemmas.sle_eq_not_slt, h2]; rfl
  · exact h2

theorem uremOf_val {ρ : Env} {v s : Term w} (h : uremOf v s = true) (hc : v.Consistent ρ) :
    ∃ q, s.denote ρ = some q ∧ q ≠ 0#w ∧ ∀ x, v.denote ρ = some x → ∃ p, x = p % q := by
  unfold uremOf at h
  split at h
  · next f a b hb =>
    obtain ⟨q, hq, hq0, hx⟩ := urem_ok (bin_val hb hc)
    refine ⟨q, by rw [← specific_denote h, hq], hq0, fun x hx' => ?_⟩
    obtain ⟨p, -, rfl⟩ := hx x hx'
    exact ⟨p, rfl⟩
  · cases h

/-- `IS.simplifyICmpWithBinOpOnLHS.L3260`: `(X urem Y) == Y`, `>u Y` and `>=u Y` to false, and `>s Y`, `>=s Y` too
where `Y`'s sign bit is known zero. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3260 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (cl : lbo.Consistent ρ)
    (hc : (uremOf lbo rhs &&
      (p == .eq || p == .ugt || p == .uge || ((p == .sgt || p == .sge) && (o.knownZero rhs).msb))) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hu, hp⟩ := hc
  obtain ⟨q, hq, hq0, hv⟩ := uremOf_val hu cl
  refine refines_bool fun x z hx hz => ?_
  rw [hq] at hz
  cases hz
  obtain ⟨pv, rfl⟩ := hv x hx
  have hl := Lemmas.umod_lt (x := pv) hq0
  rcases hp with ((rfl | rfl) | rfl) | ⟨rfl | rfl, hk⟩
  · simp only [test, beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hl
    simp [BitVec.ult] at hl
  · simp only [test, BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at hl ⊢
    omega
  · simp only [test]
    rw [Lemmas.ule_eq_not_ult, hl]; rfl
  · have := Lemmas.umod_slt (x := pv) hq0 (nonneg_of_knownZero ho hq hk)
    simp only [test, BitVec.slt, decide_eq_true_eq, decide_eq_false_iff_not] at this ⊢
    omega
  · have := Lemmas.umod_slt (x := pv) hq0 (nonneg_of_knownZero ho hq hk)
    simp only [test]
    rw [Lemmas.sle_eq_not_slt, this]; rfl

/-- `IS.simplifyICmpWithBinOpOnLHS.L3271`: `(X urem Y) != Y`, `<u Y` and `<=u Y` to true, and `<s Y`, `<=s Y` too
where `Y`'s sign bit is known zero. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3271 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (cl : lbo.Consistent ρ)
    (hc : (uremOf lbo rhs &&
      (p == .ne || p == .ult || p == .ule || ((p == .slt || p == .sle) && (o.knownZero rhs).msb))) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hu, hp⟩ := hc
  obtain ⟨q, hq, hq0, hv⟩ := uremOf_val hu cl
  refine refines_bool fun x z hx hz => ?_
  rw [hq] at hz
  cases hz
  obtain ⟨pv, rfl⟩ := hv x hx
  have hl := Lemmas.umod_lt (x := pv) hq0
  rcases hp with ((rfl | rfl) | rfl) | ⟨rfl | rfl, hk⟩
  · simp only [test, bne_iff_ne, ne_eq]
    intro he
    rw [he] at hl
    simp [BitVec.ult] at hl
  · exact hl
  · simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq] at hl ⊢
    omega
  · exact Lemmas.umod_slt hq0 (nonneg_of_knownZero ho hq hk)
  · have := Lemmas.umod_slt (x := pv) hq0 (nonneg_of_knownZero ho hq hk)
    simp only [test, BitVec.slt, BitVec.sle, decide_eq_true_eq] at this ⊢
    omega

theorem shrDiv_val {ρ : Env} {v s : Term w} (h : (lshrOf v s || udivOf v s) = true) (hc : v.Consistent ρ) :
    ∀ x z, v.denote ρ = some x → s.denote ρ = some z → z ≠ 0#w → BitVec.ult x z = true := by
  intro x z hx hz hz0
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold lshrOf at h
    split at h
    · next f a c hb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨ha, hcst⟩ := h
      split at hcst
      · next cv hcv =>
        have he := ok_inj (bin_val hb hc)
        rw [hx] at he
        obtain ⟨pa, pc, hpa, hpc, -, rfl⟩ := lshr_some he
        rw [specific_denote ha, hz] at hpa
        cases hpa
        rw [apint_denote hcv] at hpc
        cases hpc
        exact Lemmas.ushiftRight_ult hz0 (by simpa using hcst)
      · cases hcst
    · cases h
  · unfold udivOf at h
    split at h
    · next f a c hb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨ha, hcst⟩ := h
      split at hcst
      · next cv hcv =>
        obtain ⟨q, hq, hq0, hv⟩ := udiv_ok (bin_val hb hc)
        rw [apint_denote hcv] at hq
        cases hq
        obtain ⟨pa, hpa, rfl⟩ := hv x hx
        rw [specific_denote ha, hz] at hpa
        cases hpa
        exact Lemmas.udiv_ult hz0 hq0 (by simpa using hcst)
      · cases hcst
    · cases h

/-- `IS.simplifyICmpWithBinOpOnLHS.L3295`: `X >>u C` (`C != 0`) or `X udiv C` (`C != 1`) `==`, `>=u` or `>u` a known
non-zero `X`, to false. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3295 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (cl : lbo.Consistent ρ)
    (hc : ((lshrOf lbo rhs || udivOf lbo rhs) && o.nonZero rhs && (p == .eq || p == .uge || p == .ugt)) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hm, hn⟩, hp⟩ := hc
  refine refines_bool fun x z hx hz => ?_
  have hl := shrDiv_val hm cl x z hx hz (ho.nonZero rhs z hn hz)
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | rfl
  · simp only [test, beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [he] at hl
    simp [BitVec.ult] at hl
  · simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hl ⊢
    omega
  · simp only [test, BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at hl ⊢
    omega

/-- `IS.simplifyICmpWithBinOpOnLHS.L3299`: `X >>u C` (`C != 0`) or `X udiv C` (`C != 1`) `!=`, `<u` or `<=u` a known
non-zero `X`, to true. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3299 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (cl : lbo.Consistent ρ)
    (hc : ((lshrOf lbo rhs || udivOf lbo rhs) && o.nonZero rhs && (p == .ne || p == .ult || p == .ule)) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hm, hn⟩, hp⟩ := hc
  refine refines_bool fun x z hx hz => ?_
  have hl := shrDiv_val hm cl x z hx hz (ho.nonZero rhs z hn hz)
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (rfl | rfl) | rfl
  · simp only [test, bne_iff_ne, ne_eq]
    intro he
    rw [he] at hl
    simp [BitVec.ult] at hl
  · exact hl
  · simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq] at hl ⊢
    omega

theorem mulDiv_val {ρ : Env} {v s : Term w} (h : (mulUDiv v s || mulLShr v s || shlUDiv v s) = true)
    (hc : v.Consistent ρ) : ∀ x z, v.denote ρ = some x → s.denote ρ = some z → BitVec.ule x z = true := by
  intro x z hx hz
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold mulUDiv at h
    split at h
    · next f m c2 hb =>
      split at h
      · next f' xm c1 c2v hm hc2 =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨hs, hcst⟩ := h
        split at hcst
        · next c1v hc1 =>
          obtain ⟨q, hq, hq0, hv⟩ := udiv_ok (bin_val hb hc)
          rw [apint_denote hc2] at hq
          cases hq
          obtain ⟨pa, hpa, rfl⟩ := hv x hx
          have hcm := (binop?_consistent hb hc).1
          have he := ok_inj (bin_val hm hcm)
          rw [hpa] at he
          obtain ⟨pm, pc, hpm, hpc, rfl⟩ := mul_some he
          rw [specific_denote hs, hz] at hpm
          cases hpm
          rw [apint_denote hc1] at hpc
          cases hpc
          exact Lemmas.mul_udiv_ule hcst
        · cases hcst
      · cases h
    · cases h
  · unfold mulLShr at h
    split at h
    · next f m c2 hb =>
      split at h
      · next f' xm c1 c2v hm hc2 =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨hs, hcst⟩ := h
        split at hcst
        · next c1v hc1 =>
          have he0 := ok_inj (bin_val hb hc)
          rw [hx] at he0
          obtain ⟨pa, pc2, hpa, hpc2, hlt, rfl⟩ := lshr_some he0
          rw [apint_denote hc2] at hpc2
          cases hpc2
          have hcm := (binop?_consistent hb hc).1
          have he := ok_inj (bin_val hm hcm)
          rw [hpa] at he
          obtain ⟨pm, pc, hpm, hpc, rfl⟩ := mul_some he
          rw [specific_denote hs, hz] at hpm
          cases hpm
          rw [apint_denote hc1] at hpc
          cases hpc
          exact Lemmas.mul_ushiftRight_ule hlt hcst
        · cases hcst
      · cases h
    · cases h
  · unfold shlUDiv at h
    split at h
    · next f m c2 hb =>
      split at h
      · next f' xm c1 c2v hm hc2 =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨hs, hcst⟩ := h
        split at hcst
        · next c1v hc1 =>
          obtain ⟨q, hq, hq0, hv⟩ := udiv_ok (bin_val hb hc)
          rw [apint_denote hc2] at hq
          cases hq
          obtain ⟨pa, hpa, rfl⟩ := hv x hx
          have hcm := (binop?_consistent hb hc).1
          have he := ok_inj (bin_val hm hcm)
          rw [hpa] at he
          obtain ⟨pm, pc, hpm, hpc, hlt, rfl, -, -⟩ := shl_some he
          rw [specific_denote hs, hz] at hpm
          cases hpm
          rw [apint_denote hc1] at hpc
          cases hpc
          exact Lemmas.shiftLeft_udiv_ule hlt hcst
        · cases hcst
      · cases h
    · cases h

/-- `IS.simplifyICmpWithBinOpOnLHS.L3321`: `(X * C1) udiv C2 >u X` to false for `C1 <=u C2`, and its forms with
shifts. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3321 (ρ : Env) (p : Pred) (s : Bool) (lbo rhs : Term w)
    (cl : lbo.Consistent ρ) (hc : ((mulUDiv lbo rhs || mulLShr lbo rhs || shlUDiv lbo rhs) && p == .ugt) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR false).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hm, rfl⟩ := hc
  refine refines_bool fun x z hx hz => ?_
  have hl := mulDiv_val hm cl x z hx hz
  simp only [test, BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hl ⊢
  omega

/-- `IS.simplifyICmpWithBinOpOnLHS.L3323`: `(X * C1) udiv C2 <=u X` to true for `C1 <=u C2`, and its forms with
shifts. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3323 (ρ : Env) (p : Pred) (s : Bool) (lbo rhs : Term w)
    (cl : lbo.Consistent ρ) (hc : ((mulUDiv lbo rhs || mulLShr lbo rhs || shlUDiv lbo rhs) && p == .ule) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR true).eval ρ) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hm, rfl⟩ := hc
  exact refines_bool fun x z hx hz => mulDiv_val hm cl x z hx hz

/-- `IS.simplifyICmpWithBinOpOnLHS.L3330`: `(C - X) == X` to false and `!=` to true, for odd `C`. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.L3330 (ρ : Env) (p : Pred) (s : Bool) (lbo rhs : Term w)
    (cl : lbo.Consistent ρ) (hc : (subOdd lbo rhs && isEquality p) = true) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) ((boolR (!(p == .eq))).eval ρ) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hm, hp⟩ := hc
  unfold subOdd at hm
  split at hm
  · next f c xs hb =>
    simp only [Bool.and_eq_true] at hm
    obtain ⟨hs, hcst⟩ := hm
    split at hcst
    · next cv hcv =>
      refine refines_bool fun x z hx hz => ?_
      have he := ok_inj (bin_val hb cl)
      rw [hx] at he
      obtain ⟨pc, px, hpc, hpx, rfl⟩ := sub_some he
      rw [apint_denote hcv] at hpc
      cases hpc
      rw [specific_denote hs, hz] at hpx
      cases hpx
      have hne := Lemmas.sub_ne_of_odd (x := z) (by simpa using hcst)
      simp only [isEquality, Bool.or_eq_true, beq_iff_eq] at hp
      rcases hp with rfl | rfl
      · exact hne
      · simp only [test, bne, hne]; rfl
    · cases hcst
  · cases hm

/-! ### The fold -/

/-- Every step of `simplifyICmpWithBinOpOnLHS` that fires is right. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (cl : lbo.Consistent ρ) :
    ∀ site r, Step.fire site r ∈ simplifyICmpWithBinOpOnLHS.steps o p lbo rhs →
      Refines ((icmpSrc p s lbo rhs).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [simplifyICmpWithBinOpOnLHS.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · split at h
    · next y hy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOpOnLHS.L3239 ρ o ho p s lbo rhs y cl hy (by assumption)
    · cases h
  · split at h
    · next y hy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      obtain ⟨-, rfl⟩ := h
      exact simplifyICmpWithBinOpOnLHS.L3241 ρ o ho p s lbo rhs y cl hy (by assumption)
    · cases h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3260 ρ o ho p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3271 ρ o ho p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3295 ρ o ho p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3299 ρ o ho p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3321 ρ p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3323 ρ p s lbo rhs cl (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyICmpWithBinOpOnLHS.L3330 ρ p s lbo rhs cl (by assumption)

/-- Theorem 1 for `simplifyICmpWithBinOpOnLHS`: every value the model returns refines `icmp [samesign] Pred LBO, RHS`,
at every width, predicate, `samesign` flag and recursion budget, in every run `LBO` is consistent with and the oracle
is sound in, poison included. -/
theorem _root_.Peephole.IS.simplifyICmpWithBinOpOnLHS.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lbo rhs : Term w) (n : Nat) (cl : lbo.Consistent ρ) {r : Repl 1}
    (h : simplifyICmpWithBinOpOnLHS o p lbo rhs n = .value r) :
    Refines ((icmpSrc p s lbo rhs).eval ρ) (r.eval ρ) :=
  run_sound (simplifyICmpWithBinOpOnLHS.steps_sound ρ o ho p s lbo rhs cl) h

end Peephole.IS.ICmpB
