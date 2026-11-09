import Peephole.IS.ArithDiv

/-! # InstSimplify's `simplifyDiv`, `simplifyRem`, and the division entry folds

`simplifyDiv`, `simplifyRem`, `simplifySDivInst`, `simplifyUDivInst`, `simplifySRemInst` and `simplifyURemInst`, at
`llvm/lib/Analysis/InstructionSimplify.cpp:1145-1265` at `llvmorg-23.1.3`, step by step in the C++'s order, with the
theorems for their sites, `IS.simplifyDiv.L1157`, `L1168`, `IS.simplifyRem.L1189`, `L1204`,
`IS.simplifySDivInst.L1216`, `IS.simplifySRemInst.L1246` and `L1250`, and each entry fold's `sound`. The table of
what each rewrites is in `Peephole.IS.ArithDiv`. -/

namespace Peephole.IS

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-! ## `simplifyDiv` -/

/-- `m_NSWMul(m_Value(X), m_Specific(S))` on `V` if `nsw`, else `m_NUWMul`, binding `X`. Not commutative. -/
def wrapMulOf (nsw : Bool) (s v : Term w) : Option (Term w) :=
  match binop? .mul v with
  | some (g, x, b) => if (if nsw then g.nsw else g.nuw) && specific s b then some x else none
  | none => none

/-- `simplifyDiv(Opcode, Op0, Op1, IsExact, Q, MaxRecurse)`, step by step. -/
def simplifyDiv.steps (o : Oracle) (d : DomOracle) (r : Recur) (op : BinOp) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : List (Step w) :=
  [ -- foldOrCommuteConstant: the constant folder folds two constants; a division isn't commutative.
    if op0.isConstant && op1.isConstant then .delegate "ConstantFoldBinaryOpOperands" else .next,
    forward (simplifyDivRem.steps o d r op op0 op1 maxRecurse),
    -- If this is an exact divide by a constant, then the dividend (Op0) must have at least as many trailing zeros as
    -- the divisor to divide evenly. If it has less trailing zeros, then the result must be poison.
    -- `KnownOp0.countMaxTrailingZeros()` is the known ones' trailing zeros.
    match (if isExact then apint op1 else none) with
    | some c =>
      if c.ctz.toNat != 0 && (o.knownOne op0).ctz.toNat < c.ctz.toNat then .fire "IS.simplifyDiv.L1157" .poison
      else .next
    | none => .next,
    -- udiv exact (mul nsw X, C), C --> X
    -- sdiv exact (mul nuw X, C), C --> X
    -- where C is not a power of 2.
    match (if isExact then apint op1 else none) with
    | some c =>
      if ¬ c.toNat.isPowerOfTwo then
        match wrapMulOf (op == .udiv) op1 op0 with
        | some x => .fire "IS.simplifyDiv.L1168" (.old x)
        | none => .next
      else .next
    | none => .next ]

/-- `IS.simplifyDiv.L1157`: `X /exact C` to poison where `X` has a known one below `C`'s lowest set bit: `C` doesn't
divide `X`. -/
theorem simplifyDiv.L1157 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op : BinOp) (hop : op = .udiv ∨ op = .sdiv)
    (op0 op1 : Term w) {c : BitVec w} (hc : apint op1 = some c)
    (hk : (o.knownOne op0).ctz.toNat < c.ctz.toNat) :
    Refines ((binSrc op { exact := true } op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [binSrc_eval, apint_denote hc, Repl.eval_poison]
  cases h0 : op0.denote ρ with
  | none => exact eval_none_left _ _ _ _
  | some a =>
    have hlt : (o.knownOne op0).ctz.toNat < w := Nat.lt_of_lt_of_le hk (ctz_le c)
    have hb := getLsbD_ctz_of_and (ho.knownOne op0 a h0) hlt
    rcases hop with rfl | rfl
    · exact Lemmas.udiv_exact_of_low_bit_refines hb hk
    · exact Lemmas.sdiv_exact_of_low_bit_refines hb hk

theorem wrapMulOf_spec {nsw : Bool} {s v x : Term w} (h : wrapMulOf nsw s v = some x) :
    ∃ g b, binop? .mul v = some (g, x, b) ∧ (if nsw then g.nsw else g.nuw) = true ∧ specific s b = true := by
  unfold wrapMulOf at h
  split at h
  · next g x' b hb =>
    by_cases hc : ((if nsw then g.nsw else g.nuw) && specific s b) = true
    · rw [ite_eq_left hc] at h
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨g, b, hb, hc.1, hc.2⟩
    · rw [ite_eq_right hc] at h
      cases h
  · cases h

/-- `IS.simplifyDiv.L1168`: `udiv exact (mul nsw X, C), C` and `sdiv exact (mul nuw X, C), C` to `X`, for a `C` that
isn't a power of 2. -/
theorem simplifyDiv.L1168 (ρ : Env) (op : BinOp) (hop : op = .udiv ∨ op = .sdiv) (op0 op1 x : Term w)
    {c : BitVec w} (c0 : op0.Consistent ρ) (hc : apint op1 = some c) (hp : ¬ c.toNat.isPowerOfTwo)
    (hm : wrapMulOf (op == .udiv) op1 op0 = some x) :
    Refines ((binSrc op { exact := true } op0 op1).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨g, b, hb, hf, hs⟩ := wrapMulOf_spec hm
  obtain ⟨-, -, hv⟩ := binop?_consistent hb c0
  have hv' : op0.denote ρ = Val.mul (x.denote ρ) (b.denote ρ) g.nuw g.nsw := (ok_inj hv).symm
  rw [binSrc_eval, Repl.eval_old, hv', specific_denote hs, apint_denote hc]
  rcases hop with rfl | rfl
  · simp only [beq_self_eq_true, ↓reduceIte] at hf
    rw [hf]
    exact Lemmas.udiv_exact_mul_nsw_refines _ hp _
  · simp only [show (BinOp.sdiv == BinOp.udiv) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hf
    rw [hf]
    exact Lemmas.sdiv_exact_mul_nuw_refines _ hp _

private theorem isDivRem_of_div {op : BinOp} (hop : op = .udiv ∨ op = .sdiv) : isDivRem op = true := by
  rcases hop with rfl | rfl <;> rfl

/-- Every step of `simplifyDiv` that fires is right, for `udiv` and `sdiv`, with or without `exact`. -/
theorem simplifyDiv.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ)
    (r : Recur) (hr : r.Sound ρ) (op : BinOp) (hop : op = .udiv ∨ op = .sdiv) (op0 op1 : Term w) (isExact : Bool)
    (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifyDiv.steps o d r op op0 op1 isExact n →
      Refines ((binSrc op { exact := isExact } op0 op1).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifyDiv.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifyDivRem.steps_sound ρ o ho d hd r hr op (isDivRem_of_div hop) _ op0 op1 n c0 c1 u0 u1 s res
      (forward_fire h.symm)
  · split at h
    · next c hc =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hk =>
      obtain ⟨-, rfl⟩ := h
      cases isExact
      · simp at hc
      · simp only [ite_true] at hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hk
        exact simplifyDiv.L1157 ρ o ho op hop op0 op1 hc hk.2
    · simp only [reduceCtorEq] at h
  · split at h
    · next c hc =>
      split at h
      · next hp =>
        split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
        next x hm =>
        obtain ⟨-, rfl⟩ := h
        cases isExact
        · simp at hc
        · simp only [ite_true] at hc
          exact simplifyDiv.L1168 ρ op hop op0 op1 x c0 hc hp hm
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-! ## `simplifyRem` -/

/-- `m_NSWShl(m_Specific(S), m_Value())` on `V` if `nsw`, else `m_NUWShl`. -/
def wrapShlOf (nsw : Bool) (s v : Term w) : Bool :=
  match binop? .shl v with
  | some (g, a, _) => (if nsw then g.nsw else g.nuw) && specific s a
  | none => false

/-- `m_NSWMul(m_Value(), m_CheckedInt(P))` on `V` if `nsw`, else `m_NUWMul`. -/
def wrapMulConst (nsw : Bool) (p : BitVec w → Bool) (v : Term w) : Bool :=
  match binop? .mul v with
  | some (g, _, b) => (if nsw then g.nsw else g.nuw) && cst p b
  | none => false

/-- `simplifyRem(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step. `Q.IIQ.UseInstrInfo` is true in InstSimplify's
queries. -/
def simplifyRem.steps (o : Oracle) (d : DomOracle) (r : Recur) (op : BinOp) (op0 op1 : Term w) (maxRecurse : Nat) :
    List (Step w) :=
  [ -- foldOrCommuteConstant: the constant folder folds two constants; a remainder isn't commutative.
    if op0.isConstant && op1.isConstant then .delegate "ConstantFoldBinaryOpOperands" else .next,
    forward (simplifyDivRem.steps o d r op op0 op1 maxRecurse),
    -- (X << Y) % X -> 0
    if (op == .srem && wrapShlOf true op1 op0) || (op == .urem && wrapShlOf false op1 op0) then
      .fire "IS.simplifyRem.L1189" (.const 0#w)
    else .next,
    -- (srem (mul nsw X, C1), C0) -> 0 if C1 s% C0 == 0
    -- (urem (mul nuw X, C1), C0) -> 0 if C1 u% C0 == 0
    match apint op1 with
    | some c0 =>
      if (if op == .srem then wrapMulConst true (fun c => c.srem c0 == 0#w) op0
          else wrapMulConst false (fun c => c % c0 == 0#w) op0) then
        .fire "IS.simplifyRem.L1204" (.const 0#w)
      else .next
    | none => .next ]

/-- `IS.simplifyRem.L1189`: `(X << Y) % X` to 0, for `shl nsw` and `srem`, or `shl nuw` and `urem`. -/
theorem simplifyRem.L1189 (ρ : Env) (op : BinOp) (f : Flags) (op0 op1 : Term w) (c0 : op0.Consistent ρ)
    (h : ((op == .srem && wrapShlOf true op1 op0) || (op == .urem && wrapShlOf false op1 op0)) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  have shl_of : ∀ nsw, wrapShlOf nsw op1 op0 = true → ∃ (g : Flags) (s : Term w),
      (if nsw then g.nsw else g.nuw) = true ∧
        op0.denote ρ = Val.shl (op1.denote ρ) (s.denote ρ) g.nuw g.nsw := by
    intro nsw hw
    unfold wrapShlOf at hw
    split at hw
    · next g a s hb =>
      obtain ⟨-, -, hv⟩ := binop?_consistent hb c0
      simp only [Bool.and_eq_true] at hw
      refine ⟨g, s, hw.1, ?_⟩
      rw [← specific_denote hw.2]
      exact (ok_inj hv).symm
    · cases hw
  rw [binSrc_eval, Repl.eval_const]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · obtain ⟨g, s, hg, hv⟩ := shl_of true hw
    simp only [↓reduceIte] at hg
    rw [hv, hg]
    exact Lemmas.srem_shl_nsw_refines _ _ _
  · obtain ⟨g, s, hg, hv⟩ := shl_of false hw
    simp only [Bool.false_eq_true, ↓reduceIte] at hg
    rw [hv, hg]
    exact Lemmas.urem_shl_nuw_refines _ _ _

/-- `IS.simplifyRem.L1204`: `srem (mul nsw X, C1), C0` and `urem (mul nuw X, C1), C0` to 0, where `C0` divides
`C1`. -/
theorem simplifyRem.L1204 (ρ : Env) (op : BinOp) (hop : op = .urem ∨ op = .srem) (f : Flags) (op0 op1 : Term w)
    {c0 : BitVec w} (cn : op0.Consistent ρ) (hc : apint op1 = some c0)
    (h : (if op == .srem then wrapMulConst true (fun c => c.srem c0 == 0#w) op0
      else wrapMulConst false (fun c => c % c0 == 0#w) op0) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  have mul_of : ∀ nsw p, wrapMulConst nsw p op0 = true → ∃ (g : Flags) (a : Term w) (c1 : BitVec w),
      (if nsw then g.nsw else g.nuw) = true ∧ p c1 = true ∧
        op0.denote ρ = Val.mul (a.denote ρ) (some c1) g.nuw g.nsw := by
    intro nsw p hw
    unfold wrapMulConst at hw
    split at hw
    · next g a b hb =>
      obtain ⟨-, -, hv⟩ := binop?_consistent hb cn
      simp only [Bool.and_eq_true] at hw
      obtain ⟨c1, hp, hd⟩ := cst_denote (ρ := ρ) hw.2
      refine ⟨g, a, c1, hw.1, hp, ?_⟩
      rw [← hd]
      exact (ok_inj hv).symm
    · cases hw
  rw [binSrc_eval, Repl.eval_const, apint_denote hc]
  rcases hop with rfl | rfl
  · simp only [show (BinOp.urem == BinOp.srem) = false from rfl, Bool.false_eq_true, ite_false] at h
    obtain ⟨g, a, c1, hg, hp, hv⟩ := mul_of false _ h
    simp only [Bool.false_eq_true, ↓reduceIte] at hg
    simp only [beq_iff_eq] at hp
    rw [hv, hg]
    exact Lemmas.urem_mul_nuw_of_umod_refines _ hp _
  · simp only [beq_self_eq_true, ite_true] at h
    obtain ⟨g, a, c1, hg, hp, hv⟩ := mul_of true _ h
    simp only [↓reduceIte] at hg
    simp only [beq_iff_eq] at hp
    rw [hv, hg]
    exact Lemmas.srem_mul_nsw_of_srem_refines _ hp _

private theorem isDivRem_of_rem {op : BinOp} (hop : op = .urem ∨ op = .srem) : isDivRem op = true := by
  rcases hop with rfl | rfl <;> rfl

/-- Every step of `simplifyRem` that fires is right, for `urem` and `srem`. -/
theorem simplifyRem.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ)
    (r : Recur) (hr : r.Sound ρ) (op : BinOp) (hop : op = .urem ∨ op = .srem) (f : Flags) (op0 op1 : Term w)
    (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifyRem.steps o d r op op0 op1 n →
      Refines ((binSrc op f op0 op1).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifyRem.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · exact simplifyDivRem.steps_sound ρ o ho d hd r hr op (isDivRem_of_rem hop) f op0 op1 n c0 c1 u0 u1 s res
      (forward_fire h.symm)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyRem.L1189 ρ op f op0 op1 c0 (by assumption)
  · split at h
    · next c hc =>
      by_cases hm : (if op == .srem then wrapMulConst true (fun c' => c'.srem c == 0#w) op0
          else wrapMulConst false (fun c' => c' % c == 0#w) op0) = true
      · rw [ite_eq_left hm] at h
        simp only [Step.fire.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact simplifyRem.L1204 ρ op hop f op0 op1 c0 hc hm
      · rw [ite_eq_right hm] at h
        cases h
    · simp only [reduceCtorEq] at h

/-! ## The entry folds -/

/-- `isKnownNegation(X, Y, /*NeedNSW=*/true)` from `llvm/lib/Analysis/ValueTracking.cpp`, as `simplifySDivInst` calls
it: `X` is `sub nsw 0, Y`, `Y` is `sub nsw 0, X`, or they're `sub nsw A, B` and `sub nsw B, A`. -/
def isKnownNegationNSW (x y : Term w) : Bool :=
  negationOf x y || negationOf y x || subSwapped x y
where
  /-- `match(X, m_Neg(m_Specific(Y)))`, and the `sub` has `nsw`. -/
  negationOf (x y : Term w) : Bool :=
    match binop? .sub x with
    | some (f, z, v) => zero z && specific y v && f.nsw
    | none => false
  /-- `match(X, m_NSWSub(m_Value(A), m_Value(B))) && match(Y, m_NSWSub(m_Specific(B), m_Specific(A)))`. -/
  subSwapped (x y : Term w) : Bool :=
    match binop? .sub x, binop? .sub y with
    | some (f, a, b), some (f', b', a') => f.nsw && f'.nsw && specific b b' && specific a a'
    | _, _ => false

/-- `simplifySDivInst(Op0, Op1, IsExact, Q, MaxRecurse)`, step by step. -/
def simplifySDivInst.steps (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : List (Step w) :=
  [ -- If two operands are negated and no signed overflow, return -1.
    if isKnownNegationNSW op0 op1 then .fire "IS.simplifySDivInst.L1216" (.const (BitVec.allOnes w)) else .next,
    forward (simplifyDiv.steps o d r .sdiv op0 op1 isExact maxRecurse) ]

def simplifySDivInst (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : Result w :=
  run (simplifySDivInst.steps o d r op0 op1 isExact maxRecurse)

/-- `simplifyUDivInst(Op0, Op1, IsExact, Q, MaxRecurse)`: `simplifyDiv` for `udiv`. -/
def simplifyUDivInst (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : Result w :=
  run (simplifyDiv.steps o d r .udiv op0 op1 isExact maxRecurse)

/-- `m_SExt(m_Value(X))` with `X->getType()->isIntOrIntVectorTy(1)`: a `sext` of an `i1`. -/
def sextOfBit : Term w → Bool
  | @Term.sext v _ _ _ => v == 1
  | _ => false

/-- `simplifySRemInst(Op0, Op1, Q, MaxRecurse)`, step by step. -/
def simplifySRemInst.steps (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (maxRecurse : Nat) :
    List (Step w) :=
  [ -- If the divisor is 0, the result is undefined, so assume the divisor is -1.
    -- srem Op0, (sext i1 X) --> srem Op0, -1 --> 0
    if sextOfBit op1 then .fire "IS.simplifySRemInst.L1246" (.const 0#w) else .next,
    -- If the two operands are negated, return 0.
    if isKnownNegation op0 op1 then .fire "IS.simplifySRemInst.L1250" (.const 0#w) else .next,
    forward (simplifyRem.steps o d r .srem op0 op1 maxRecurse) ]

def simplifySRemInst (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (maxRecurse : Nat) : Result w :=
  run (simplifySRemInst.steps o d r op0 op1 maxRecurse)

/-- `simplifyURemInst(Op0, Op1, Q, MaxRecurse)`: `simplifyRem` for `urem`. -/
def simplifyURemInst (o : Oracle) (d : DomOracle) (r : Recur) (op0 op1 : Term w) (maxRecurse : Nat) : Result w :=
  run (simplifyRem.steps o d r .urem op0 op1 maxRecurse)

/-- What InstSimplify does with an `sdiv`: `simplifyInstruction` calls `simplifySDivInst` with its `exact` flag and
`MaxRecurse` at `RecursionLimit`. The recursive calls and dominating conditions are what the model doesn't say. -/
def simplifySDivInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .sdiv f a b => simplifySDivInst o DomOracle.none Recur.unknown a b f.exact recursionLimit
  | _, _ => .null

/-- What InstSimplify does with a `udiv`. -/
def simplifyUDivInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .udiv f a b => simplifyUDivInst o DomOracle.none Recur.unknown a b f.exact recursionLimit
  | _, _ => .null

/-- What InstSimplify does with an `srem`. -/
def simplifySRemInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .srem _ a b => simplifySRemInst o DomOracle.none Recur.unknown a b recursionLimit
  | _, _ => .null

/-- What InstSimplify does with a `urem`. -/
def simplifyURemInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .urem _ a b => simplifyURemInst o DomOracle.none Recur.unknown a b recursionLimit
  | _, _ => .null

/-! ### The entry folds' own rewrites -/

/-- `IS.simplifySDivInst.L1216`: `X sdiv Y` to -1 where one is the other's `sub nsw 0, _`, or they're
`sub nsw A, B` and `sub nsw B, A`. -/
theorem simplifySDivInst.L1216 (ρ : Env) (op0 op1 : Term w) (isExact : Bool) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (h : isKnownNegationNSW op0 op1 = true) :
    Refines ((binSrc .sdiv { exact := isExact } op0 op1).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  rw [binSrc_eval, Repl.eval_const]
  show Refines (Val.sdiv _ _ isExact) _
  simp only [isKnownNegationNSW, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold isKnownNegationNSW.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hz, hv⟩, hn⟩ := h
      rw [sub_denote hs c0, cst_eq hz, specific_denote hv, hn]
      exact Lemmas.sdiv_neg_nsw_left_refines _ _ _
    · cases h
  · unfold isKnownNegationNSW.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hz, hv⟩, hn⟩ := h
      rw [sub_denote hs c1, cst_eq hz, specific_denote hv, hn]
      exact Lemmas.sdiv_neg_nsw_right_refines _ _ _
    · cases h
  · unfold isKnownNegationNSW.subSwapped at h
    split at h
    · next f a b f' b' a' hs hs' =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hn, hn'⟩, hb⟩, ha⟩ := h
      rw [sub_denote hs c0, sub_denote hs' c1, specific_denote hb, specific_denote ha, hn, hn']
      exact Lemmas.sdiv_sub_nsw_swap_refines _ _ _ _ _
    · cases h

/-- `IS.simplifySRemInst.L1246`: `srem X, (sext i1 B)` to 0: the divisor is -1, or 0, which is undefined. -/
theorem simplifySRemInst.L1246 (ρ : Env) (op0 op1 : Term w) (c1 : op1.Consistent ρ) (h : sextOfBit op1 = true) :
    Refines ((binSrc .srem {} op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, Repl.eval_const]
  show Refines (Val.srem _ _) _
  cases op1 with
  | sext id a =>
    simp only [sextOfBit, beq_iff_eq] at h
    subst h
    obtain ⟨-, hv⟩ := c1
    simp only [Term.denote]
    rw [← hv]
    exact Lemmas.srem_sext_one_bit_refines _ _
  | _ => simp [sextOfBit] at h

/-- `IS.simplifySRemInst.L1250`: `X srem Y` to 0 where one is the other's `sub 0, _`, or they're `A - B` and `B - A`,
whatever their flags. -/
theorem simplifySRemInst.L1250 (ρ : Env) (op0 op1 : Term w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h : isKnownNegation op0 op1 = true) :
    Refines ((binSrc .srem {} op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, Repl.eval_const]
  show Refines (Val.srem _ _) _
  simp only [isKnownNegation, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold isKnownNegation.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c0, cst_eq h.1, specific_denote h.2]
      exact Lemmas.srem_neg_left_refines _ _ _
    · cases h
  · unfold isKnownNegation.negationOf at h
    split at h
    · next f z v hs =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c1, cst_eq h.1, specific_denote h.2]
      exact Lemmas.srem_neg_right_refines _ _ _
    · cases h
  · unfold isKnownNegation.subSwapped at h
    split at h
    · next f a b f' b' a' hs hs' =>
      simp only [Bool.and_eq_true] at h
      rw [sub_denote hs c0, sub_denote hs' c1, specific_denote h.1, specific_denote h.2]
      exact Lemmas.srem_sub_swap_refines _ _ _ _ _ _
    · cases h

/-! ### The folds -/

/-- Theorem 1 for `simplifySDivInst`: every value the model returns refines the `sdiv` it replaces, at every width,
with or without `exact`, for every recursion budget, in every run its operands are consistent with, poison and
undefined behaviour included, for every oracle, dominating-condition oracle and recursive simplifier that's sound in
the run. It says nothing about operands that reach an `undef`. -/
theorem simplifySDivInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ) (r : Recur)
    (hr : r.Sound ρ) (op0 op1 : Term w) (isExact : Bool) (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {res : Repl w}
    (h : simplifySDivInst o d r op0 op1 isExact n = .value res) :
    Refines ((binSrc .sdiv { exact := isExact } op0 op1).eval ρ) (res.eval ρ) := by
  refine run_sound (P := fun res => Refines ((binSrc .sdiv { exact := isExact } op0 op1).eval ρ) (res.eval ρ))
    (fun s res hmem => ?_) h
  simp only [simplifySDivInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySDivInst.L1216 ρ op0 op1 isExact c0 c1 (by assumption)
  · exact simplifyDiv.steps_sound ρ o ho d hd r hr .sdiv (.inr rfl) op0 op1 isExact n c0 c1 u0 u1 s res
      (forward_fire h.symm)

/-- Theorem 1 for `simplifyUDivInst`, as for `simplifySDivInst`. -/
theorem simplifyUDivInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ) (r : Recur)
    (hr : r.Sound ρ) (op0 op1 : Term w) (isExact : Bool) (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {res : Repl w}
    (h : simplifyUDivInst o d r op0 op1 isExact n = .value res) :
    Refines ((binSrc .udiv { exact := isExact } op0 op1).eval ρ) (res.eval ρ) :=
  run_sound (simplifyDiv.steps_sound ρ o ho d hd r hr .udiv (.inl rfl) op0 op1 isExact n c0 c1 u0 u1) h

/-- Theorem 1 for `simplifySRemInst`, as for `simplifySDivInst`. -/
theorem simplifySRemInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ) (r : Recur)
    (hr : r.Sound ρ) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {res : Repl w}
    (h : simplifySRemInst o d r op0 op1 n = .value res) :
    Refines ((binSrc .srem {} op0 op1).eval ρ) (res.eval ρ) := by
  refine run_sound (P := fun res => Refines ((binSrc .srem {} op0 op1).eval ρ) (res.eval ρ))
    (fun s res hmem => ?_) h
  simp only [simplifySRemInst.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySRemInst.L1246 ρ op0 op1 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifySRemInst.L1250 ρ op0 op1 c0 c1 (by assumption)
  · exact simplifyRem.steps_sound ρ o ho d hd r hr .srem (.inr rfl) {} op0 op1 n c0 c1 u0 u1 s res
      (forward_fire h.symm)

/-- Theorem 1 for `simplifyURemInst`, as for `simplifySDivInst`. -/
theorem simplifyURemInst.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ) (r : Recur)
    (hr : r.Sound ρ) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) {res : Repl w}
    (h : simplifyURemInst o d r op0 op1 n = .value res) :
    Refines ((binSrc .urem {} op0 op1).eval ρ) (res.eval ρ) :=
  run_sound (simplifyRem.steps_sound ρ o ho d hd r hr .urem (.inl rfl) {} op0 op1 n c0 c1 u0 u1) h

end Peephole.IS
