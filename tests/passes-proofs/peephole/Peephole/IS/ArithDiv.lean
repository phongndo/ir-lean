import Peephole.IS.ArithRecur

/-! # InstSimplify's divisions and remainders, and their rewrites for every input

`isICmpTrue`, `isDivZero`, `simplifyDivRem`, `simplifyDiv`, `simplifyRem`, and the entry folds `simplifySDivInst`,
`simplifyUDivInst`, `simplifySRemInst` and `simplifyURemInst`, at `llvm/lib/Analysis/InstructionSimplify.cpp:970-1265`
at `llvmorg-23.1.3`, step by step in the C++'s order. A division is an `Outcome`: dividing by zero or poison, and the
signed division of the minimum by `-1`, are undefined, and an undefined source allows any replacement.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyDivRem.L1057` | `X / undef`, `X % undef`, and by poison, to poison |
| `IS.simplifyDivRem.L1063` | `X / 0` and `X % 0` to poison |
| `IS.simplifyDivRem.L1068` | `poison / X` and `poison % X` to poison |
| `IS.simplifyDivRem.L1073` | `undef / X` and `undef % X` to 0. IRLean has no `undef`, so this is about poison only |
| `IS.simplifyDivRem.L1078` | `0 / X` and `0 % X` to 0 |
| `IS.simplifyDivRem.L1083` | `X / X` to 1 and `X % X` to 0 |
| `IS.simplifyDivRem.L1092` | `X / Y` and `X % Y` to poison where `Y`'s known zeros are every bit |
| `IS.simplifyDivRem.L1100` | `X / Y` to `X` and `X % Y` to 0 where `Y`'s known zeros are every bit but the lowest |
| `IS.simplifyDivRem.L1114` | `X * Y / Y` to `X` and `X * Y % Y` to 0 where the product can't overflow |
| `IS.simplifyDivRem.L1119` | `X / Y` to 0 and `X % Y` to `X` where `isDivZero` holds |
| `IS.simplifyDiv.L1157` | `X /exact C` to poison where `X` has a known bit below `C`'s lowest |
| `IS.simplifyDiv.L1168` | `udiv exact (mul nsw X, C), C` and `sdiv exact (mul nuw X, C), C` to `X`, `C` not a power of 2 |
| `IS.simplifyRem.L1189` | `(X << Y) % X` to 0, for `shl nsw` and `srem`, or `shl nuw` and `urem` |
| `IS.simplifyRem.L1204` | `srem (mul nsw X, C1), C0` and `urem (mul nuw X, C1), C0` to 0 where `C0` divides `C1` |
| `IS.simplifySDivInst.L1216` | `X sdiv -X` to -1 where the negation has `nsw` |
| `IS.simplifySRemInst.L1246` | `srem X, (sext i1 B)` to 0 |
| `IS.simplifySRemInst.L1250` | `X srem -X` to 0 |

`isICmpTrue` asks `simplifyICmpInst`, which isn't modelled here: the model takes its answers from `Recur.icmp`, and
`isDivZero` answers `none` where the model doesn't say, so `simplifyDivRem` delegates there. -/

namespace Peephole.IS

open IRLean Peephole.IS.Arith

variable {w : Nat}

/-! ## `isICmpTrue` and `isDivZero` -/

/-- `A || B` on answers that may be unknown (`none`), where neither side does anything else. -/
def orK : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | some false, b => b
  | none, some true => some true
  | none, _ => none

/-- `A && B` on answers that may be unknown (`none`), where neither side does anything else. -/
def andK : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | some true, b => b
  | none, some false => some false
  | none, _ => none

theorem orK_true {a b : Option Bool} (h : orK a b = some true) : a = some true ∨ b = some true := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [orK]

theorem andK_true {a b : Option Bool} (h : andK a b = some true) : a = some true ∧ b = some true := by
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [andK]

/-- `isICmpTrue(Pred, LHS, RHS, Q, MaxRecurse)`: whether `simplifyICmpInst` answers the constant true. `none` where the
model doesn't say what it answers. -/
def isICmpTrue (r : Recur) (p : Pred) (lhs rhs : Term w) (maxRecurse : Nat) : Option Bool :=
  match r.icmp maxRecurse p lhs rhs with
  -- `C && C->isAllOnesValue()`, with `C = dyn_cast_or_null<Constant>(V)`.
  | .val t => some (allOnes t)
  | .null => some false
  | .unknown => none

/-- Where `isICmpTrue` says true, the comparison of two values holds. -/
theorem isICmpTrue_sound {ρ : Env} {r : Recur} (hr : r.Sound ρ) {p : Pred} {a b : Term w} {n : Nat}
    (h : isICmpTrue r p a b n = some true) (ca : a.Consistent ρ) (cb : b.Consistent ρ) (ua : a.hasUndef = false)
    (ub : b.hasUndef = false) {x y : BitVec w} (hx : a.denote ρ = some x) (hy : b.denote ρ = some y) :
    p.eval (some x) (some y) false = some (BitVec.allOnes 1) := by
  unfold isICmpTrue at h
  split at h
  · next t ht =>
    simp only [Option.some.injEq] at h
    have hrf := hr.icmp n p a b t ht ca cb ua ub
    rw [cst_eq h, hx, hy] at hrf
    have := (Refine.val_iff _ _).1 hrf
    cases p <;> simp_all [Pred.eval, Val.icmpEq, Val.icmpNe, Val.icmpUlt, Val.icmpUle, Val.icmpUgt, Val.icmpUge,
      Val.icmpSlt, Val.icmpSle, Val.icmpSgt, Val.icmpSge, Val.icmp]
  · cases h
  · cases h

private theorem icmp_holds {p : BitVec w → BitVec w → Bool} {x y : BitVec w}
    (h : Val.icmp p (some x) (some y) false = some (BitVec.allOnes 1)) : p x y = true := by
  simp only [Val.icmp, Bool.false_and, Bool.false_eq_true, ite_false, Option.some.injEq] at h
  revert h
  cases p x y <;> decide

/-- `m_SRem(m_Value(), m_Specific(S))` on `V`. -/
def sremBy (s v : Term w) : Bool :=
  match binop? .srem v with
  | some (_, _, b) => specific s b
  | none => false

/-- `isDivZero(X, Y, Q, MaxRecurse, IsSigned)`: whether `X / Y` is 0, so that `X % Y` is `X`. `none` where the model
doesn't say what `simplifyICmpInst` answers. -/
def isDivZero (o : Oracle) (r : Recur) (x y : Term w) (maxRecurse : Nat) (isSigned : Bool) : Option Bool :=
  -- Recursion is always used, so bail out at once if we already hit the limit.
  if maxRecurse == 0 then some false
  else if isSigned then
    -- (X srem Y) sdiv Y --> 0
    if sremBy y x then some true
    else
      orK
        -- |X| / |Y| --> 0, where the dividend is a constant other than the minimum: |Y| > |C|.
        (match apint x with
          | some c =>
            if c == BitVec.intMin w then some false
            else orK (isICmpTrue r .slt y (.const (-c.abs)) (maxRecurse - 1))
              (isICmpTrue r .sgt y (.const c.abs) (maxRecurse - 1))
          | none => some false)
        (match apint y with
          | some c =>
            -- Special-case: we can't take the abs() of a minimum signed value. If that's the divisor, then all we
            -- have to do is prove that the dividend is also not the minimum signed value.
            if c == BitVec.intMin w then isICmpTrue r .ne x y (maxRecurse - 1)
            -- |X| < |C| --> X > -abs(C) and X < abs(C)
            else andK (isICmpTrue r .sgt x (.const (-c.abs)) (maxRecurse - 1))
              (isICmpTrue r .slt x (.const c.abs) (maxRecurse - 1))
          | none => some false)
  else
    -- Is the unsigned dividend known to be less than a constant divisor?
    match apint y with
    | some c => if (~~~(o.knownZero x)).ult c then some true else isICmpTrue r .ult x y (maxRecurse - 1)
    -- Try again for any divisor: Is the dividend unsigned less than the divisor?
    | none => isICmpTrue r .ult x y (maxRecurse - 1)

/-- Where `isDivZero` says true, the dividend is smaller than the divisor: in magnitude if signed. -/
theorem isDivZero_sound {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {r : Recur} (hr : r.Sound ρ) {x y : Term w}
    {n : Nat} {isSigned : Bool} (h : isDivZero o r x y n isSigned = some true) (cx : x.Consistent ρ)
    (cy : y.Consistent ρ) (ux : x.hasUndef = false) (uy : y.hasUndef = false) {a b : BitVec w}
    (ha : x.denote ρ = some a) (hb : y.denote ρ = some b) :
    if isSigned then a.toInt.natAbs < b.toInt.natAbs else a < b := by
  unfold isDivZero at h
  split at h
  · cases h
  split at h
  · next hs =>
    simp only [hs, ite_true]
    split at h
    · next hsr =>
      unfold sremBy at hsr
      split at hsr
      · next f p b' hm =>
        obtain ⟨-, -, hv⟩ := binop?_consistent hm cx
        rw [ha, specific_denote hsr, hb] at hv
        have hv' : Val.srem (p.denote ρ) (some b) = Outcome.ok (some a) := hv
        obtain ⟨y', hy', hy0, hx'⟩ := srem_ok hv'
        cases hy'
        rcases hx' with h0 | ⟨p', -, -, hp⟩
        · cases h0
        · cases hp
          exact natAbs_srem_lt hy0
      · cases hsr
    · rcases orK_true h with h1 | h1
      · cases hcx : apint x with
        | none => simp only [hcx] at h1; cases h1
        | some c =>
          simp only [hcx] at h1
          have hxa := apint_denote (ρ := ρ) hcx
          rw [ha, Option.some.injEq] at hxa
          subst hxa
          by_cases hm : a = BitVec.intMin w
          · simp [hm] at h1
          · simp only [hm, beq_iff_eq, ite_false] at h1
            rcases orK_true h1 with h2 | h2
            · have := isICmpTrue_sound hr h2 cy trivial uy rfl hb rfl
              exact natAbs_lt_of_slt_neg_abs hm (icmp_holds this)
            · have := isICmpTrue_sound hr h2 cy trivial uy rfl hb rfl
              exact natAbs_lt_of_abs_slt hm (icmp_holds this)
      · cases hcy : apint y with
        | none => simp only [hcy] at h1; cases h1
        | some c =>
          simp only [hcy] at h1
          have hyb := apint_denote (ρ := ρ) hcy
          rw [hb, Option.some.injEq] at hyb
          subst hyb
          by_cases hm : b = BitVec.intMin w
          · simp only [hm, beq_self_eq_true, ite_true] at h1
            have := isICmpTrue_sound hr h1 cx cy ux uy ha hb
            have hne := icmp_holds this
            rw [hm]
            exact natAbs_lt_natAbs_intMin (by subst hm; simpa using hne)
          · simp only [hm, beq_iff_eq, ite_false] at h1
            obtain ⟨h2, h3⟩ := andK_true h1
            have e2 := icmp_holds (isICmpTrue_sound hr h2 cx trivial ux rfl ha rfl)
            have e3 := icmp_holds (isICmpTrue_sound hr h3 cx trivial ux rfl ha rfl)
            exact natAbs_lt_of_between hm e2 e3
  · next hs =>
    simp only [Bool.not_eq_true] at hs
    simp only [hs, Bool.false_eq_true, ite_false]
    split at h
    · next c hc =>
      have hyb := apint_denote (ρ := ρ) hc
      rw [hb, Option.some.injEq] at hyb
      subst hyb
      split at h
      · next hlt =>
        have hle := toNat_le_not_of_and_eq_zero (ho.knownZero x a ha)
        rw [BitVec.ult_eq_decide, decide_eq_true_eq] at hlt
        rw [BitVec.lt_def]
        omega
      · have := icmp_holds (isICmpTrue_sound hr h cx cy ux uy ha hb)
        exact BitVec.ult_iff_lt.1 this
    · have := icmp_holds (isICmpTrue_sound hr h cx cy ux uy ha hb)
      exact BitVec.ult_iff_lt.1 this

/-! ## `simplifyDivRem` -/

/-- The four opcodes `simplifyDivRem` is called with. -/
def isDivRem : BinOp → Bool
  | .udiv | .sdiv | .urem | .srem => true
  | _ => false

/-- `IsDiv`: `Opcode == Instruction::SDiv || Opcode == Instruction::UDiv`. -/
def isDivOp : BinOp → Bool
  | .sdiv | .udiv => true
  | _ => false

/-- `IsSigned`: `Opcode == Instruction::SDiv || Opcode == Instruction::SRem`. -/
def isSignedOp : BinOp → Bool
  | .sdiv | .srem => true
  | _ => false

/-- `m_c_Mul(m_Value(X), m_Specific(S))` on `V`, binding `X`, with the `mul`'s flags: operand 0 first. -/
def mulOf (s v : Term w) : Option (Flags × Term w) :=
  match binop? .mul v with
  | some (g, a, b) => if specific s b then some (g, a) else if specific s a then some (g, b) else none
  | none => none

/-- `m_SDiv(m_Value(), m_Specific(S))` on `V`, or `m_UDiv`: a division by `S`. -/
def divBy (op : BinOp) (s v : Term w) : Bool :=
  match binop? op v with
  | some (_, _, b) => specific s b
  | none => false

/-- `simplifyDivRem(Opcode, Op0, Op1, Q, MaxRecurse)`, step by step. -/
def simplifyDivRem.steps (o : Oracle) (d : DomOracle) (r : Recur) (op : BinOp) (op0 op1 : Term w)
    (maxRecurse : Nat) : List (Step w) :=
  [ -- X / undef -> poison
    -- X % undef -> poison
    if isUndefValue op1 || isPoison op1 then .fire "IS.simplifyDivRem.L1057" .poison else .next,
    -- X / 0 -> poison
    -- X % 0 -> poison
    -- We don't need to preserve faults!
    if zero op1 then .fire "IS.simplifyDivRem.L1063" .poison else .next,
    -- poison / X -> poison
    -- poison % X -> poison
    if isPoison op0 then .fire "IS.simplifyDivRem.L1068" (.old op0) else .next,
    -- undef / X -> 0
    -- undef % X -> 0
    if isUndefValue op0 then .fire "IS.simplifyDivRem.L1073" (.const 0#w) else .next,
    -- 0 / X -> 0
    -- 0 % X -> 0
    if zero op0 then .fire "IS.simplifyDivRem.L1078" (.const 0#w) else .next,
    -- X / X -> 1
    -- X % X -> 0
    if specific op0 op1 then .fire "IS.simplifyDivRem.L1083" (if isDivOp op then .const 1#w else .const 0#w)
    else .next,
    -- X / 0 -> poison
    -- X % 0 -> poison
    -- If the divisor is known to be zero, just return poison. `Known.isZero()` is `Known.Zero.isAllOnes()`.
    if o.knownZero op1 == BitVec.allOnes w then .fire "IS.simplifyDivRem.L1092" .poison else .next,
    -- X / 1 -> X
    -- X % 1 -> 0
    -- If the divisor can only be zero or one, we can't have division-by-zero or remainder-by-zero, so assume the
    -- divisor is 1. `Known.countMinLeadingZeros()` is the known zeros' leading ones.
    if (~~~(o.knownZero op1)).clz.toNat == w - 1 then
      .fire "IS.simplifyDivRem.L1100" (if isDivOp op then .old op0 else .const 0#w)
    else .next,
    -- If X * Y does not overflow, then:
    --   X * Y / Y -> X
    --   X * Y % Y -> 0
    -- The multiplication can't overflow if it is defined not to, or if X == A / Y for some A.
    match mulOf op1 op0 with
    | some (g, x) =>
      if (isSignedOp op && g.nsw) || (!isSignedOp op && g.nuw) || (isSignedOp op && divBy .sdiv op1 x) ||
          (!isSignedOp op && divBy .udiv op1 x) then
        .fire "IS.simplifyDivRem.L1114" (if isDivOp op then .old x else .const 0#w)
      else .next
    | none => .next,
    match isDivZero o r op0 op1 maxRecurse (isSignedOp op) with
    | some true => .fire "IS.simplifyDivRem.L1119" (if isDivOp op then .const 0#w else .old op0)
    | some false => .next
    | none => .delegate "simplifyICmpInst",
    forward (simplifyByDomEq.steps d op op0 op1 maxRecurse),
    -- If the operation is with the result of a select instruction, check whether operating on either branch of the
    -- select always yields the same value.
    if isSelect op0 || isSelect op1 then forward (threadBinOpOverSelect.steps r op op0 op1 maxRecurse) else .next,
    -- If the operation is with the result of a phi instruction, check whether operating on all incoming values of
    -- the phi always yields the same value: threadBinOpOverPHI isn't modelled, and a phi is an operand the model
    -- doesn't see into.
    if (mayBePhi op0 || mayBePhi op1) && maxRecurse != 0 then .delegate "threadBinOpOverPHI" else .next ]

/-! ### Per-opcode facts -/

private theorem eval_zero_right {op : BinOp} (hop : isDivRem op = true) (f : Flags) (a r : Val w) :
    Refines (op.eval f a (some 0#w)) (Outcome.ok r) := by
  cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop
  · exact udiv_zero_right a f.exact r
  · exact sdiv_zero_right a f.exact r
  · exact urem_zero_right a r
  · exact srem_zero_right a r

private theorem ite_eval_old_const (ρ : Env) (b : Bool) (t : Term w) (c : BitVec w) :
    (if b then Repl.old t else Repl.const c).eval ρ = Outcome.ok (if b then t.denote ρ else some c) := by
  cases b <;> rfl

private theorem ite_eval_const_old (ρ : Env) (b : Bool) (t : Term w) (c : BitVec w) :
    (if b then Repl.const c else Repl.old t).eval ρ = Outcome.ok (if b then some c else t.denote ρ) := by
  cases b <;> rfl

private theorem ite_eval_const_const (ρ : Env) (b : Bool) (c c' : BitVec w) :
    (if b then Repl.const c else Repl.const c').eval ρ = Outcome.ok (if b then some c else some c') := by
  cases b <;> rfl

/-! ### The rewrites -/

/-- `IS.simplifyDivRem.L1057`: `X / undef`, `X % undef`, and by poison, to poison: dividing by poison is undefined. -/
theorem simplifyDivRem.L1057 (ρ : Env) (op : BinOp) (f : Flags) (op0 op1 : Term w) (u1 : op1.hasUndef = false)
    (h : (isUndefValue op1 || isPoison op1) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  have : op1.denote ρ = none := by
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact isUndefValue_denote h u1
    · exact isPoison_denote h
  rw [binSrc_eval, this]
  exact eval_none_right _ _ _ _

/-- `IS.simplifyDivRem.L1063`: `X / 0` and `X % 0` to poison: dividing by zero is undefined. -/
theorem simplifyDivRem.L1063 (ρ : Env) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w)
    (h : zero op1 = true) : Refines ((binSrc op f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [binSrc_eval, cst_eq h]
  exact eval_zero_right hop _ _ _

/-- `IS.simplifyDivRem.L1068`: `poison / X` and `poison % X` to poison. -/
theorem simplifyDivRem.L1068 (ρ : Env) (op : BinOp) (f : Flags) (op0 op1 : Term w) (h : isPoison op0 = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [binSrc_eval, Repl.eval_old, isPoison_denote h]
  exact eval_none_left _ _ _ _

/-- `IS.simplifyDivRem.L1073`: `undef / X` and `undef % X` to 0, which without `undef` is poison to 0. -/
theorem simplifyDivRem.L1073 (ρ : Env) (op : BinOp) (f : Flags) (op0 op1 : Term w) (u0 : op0.hasUndef = false)
    (h : isUndefValue op0 = true) : Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, isUndefValue_denote h u0]
  exact eval_none_left _ _ _ _

/-- `IS.simplifyDivRem.L1078`: `0 / X` and `0 % X` to 0. -/
theorem simplifyDivRem.L1078 (ρ : Env) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w)
    (h : zero op0 = true) : Refines ((binSrc op f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, cst_eq h, Repl.eval_const]
  cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop
  · exact Lemmas.udiv_zero_left_refines _ _
  · exact Lemmas.sdiv_zero_left_refines _ _
  · exact Lemmas.urem_zero_left_refines _
  · exact Lemmas.srem_zero_left_refines _

/-- `IS.simplifyDivRem.L1083`: `X / X` to 1 and `X % X` to 0. -/
theorem simplifyDivRem.L1083 (ρ : Env) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w)
    (h : specific op0 op1 = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((if isDivOp op then Repl.const 1#w else Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, specific_denote h, ite_eval_const_const]
  cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop <;> simp only [isDivOp, ite_true, ite_false,
    Bool.false_eq_true]
  · exact Lemmas.udiv_self_refines _ _
  · exact Lemmas.sdiv_self_refines _ _
  · exact Lemmas.urem_self_refines _
  · exact Lemmas.srem_self_refines _

/-- `IS.simplifyDivRem.L1092`: `X / Y` and `X % Y` to poison where `computeKnownBits(Y).Zero` is every bit: `Y` is 0,
and dividing by it is undefined. -/
theorem simplifyDivRem.L1092 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op : BinOp) (hop : isDivRem op = true)
    (f : Flags) (op0 op1 : Term w) (hk : o.knownZero op1 = BitVec.allOnes w) :
    Refines ((binSrc op f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [binSrc_eval]
  cases h1 : op1.denote ρ with
  | none => exact eval_none_right _ _ _ _
  | some y =>
    have := ho.knownZero op1 y h1
    rw [hk] at this
    rw [eq_zero_of_and_allOnes this]
    exact eval_zero_right hop _ _ _

/-- `IS.simplifyDivRem.L1100`: `X / Y` to `X` and `X % Y` to 0 where `computeKnownBits(Y)` leaves only the lowest bit
unknown: `Y` is 1, or 0, which is undefined. -/
theorem simplifyDivRem.L1100 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op : BinOp) (hop : isDivRem op = true)
    (f : Flags) (op0 op1 : Term w) (hk : (~~~(o.knownZero op1)).clz.toNat = w - 1) :
    Refines ((binSrc op f op0 op1).eval ρ) ((if isDivOp op then Repl.old op0 else Repl.const 0#w).eval ρ) := by
  rw [binSrc_eval, ite_eval_old_const]
  cases h1 : op1.denote ρ with
  | none => exact eval_none_right _ _ _ _
  | some y =>
    rcases le_one_of_clz_not (ho.knownZero op1 y h1) hk with rfl | rfl
    · exact eval_zero_right hop _ _ _
    · by_cases hy : (1#w) = 0#w
      · rw [hy]; exact eval_zero_right hop _ _ _
      have hw := pos_of_ne_zero hy
      cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop <;> simp only [isDivOp, ite_true, ite_false,
        Bool.false_eq_true]
      · rw [show BinOp.eval .udiv f (op0.denote ρ) (some 1#w) = Val.udiv (op0.denote ρ) (some 1#w) f.exact from rfl,
          Generic.udiv_one _ _ hw]
        exact ok_refl _
      · exact Generic.sdiv_one_refines _ _
      · exact Generic.urem_one_refines _
      · exact Generic.srem_one_refines _

/-- What `mulOf` matched: the dividend is the product of `X` and the divisor, in one order or the other. -/
private theorem mulOf_denote {ρ : Env} {s v x : Term w} {g : Flags} (h : mulOf s v = some (g, x))
    (hc : v.Consistent ρ) :
    v.denote ρ = Val.mul (x.denote ρ) (s.denote ρ) g.nuw g.nsw ∧ x.Consistent ρ := by
  unfold mulOf at h
  split at h
  · next g' a b hb =>
    obtain ⟨ca, cb, hv⟩ := binop?_consistent hb hc
    have hv' : v.denote ρ = Val.mul (a.denote ρ) (b.denote ρ) g'.nuw g'.nsw := (ok_inj hv).symm
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [hv', specific_denote hs], ca⟩
    · split at h
      · next hs =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by rw [hv', specific_denote hs, Lemmas.mul_comm], cb⟩
      · cases h
  · cases h

/-- What `divBy` matched: `X` is a division by the divisor that ran. -/
private theorem divBy_eval {ρ : Env} {op : BinOp} {s x : Term w} (h : divBy op s x = true) (hc : x.Consistent ρ) :
    ∃ (a : Term w) (f : Flags), op.eval f (a.denote ρ) (s.denote ρ) = Outcome.ok (x.denote ρ) := by
  unfold divBy at h
  split at h
  · next f a b hb =>
    obtain ⟨-, -, hv⟩ := binop?_consistent hb hc
    exact ⟨a, f, by rw [← specific_denote h]; exact hv⟩
  · cases h

/-- `IS.simplifyDivRem.L1114`: `X * Y / Y` to `X` and `X * Y % Y` to 0, where the product can't overflow: it has the
flag the division's signedness needs, or `X` is a division by `Y`. -/
theorem simplifyDivRem.L1114 (ρ : Env) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w)
    {g : Flags} {x : Term w} (c0 : op0.Consistent ρ) (hm : mulOf op1 op0 = some (g, x))
    (hc : ((isSignedOp op && g.nsw) || (!isSignedOp op && g.nuw) || (isSignedOp op && divBy .sdiv op1 x) ||
      (!isSignedOp op && divBy .udiv op1 x)) = true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((if isDivOp op then Repl.old x else Repl.const 0#w).eval ρ) := by
  obtain ⟨hv, cx⟩ := mulOf_denote hm c0
  rw [binSrc_eval, hv, ite_eval_old_const]
  cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop <;> simp only [isDivOp, isSignedOp, ite_true,
    ite_false, Bool.false_eq_true, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false, Bool.or_false,
    Bool.false_or, Bool.or_eq_true] at hc ⊢
  · -- udiv
    rcases hc with hn | hd
    · rw [hn]; exact Lemmas.udiv_mul_nuw_refines _ _ _ _
    · obtain ⟨a, e, he⟩ := divBy_eval hd cx
      exact Lemmas.udiv_mul_udiv_refines he _ _ _
  · -- sdiv
    rcases hc with hn | hd
    · rw [hn]; exact Lemmas.sdiv_mul_nsw_refines _ _ _ _
    · obtain ⟨a, e, he⟩ := divBy_eval hd cx
      exact Lemmas.sdiv_mul_sdiv_refines he _ _ _
  · -- urem
    rcases hc with hn | hd
    · rw [hn]; exact Lemmas.urem_mul_nuw_refines _ _ _
    · obtain ⟨a, e, he⟩ := divBy_eval hd cx
      exact Lemmas.urem_mul_udiv_refines he _ _
  · -- srem
    rcases hc with hn | hd
    · rw [hn]; exact Lemmas.srem_mul_nsw_refines _ _ _
    · obtain ⟨a, e, he⟩ := divBy_eval hd cx
      exact Lemmas.srem_mul_sdiv_refines he _ _

/-- `IS.simplifyDivRem.L1119`: `X / Y` to 0 and `X % Y` to `X`, where `isDivZero` holds. -/
theorem simplifyDivRem.L1119 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (r : Recur) (hr : r.Sound ρ) (op : BinOp)
    (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w) (n : Nat) (c0 : op0.Consistent ρ)
    (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    (h : isDivZero o r op0 op1 n (isSignedOp op) = some true) :
    Refines ((binSrc op f op0 op1).eval ρ) ((if isDivOp op then Repl.const 0#w else Repl.old op0).eval ρ) := by
  rw [binSrc_eval, ite_eval_const_old]
  cases h0 : op0.denote ρ with
  | none => exact eval_none_left _ _ _ _
  | some a =>
  cases h1 : op1.denote ρ with
  | none => exact eval_none_right _ _ _ _
  | some b =>
  have hs := isDivZero_sound ho hr h c0 c1 u0 u1 h0 h1
  cases op <;> simp only [isDivRem, Bool.false_eq_true] at hop <;> simp only [isDivOp, isSignedOp, ite_true,
    ite_false, Bool.false_eq_true] at hs ⊢
  · exact Lemmas.udiv_of_lt_refines hs _
  · exact Lemmas.sdiv_of_natAbs_lt_refines hs _
  · exact Lemmas.urem_of_lt_refines hs
  · exact Lemmas.srem_of_natAbs_lt_refines hs

/-- Every step of `simplifyDivRem` that fires is right, for the four opcodes it's called with, with any flags. -/
theorem simplifyDivRem.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ)
    (r : Recur) (hr : r.Sound ρ) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false) :
    ∀ s res, Step.fire s res ∈ simplifyDivRem.steps o d r op op0 op1 n →
      Refines ((binSrc op f op0 op1).eval ρ) (res.eval ρ) := by
  intro s res hmem
  simp only [simplifyDivRem.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1057 ρ op f op0 op1 u1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1063 ρ op hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1068 ρ op f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1073 ρ op f op0 op1 u0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1078 ρ op hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1083 ρ op hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hk =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1092 ρ o ho op hop f op0 op1 (by simpa using hk)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hk =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1100 ρ o ho op hop f op0 op1 (by simpa using hk)
  · split at h
    · next g x hm =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      exact simplifyDivRem.L1114 ρ op hop f op0 op1 c0 hm hc
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hz =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyDivRem.L1119 ρ o ho r hr op hop f op0 op1 n c0 c1 u0 u1 hz
  · exact simplifyByDomEq.steps_sound ρ d hd op f op0 op1 n s res (forward_fire h.symm)
  · split at h
    · exact threadBinOpOverSelect.steps_sound ρ r hr op f op0 op1 n c0 c1 u0 u1 s res (forward_fire h.symm)
    · simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h

/-- `simplifyDivRem`: every value it returns refines its caller's division or remainder, with any flags. -/
theorem simplifyDivRem.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (d : DomOracle) (hd : d.Sound ρ)
    (r : Recur) (hr : r.Sound ρ) (op : BinOp) (hop : isDivRem op = true) (f : Flags) (op0 op1 : Term w) (n : Nat)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    {res : Repl w} (h : run (simplifyDivRem.steps o d r op op0 op1 n) = .value res) :
    Refines ((binSrc op f op0 op1).eval ρ) (res.eval ρ) :=
  run_sound (simplifyDivRem.steps_sound ρ o ho d hd r hr op hop f op0 op1 n c0 c1 u0 u1) h

end Peephole.IS
