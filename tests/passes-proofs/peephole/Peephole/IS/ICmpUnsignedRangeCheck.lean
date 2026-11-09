import Peephole.IS.ICmpOfBools

/-! # InstSimplify's `simplifyUnsignedRangeCheck`, and its rewrites for every input

`simplifyUnsignedRangeCheck` is at `llvm/lib/Analysis/InstructionSimplify.cpp:1512-1616` at `llvmorg-23.1.3`.
`simplifyAndOfICmps` and `simplifyOrOfICmps` call it on the two compares of an `and` or `or`, each way round: a
compare of `Y` against 0 for equality, `ZeroICmp`, and an unsigned compare, `UnsignedICmp`, that together say one
thing.

| ID | Rewrite (`Y == 0` is `ZeroICmp`; `&&` is `and`, `||` is `or`) |
| --- | --- |
| `IS.simplifyUnsignedRangeCheck.L1534` | `A >=/<= B || (A - B) != 0` to true |
| `IS.simplifyUnsignedRangeCheck.L1539` | `A </> B && (A - B) == 0` to false |
| `IS.simplifyUnsignedRangeCheck.L1545` | `A </> B && (A - B) != 0` to `A </> B`; with `||`, to `(A - B) != 0` |
| `IS.simplifyUnsignedRangeCheck.L1551` | `A <=/>= B && (A - B) == 0` to `(A - B) == 0`; with `||`, to `A <=/>= B` |
| `IS.simplifyUnsignedRangeCheck.L1561` | `Y >= A && Y != 0` to `Y >= A`, where `Y = A - B` and `B` is known non-zero |
| `IS.simplifyUnsignedRangeCheck.L1564` | `Y < A || Y == 0` to `Y < A`, where `Y = A - B` and `B` is known non-zero |
| `IS.simplifyUnsignedRangeCheck.L1582` | `X > Y && Y == 0` to `Y == 0`; with `||`, to `X > Y`; `X` known non-zero |
| `IS.simplifyUnsignedRangeCheck.L1588` | `X <= Y && Y != 0` to `X <= Y`; with `||`, to `Y != 0`; `X` known non-zero |
| `IS.simplifyUnsignedRangeCheck.L1598` | `X < Y && Y != 0` to `X < Y`; with `||`, to `Y != 0` |
| `IS.simplifyUnsignedRangeCheck.L1603` | `X >= Y && Y == 0` to `Y == 0`; with `||`, to `X >= Y` |
| `IS.simplifyUnsignedRangeCheck.L1608` | `X < Y && Y == 0` to false |
| `IS.simplifyUnsignedRangeCheck.L1613` | `X >= Y || Y != 0` to true |

Comparisons are unsigned throughout. The source is the `and` or `or` of the two compares, `ICmp.andOrSrc`, with any
flags: a `disjoint` `or` is poison in more runs. `simplifyUnsignedRangeCheck.sound` says the answer refines it with
`ZeroICmp` first; `sound_swap`, with it second, as `simplifyAndOfICmps(Op0, Op1)`'s second call has it. -/

namespace Peephole.IS

open IRLean ICmp

variable {v : Nat}

/-! ### Helpers -/

namespace ICmp

/-- `m_c_ICmp(Pred, m_Specific(A), m_Specific(B))` on `icmp Pred P, Q`: the predicate, swapped if the operands are,
as a comparison of `A` with `B`. -/
def cICmp (up : Pred) (p q a b : Term v) : Option Pred :=
  if specific a p && specific b q then some up
  else if specific a q && specific b p then some (swap up)
  else none

/-- `m_ICmp(UnsignedPred, m_Value(X), m_Specific(Y))` with `UnsignedPred` unsigned, or else
`m_ICmp(UnsignedPred, m_Specific(Y), m_Value(X))` with it unsigned, and then swapped: `X`, and the predicate as a
comparison of `X` with `Y`. -/
def xyForm (up : Pred) (p q y : Term v) : Option (Term v × Pred) :=
  if specific y q && isUnsigned up then some (p, up)
  else if specific y p && isUnsigned up then some (q, swap up)
  else none

/-- `match(Y, m_Sub(m_Value(A), m_Value(B)))`: `A` and `B`. -/
def subOps (y : Term v) : Option (Term v × Term v) :=
  match binop? .sub y with
  | some (_, a, b) => some (a, b)
  | none => none

/-- Where `Y = A - B`: `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(A), m_Specific(B)))`. -/
def predAB (up : Pred) (p q y : Term v) : Option Pred :=
  match subOps y with
  | some (a, b) => cICmp up p q a b
  | none => none

/-- Where `Y = A - B`: `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(Y), m_Specific(A)))`. -/
def predYA (up : Pred) (p q y : Term v) : Option Pred :=
  match subOps y with
  | some (a, _) => cICmp up p q y a
  | none => none

/-- Where `Y = A - B`: `isKnownNonZero(B, Q)`. -/
def nonZeroB (o : Oracle) (y : Term v) : Bool :=
  match subOps y with
  | some (_, b) => o.nonZero b
  | none => false

theorem eq_of_sub_eq_zero {a b : BitVec v} (h : a - b = 0#v) : a = b := by
  rw [← BitVec.sub_add_cancel a b, h, BitVec.zero_add]

/-- The `and`, if `isAnd`, else the `or`, of two compares: what `simplifyAndOfICmps` and `simplifyOrOfICmps`
simplify. -/
def andOrSrc (isAnd : Bool) (f : Flags) (a b : Term 1) : Repl 1 :=
  .bin (if isAnd then .and else .or) f (.old a) (.old b)

theorem bv1_ofBool (x : BitVec 1) : ∃ b, x = BitVec.ofBool b := by
  rcases bv1_cases x with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-- An `and` or `or` of two `i1`s refines `t` if `t` is what it computes whenever neither is poison. -/
theorem andOrSrc_refines {ρ : Env} {isAnd : Bool} {f : Flags} {a b : Term 1} {t : Val 1}
    (h : ∀ za ub, a.denote ρ = some (BitVec.ofBool za) → b.denote ρ = some (BitVec.ofBool ub) →
      t = some (BitVec.ofBool (if isAnd then za && ub else za || ub))) :
    Refines ((andOrSrc isAnd f a b).eval ρ) (Outcome.ok t) := by
  have : (andOrSrc isAnd f a b).eval ρ =
      (if isAnd then BinOp.and else BinOp.or).eval f (a.denote ρ) (b.denote ρ) := rfl
  rw [this]
  cases ha : a.denote ρ with
  | none => cases isAnd <;> exact refines_ok (Refine.val_none _)
  | some x =>
  cases hb : b.denote ρ with
  | none => cases isAnd <;> cases x <;> exact refines_ok (Refine.val_none _)
  | some y =>
  obtain ⟨za, rfl⟩ := bv1_ofBool x
  obtain ⟨ub, rfl⟩ := bv1_ofBool y
  rw [h za ub ha hb]
  cases isAnd
  · simp only [BinOp.eval, Bool.false_eq_true, ↓reduceIte, Val.or, BitVec.ofBool_or_ofBool]
    split
    · exact refines_ok (Refine.val_none _)
    · exact refines_ok (Refine.refl_val _)
  · simp only [BinOp.eval, ↓reduceIte, Val.and, Val.map₂, BitVec.ofBool_and_ofBool]
    exact refines_ok (Refine.refl_val _)

theorem eval_ofBool {p : Pred} {a b : Val v} {s zb : Bool} (h : p.eval a b s = some (BitVec.ofBool zb)) :
    ∃ x y, a = some x ∧ b = some y ∧ zb = test p x y := by
  cases a with
  | none => rw [eval_none_left] at h; cases h
  | some x =>
  cases b with
  | none => rw [eval_none_right] at h; cases h
  | some y =>
  rw [eval_some] at h
  split at h
  · cases h
  · exact ⟨x, y, rfl, rfl, BitVec.ofBool_eq_iff_eq.1 (Option.some.inj h).symm⟩

theorem cICmp_test {ρ : Env} {up up' : Pred} {p q a b : Term v} (h : cICmp up p q a b = some up')
    {pv qv : BitVec v} (hp : p.denote ρ = some pv) (hq : q.denote ρ = some qv) :
    ∃ av bv, a.denote ρ = some av ∧ b.denote ρ = some bv ∧ test up pv qv = test up' av bv := by
  unfold cICmp at h
  split at h
  · next hs =>
    cases h
    simp only [Bool.and_eq_true] at hs
    rw [specific_denote hs.1] at hp
    rw [specific_denote hs.2] at hq
    exact ⟨pv, qv, hp, hq, rfl⟩
  · split at h
    · next hs =>
      cases h
      simp only [Bool.and_eq_true] at hs
      rw [specific_denote hs.2] at hp
      rw [specific_denote hs.1] at hq
      exact ⟨qv, pv, hq, hp, (test_swap up pv qv).symm⟩
    · cases h

theorem xyForm_test {ρ : Env} {up up' : Pred} {p q y x : Term v} (h : xyForm up p q y = some (x, up'))
    {pv qv : BitVec v} (hp : p.denote ρ = some pv) (hq : q.denote ρ = some qv) :
    ∃ xv yv, x.denote ρ = some xv ∧ y.denote ρ = some yv ∧ test up pv qv = test up' xv yv := by
  unfold xyForm at h
  split at h
  · next hs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hs
    rw [specific_denote hs.1] at hq
    exact ⟨pv, qv, hp, hq, rfl⟩
  · split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hs
      rw [specific_denote hs.1] at hp
      exact ⟨qv, pv, hq, hp, (test_swap up pv qv).symm⟩
    · cases h

/-- What `ZeroICmp`'s and `UnsignedICmp`'s values are, as a site's theorem takes them: `Y == 0` or `Y != 0`, and
`UnsignedPred` on `P` and `Q`. -/
structure RangeCheck (ρ : Env) (zc uc : Term 1) (eqp : Pred) (y : Term v) (up : Pred) (p q : Term v) : Prop where
  zero : ∀ zb, zc.denote ρ = some (BitVec.ofBool zb) → ∃ yv, y.denote ρ = some yv ∧ zb = test eqp yv 0#v
  unsigned : ∀ ub, uc.denote ρ = some (BitVec.ofBool ub) →
    ∃ pv qv, p.denote ρ = some pv ∧ q.denote ρ = some qv ∧ ub = test up pv qv
  /-- `Y`'s value is its operation's on its operands', as `Y.Consistent` says. -/
  y : y.Consistent ρ

/-- `Y = A - B`: `Y`'s value is `A - B`'s, where it isn't poison. -/
theorem sub_value {ρ : Env} {y a b : Term v} {f : Flags} (hs : binop? .sub y = some (f, a, b)) (hc : y.Consistent ρ)
    {yv : BitVec v} (hy : y.denote ρ = some yv) : ∃ av bv, a.denote ρ = some av ∧ b.denote ρ = some bv ∧
      yv = av - bv := by
  have hd := (ok_inj (binop?_consistent hs hc).2.2)
  rw [hy] at hd
  revert hd
  cases a.denote ρ <;> cases b.denote ρ <;> simp only [Val.sub, reduceCtorEq, false_implies]
  next av bv =>
  split
  · simp
  · intro hd
    exact ⟨av, bv, rfl, rfl, (Option.some.inj hd).symm⟩

theorem toNat_ne_zero {x : BitVec v} : x ≠ 0#v ↔ x.toNat ≠ 0 := by
  rw [Ne, BitVec.toNat_eq]; simp

end ICmp

/-! ### The model -/

/-- `simplifyUnsignedRangeCheck`, from where `ZeroICmp` has matched `icmp EqPred Y, 0` with `EqPred` an equality,
and `UnsignedICmp` is `icmp UnsignedPred P, Q` with `P` and `Q` at `Y`'s width. A step for each `return`. -/
def simplifyUnsignedRangeCheck.inner (o : Oracle) (zc uc : Term 1) (eqp : Pred) (y : Term v) (up : Pred)
    (p q : Term v) (isAnd : Bool) : List (Step 1) :=
  -- Y = (A - B); the two m_c_ICmp matches on UnsignedICmp; isKnownNonZero(B, Q); and the X/Y forms.
  let pAB := predAB up p q y
  let pYA := predYA up p q y
  let xy := xyForm up p q y
  [ -- A >=/<= B || (A - B) != 0  <-->  true
    match pAB with
    | some u =>
      if isUnsigned u && (u == .uge || u == .ule) && eqp == .ne && !isAnd then
        .fire "IS.simplifyUnsignedRangeCheck.L1534" getTrue
      else .next
    | none => .next,
    -- A </> B && (A - B) == 0  <-->  false
    match pAB with
    | some u =>
      if isUnsigned u && (u == .ult || u == .ugt) && eqp == .eq && isAnd then
        .fire "IS.simplifyUnsignedRangeCheck.L1539" getFalse
      else .next
    | none => .next,
    -- A </> B && (A - B) != 0  <-->  A </> B;  A </> B || (A - B) != 0  <-->  (A - B) != 0
    match pAB with
    | some u =>
      if isUnsigned u && eqp == .ne && (u == .ult || u == .ugt) then
        .fire "IS.simplifyUnsignedRangeCheck.L1545" (.old (if isAnd then uc else zc))
      else .next
    | none => .next,
    -- A <=/>= B && (A - B) == 0  <-->  (A - B) == 0;  A <=/>= B || (A - B) == 0  <-->  A <=/>= B
    match pAB with
    | some u =>
      if isUnsigned u && eqp == .eq && (u == .ule || u == .uge) then
        .fire "IS.simplifyUnsignedRangeCheck.L1551" (.old (if isAnd then zc else uc))
      else .next
    | none => .next,
    -- Given Y = (A - B): Y >= A && Y != 0  --> Y >= A  iff B != 0
    match pYA with
    | some u =>
      if u == .uge && isAnd && eqp == .ne && nonZeroB o y then .fire "IS.simplifyUnsignedRangeCheck.L1561" (.old uc)
      else .next
    | none => .next,
    --   Y <  A || Y == 0  --> Y <  A  iff B != 0
    match pYA with
    | some u =>
      if u == .ult && !isAnd && eqp == .eq && nonZeroB o y then .fire "IS.simplifyUnsignedRangeCheck.L1564" (.old uc)
      else .next
    | none => .next,
    -- if (match(UnsignedICmp, m_ICmp(UnsignedPred, m_Value(X), m_Specific(Y))) && ...) ... else return nullptr;
    match xy with
    | some _ => .next
    | none => .decline,
    -- X > Y && Y == 0  -->  Y == 0  iff X != 0;  X > Y || Y == 0  -->  X > Y   iff X != 0
    match xy with
    | some (x, u) =>
      if u == .ugt && eqp == .eq && o.nonZero x then
        .fire "IS.simplifyUnsignedRangeCheck.L1582" (.old (if isAnd then zc else uc))
      else .next
    | none => .next,
    -- X <= Y && Y != 0  -->  X <= Y  iff X != 0;  X <= Y || Y != 0  -->  Y != 0  iff X != 0
    match xy with
    | some (x, u) =>
      if u == .ule && eqp == .ne && o.nonZero x then
        .fire "IS.simplifyUnsignedRangeCheck.L1588" (.old (if isAnd then uc else zc))
      else .next
    | none => .next,
    -- X < Y && Y != 0  -->  X < Y;  X < Y || Y != 0  -->  Y != 0
    match xy with
    | some (_, u) =>
      if u == .ult && eqp == .ne then .fire "IS.simplifyUnsignedRangeCheck.L1598" (.old (if isAnd then uc else zc))
      else .next
    | none => .next,
    -- X >= Y && Y == 0  -->  Y == 0;  X >= Y || Y == 0  -->  X >= Y
    match xy with
    | some (_, u) =>
      if u == .uge && eqp == .eq then .fire "IS.simplifyUnsignedRangeCheck.L1603" (.old (if isAnd then zc else uc))
      else .next
    | none => .next,
    -- X < Y && Y == 0  -->  false
    match xy with
    | some (_, u) =>
      if u == .ult && eqp == .eq && isAnd then .fire "IS.simplifyUnsignedRangeCheck.L1608" getFalse else .next
    | none => .next,
    -- X >= Y || Y != 0  -->  true
    match xy with
    | some (_, u) =>
      if u == .uge && eqp == .ne && !isAnd then .fire "IS.simplifyUnsignedRangeCheck.L1613" getTrue else .next
    | none => .next ]

/-- `simplifyUnsignedRangeCheck(ZeroICmp, UnsignedICmp, IsAnd, Q)`, step by step. Its first statement returns
`nullptr` unless `ZeroICmp` is `m_ICmp(EqPred, m_Value(Y), m_Zero())` with `EqPred` an equality. Every later
`return` needs `UnsignedICmp`'s operands to be `Y`, `A` or `B` by `m_Specific`, so where they're of another type the
function returns `nullptr`, as `[.decline]` does here. -/
def simplifyUnsignedRangeCheck.steps (o : Oracle) (zc uc : Term 1) (isAnd : Bool) : List (Step 1) :=
  match zc with
  | @Term.icmp v _ eqp _ y z =>
    if zero z && isEquality eqp then
      match uc with
      | @Term.icmp _ _ up _ p q =>
        match sameWidth (v := v) p, sameWidth (v := v) q with
        | some p', some q' => inner o zc uc eqp y up p' q' isAnd
        | _, _ => [.decline]
      | _ => [.decline]
    else [.decline]
  | _ => [.decline]

def simplifyUnsignedRangeCheck (o : Oracle) (zc uc : Term 1) (isAnd : Bool) : Result 1 :=
  run (simplifyUnsignedRangeCheck.steps o zc uc isAnd)

/-! ### The rewrites, one theorem each

Each takes `ZeroICmp`'s and `UnsignedICmp`'s values as a `RangeCheck` and the facts its step tests, for any flags on
the `and` or `or`. -/

section sites

variable (ρ : Env) (o : Oracle) (zc uc : Term 1) (eqp : Pred) (y : Term v) (up : Pred) (p q : Term v)
  (isAnd : Bool) (f : Flags) (hr : RangeCheck ρ zc uc eqp y up p q)
include hr

/-- `IS.simplifyUnsignedRangeCheck.L1534`: `A >=/<= B || (A - B) != 0` to true. -/
theorem simplifyUnsignedRangeCheck.L1534 {fs : Flags} {a b : Term v} {u : Pred}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q a b = some u) (hp : u = .uge ∨ u = .ule)
    (he : eqp = .ne) : Refines ((andOrSrc false f zc uc).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
  obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
  obtain ⟨av, bv, ha, hb, ht⟩ := cICmp_test hu hpv hqv
  obtain ⟨av', bv', ha', hb', rfl⟩ := sub_value hs hr.y hy
  rw [ha] at ha'; cases ha'
  rw [hb] at hb'; cases hb'
  subst he
  simp only [Bool.false_eq_true, ↓reduceIte, ht]
  by_cases h0 : av - bv = 0#v
  · have : av = bv := eq_of_sub_eq_zero h0
    subst this
    rcases hp with rfl | rfl <;> simp [test, BitVec.ule_eq_decide]
  · have : (av - bv != 0#v) = true := by simpa using h0
    simp [test, this]

/-- `IS.simplifyUnsignedRangeCheck.L1539`: `A </> B && (A - B) == 0` to false. -/
theorem simplifyUnsignedRangeCheck.L1539 {fs : Flags} {a b : Term v} {u : Pred}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q a b = some u) (hp : u = .ult ∨ u = .ugt)
    (he : eqp = .eq) : Refines ((andOrSrc true f zc uc).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
  obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
  obtain ⟨av, bv, ha, hb, ht⟩ := cICmp_test hu hpv hqv
  obtain ⟨av', bv', ha', hb', rfl⟩ := sub_value hs hr.y hy
  rw [ha] at ha'; cases ha'
  rw [hb] at hb'; cases hb'
  subst he
  simp only [↓reduceIte, ht]
  by_cases h0 : av - bv = 0#v
  · have : av = bv := eq_of_sub_eq_zero h0
    subst this
    rcases hp with rfl | rfl <;> simp [test, BitVec.ult_eq_decide]
  · have : (av - bv == 0#v) = false := by simpa using h0
    simp [test, this]

/-- `IS.simplifyUnsignedRangeCheck.L1545`: `A </> B && (A - B) != 0` to `A </> B`, and with `||`, to
`(A - B) != 0`. -/
theorem simplifyUnsignedRangeCheck.L1545 {fs : Flags} {a b : Term v} {u : Pred}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q a b = some u) (hp : u = .ult ∨ u = .ugt)
    (he : eqp = .ne) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then uc else zc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  -- `A </> B` implies `A - B != 0`.
  have himp : ub = true → zb = true := by
    intro hub
    obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
    obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
    obtain ⟨av, bv, ha, hb, ht⟩ := cICmp_test hu hpv hqv
    obtain ⟨av', bv', ha', hb', rfl⟩ := sub_value hs hr.y hy
    rw [ha] at ha'; cases ha'
    rw [hb] at hb'; cases hb'
    subst he
    rw [ht] at hub
    have hne : av ≠ bv := by
      rintro rfl
      rcases hp with rfl | rfl <;> simp [test, BitVec.ult_eq_decide] at hub
    have : av - bv ≠ 0#v := fun h0 => hne (eq_of_sub_eq_zero h0)
    simpa [test] using this
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1551`: `A <=/>= B && (A - B) == 0` to `(A - B) == 0`, and with `||`, to
`A <=/>= B`. -/
theorem simplifyUnsignedRangeCheck.L1551 {fs : Flags} {a b : Term v} {u : Pred}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q a b = some u) (hp : u = .ule ∨ u = .uge)
    (he : eqp = .eq) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then zc else uc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  -- `A - B == 0` implies `A <=/>= B`.
  have himp : zb = true → ub = true := by
    intro hzb
    obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
    obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
    obtain ⟨av, bv, ha, hb, ht⟩ := cICmp_test hu hpv hqv
    obtain ⟨av', bv', ha', hb', rfl⟩ := sub_value hs hr.y hy
    rw [ha] at ha'; cases ha'
    rw [hb] at hb'; cases hb'
    subst he
    rw [ht]
    have h0 : av - bv = 0#v := by simpa [test] using hzb
    have : av = bv := eq_of_sub_eq_zero h0
    subst this
    rcases hp with rfl | rfl <;> simp [test, BitVec.ule_eq_decide]
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1561`: `Y >= A && Y != 0` to `Y >= A`, where `Y = A - B` and `B` is known
non-zero. -/
theorem simplifyUnsignedRangeCheck.L1561 (ho : o.Sound ρ) {fs : Flags} {a b : Term v}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q y a = some .uge) (he : eqp = .ne)
    (hnz : o.nonZero b = true) : Refines ((andOrSrc true f zc uc).eval ρ) ((Repl.old uc).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  -- `Y >= A` implies `Y != 0`, as `A = B` isn't 0 when `Y` is.
  have himp : ub = true → zb = true := by
    intro hub
    obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
    obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
    obtain ⟨yv', av, hy', ha, ht⟩ := cICmp_test hu hpv hqv
    rw [hy] at hy'; cases hy'
    obtain ⟨av', bv, ha', hb, rfl⟩ := sub_value hs hr.y hy
    rw [ha] at ha'; cases ha'
    have hb0 := ho.nonZero b bv hnz hb
    subst he
    rw [ht] at hub
    simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq] at hub
    simp only [test, bne_iff_ne, ne_eq]
    intro h0
    rw [h0] at hub
    have : av = bv := eq_of_sub_eq_zero h0
    subst this
    apply hb0
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hub ⊢
    omega
  simp only [↓reduceIte, hw]
  cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1564`: `Y < A || Y == 0` to `Y < A`, where `Y = A - B` and `B` is known
non-zero. -/
theorem simplifyUnsignedRangeCheck.L1564 (ho : o.Sound ρ) {fs : Flags} {a b : Term v}
    (hs : binop? .sub y = some (fs, a, b)) (hu : cICmp up p q y a = some .ult) (he : eqp = .eq)
    (hnz : o.nonZero b = true) : Refines ((andOrSrc false f zc uc).eval ρ) ((Repl.old uc).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  -- `Y == 0` implies `Y < A`, as `A = B` isn't 0.
  have himp : zb = true → ub = true := by
    intro hzb
    obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
    obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
    obtain ⟨yv', av, hy', ha, ht⟩ := cICmp_test hu hpv hqv
    rw [hy] at hy'; cases hy'
    obtain ⟨av', bv, ha', hb, rfl⟩ := sub_value hs hr.y hy
    rw [ha] at ha'; cases ha'
    have hb0 := ho.nonZero b bv hnz hb
    subst he
    rw [ht]
    have h0 : av - bv = 0#v := by simpa [test] using hzb
    have : av = bv := eq_of_sub_eq_zero h0
    subst this
    rw [h0]
    have := toNat_ne_zero.1 hb0
    simp only [test, BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
    omega
  simp only [Bool.false_eq_true, ↓reduceIte, hw]
  cases zb <;> cases ub <;> simp_all

/-- The values in the `X`/`Y` cases: `ZeroICmp` is `EqPred` on `Y` and 0, and `UnsignedICmp` is `u` on `X` and
`Y`. -/
theorem xy_values {x : Term v} {u : Pred} (hxy : xyForm up p q y = some (x, u)) {zb ub : Bool}
    (hz : zc.denote ρ = some (BitVec.ofBool zb)) (hw : uc.denote ρ = some (BitVec.ofBool ub)) :
    ∃ xv yv, x.denote ρ = some xv ∧ zb = test eqp yv 0#v ∧ ub = test u xv yv := by
  obtain ⟨yv, hy, rfl⟩ := hr.zero zb hz
  obtain ⟨pv, qv, hpv, hqv, rfl⟩ := hr.unsigned ub hw
  obtain ⟨xv, yv', hx, hy', ht⟩ := xyForm_test hxy hpv hqv
  rw [hy] at hy'; cases hy'
  exact ⟨xv, yv, hx, rfl, ht⟩

/-- `IS.simplifyUnsignedRangeCheck.L1582`: `X > Y && Y == 0` to `Y == 0`, and with `||`, to `X > Y`, where `X` is
known non-zero. -/
theorem simplifyUnsignedRangeCheck.L1582 (ho : o.Sound ρ) {x : Term v} (hxy : xyForm up p q y = some (x, .ugt))
    (he : eqp = .eq) (hnz : o.nonZero x = true) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then zc else uc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  have himp : zb = true → ub = true := by
    obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
    subst he
    have := toNat_ne_zero.1 (ho.nonZero x xv hnz hx)
    simp only [test, beq_iff_eq, BitVec.ult_eq_decide, decide_eq_true_eq]
    rintro rfl
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1588`: `X <= Y && Y != 0` to `X <= Y`, and with `||`, to `Y != 0`, where `X` is
known non-zero. -/
theorem simplifyUnsignedRangeCheck.L1588 (ho : o.Sound ρ) {x : Term v} (hxy : xyForm up p q y = some (x, .ule))
    (he : eqp = .ne) (hnz : o.nonZero x = true) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then uc else zc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  have himp : ub = true → zb = true := by
    obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
    subst he
    have := toNat_ne_zero.1 (ho.nonZero x xv hnz hx)
    simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq, bne_iff_ne, ne_eq, BitVec.toNat_eq,
      BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1598`: `X < Y && Y != 0` to `X < Y`, and with `||`, to `Y != 0`. -/
theorem simplifyUnsignedRangeCheck.L1598 {x : Term v} (hxy : xyForm up p q y = some (x, .ult)) (he : eqp = .ne) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then uc else zc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  have himp : ub = true → zb = true := by
    obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
    subst he
    simp only [test, BitVec.ult_eq_decide, decide_eq_true_eq, bne_iff_ne, ne_eq, BitVec.toNat_eq,
      BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1603`: `X >= Y && Y == 0` to `Y == 0`, and with `||`, to `X >= Y`. -/
theorem simplifyUnsignedRangeCheck.L1603 {x : Term v} (hxy : xyForm up p q y = some (x, .uge)) (he : eqp = .eq) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) ((Repl.old (if isAnd then zc else uc)).eval ρ) := by
  rw [Repl.eval_old]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  have himp : zb = true → ub = true := by
    obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
    subst he
    simp only [test, beq_iff_eq, BitVec.ule_eq_decide, decide_eq_true_eq]
    rintro rfl
    simp
  cases isAnd
  · simp only [Bool.false_eq_true, ↓reduceIte, hw]
    cases zb <;> cases ub <;> simp_all
  · simp only [↓reduceIte, hz]
    cases zb <;> cases ub <;> simp_all

/-- `IS.simplifyUnsignedRangeCheck.L1608`: `X < Y && Y == 0` to false. -/
theorem simplifyUnsignedRangeCheck.L1608 {x : Term v} (hxy : xyForm up p q y = some (x, .ult)) (he : eqp = .eq) :
    Refines ((andOrSrc true f zc uc).eval ρ) (getFalse.eval ρ) := by
  rw [getFalse_eval]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
  subst he
  simp only [↓reduceIte]
  by_cases h0 : yv = 0#v
  · subst h0; simp [test, BitVec.ult_eq_decide]
  · have : (yv == 0#v) = false := by simpa using h0
    simp [test, this]

/-- `IS.simplifyUnsignedRangeCheck.L1613`: `X >= Y || Y != 0` to true. -/
theorem simplifyUnsignedRangeCheck.L1613 {x : Term v} (hxy : xyForm up p q y = some (x, .uge)) (he : eqp = .ne) :
    Refines ((andOrSrc false f zc uc).eval ρ) (getTrue.eval ρ) := by
  rw [getTrue_eval]
  refine andOrSrc_refines fun zb ub hz hw => ?_
  obtain ⟨xv, yv, hx, rfl, rfl⟩ := xy_values ρ zc uc eqp y up p q hr hxy hz hw
  subst he
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : yv = 0#v
  · subst h0; simp [test, BitVec.ule_eq_decide]
  · have : (yv != 0#v) = true := by simpa using h0
    simp [test, this]

end sites

/-! ### The fold -/

theorem ICmp.subOps_eq {y a b : Term v} (h : subOps y = some (a, b)) : ∃ fs, binop? .sub y = some (fs, a, b) := by
  unfold subOps at h
  split at h
  · next fs a' b' hs =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fs, hs⟩
  · cases h

theorem ICmp.pAB_eq {y : Term v} {u up : Pred} {p q : Term v} (h : predAB up p q y = some u) :
    ∃ fs a b, binop? .sub y = some (fs, a, b) ∧ cICmp up p q a b = some u := by
  unfold predAB at h
  split at h
  · next a b hab =>
    obtain ⟨fs, hs⟩ := subOps_eq hab
    exact ⟨fs, a, b, hs, h⟩
  · cases h

theorem ICmp.pYA_eq {y : Term v} {u up : Pred} {p q : Term v} {o : Oracle} (h : predYA up p q y = some u)
    (hn : nonZeroB o y = true) :
    ∃ fs a b, binop? .sub y = some (fs, a, b) ∧ cICmp up p q y a = some u ∧ o.nonZero b = true := by
  unfold predYA at h
  unfold nonZeroB at hn
  split at h
  · next a b hab =>
    rw [hab] at hn
    obtain ⟨fs, hs⟩ := subOps_eq hab
    exact ⟨fs, a, b, hs, h, hn⟩
  · cases h

/-- Every step of `simplifyUnsignedRangeCheck.inner` that fires is right. -/
theorem simplifyUnsignedRangeCheck.inner_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (zc uc : Term 1)
    (eqp : Pred) (y : Term v) (up : Pred) (p q : Term v) (isAnd : Bool) (f : Flags)
    (hr : RangeCheck ρ zc uc eqp y up p q) :
    ∀ site r, Step.fire site r ∈ inner o zc uc eqp y up p q isAnd →
      Refines ((andOrSrc isAnd f zc uc).eval ρ) (r.eval ρ) := by
  intro site r hmem
  simp only [inner, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨-, hp⟩, he⟩, rfl⟩ := hc
      obtain ⟨fs, a, b, hs, hu⟩ := pAB_eq hu
      exact L1534 ρ zc uc eqp y up p q f hr hs hu hp he
    · cases h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨-, hp⟩, he⟩, rfl⟩ := hc
      obtain ⟨fs, a, b, hs, hu⟩ := pAB_eq hu
      exact L1539 ρ zc uc eqp y up p q f hr hs hu hp he
    · cases h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨-, he⟩, hp⟩ := hc
      obtain ⟨fs, a, b, hs, hu⟩ := pAB_eq hu
      exact L1545 ρ zc uc eqp y up p q isAnd f hr hs hu hp he
    · cases h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨-, he⟩, hp⟩ := hc
      obtain ⟨fs, a, b, hs, hu⟩ := pAB_eq hu
      exact L1551 ρ zc uc eqp y up p q isAnd f hr hs hu hp he
    · cases h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, he⟩, hn⟩ := hc
      obtain ⟨fs, a, b, hs, hu, hnz⟩ := pYA_eq hu hn
      exact L1561 ρ o zc uc eqp y up p q f hr ho hs hu he hnz
    · cases h
  · split at h
    · next u hu =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, he⟩, hn⟩ := hc
      obtain ⟨fs, a, b, hs, hu, hnz⟩ := pYA_eq hu hn
      exact L1564 ρ o zc uc eqp y up p q f hr ho hs hu he hnz
    · cases h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, he⟩, hnz⟩ := hc
      exact L1582 ρ o zc uc eqp y up p q isAnd f hr ho hxy he hnz
    · cases h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, he⟩, hnz⟩ := hc
      exact L1588 ρ o zc uc eqp y up p q isAnd f hr ho hxy he hnz
    · cases h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, he⟩ := hc
      exact L1598 ρ zc uc eqp y up p q isAnd f hr hxy he
    · cases h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, he⟩ := hc
      exact L1603 ρ zc uc eqp y up p q isAnd f hr hxy he
    · cases h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, he⟩, rfl⟩ := hc
      exact L1608 ρ zc uc eqp y up p q f hr hxy he
    · cases h
  · split at h
    · next x u hxy =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨rfl, he⟩, rfl⟩ := hc
      exact L1613 ρ zc uc eqp y up p q f hr hxy he
    · cases h

/-- What two consistent compares say, as a `RangeCheck`, once `ZeroICmp` matched `icmp EqPred Y, 0`. -/
theorem simplifyUnsignedRangeCheck.rangeCheck {ρ : Env} {id id' : Nat} {eqp up : Pred} {s s' : Bool}
    {y z : Term v} {p q : Term v} (hz : zero z = true)
    (cz : (Term.icmp id eqp s y z).Consistent ρ) (cu : (Term.icmp id' up s' p q).Consistent ρ) :
    RangeCheck ρ (.icmp id eqp s y z) (.icmp id' up s' p q) eqp y up p q where
  zero zb h := by
    simp only [Term.Consistent] at cz
    simp only [Term.denote] at h
    rw [← cz.2.2] at h
    obtain ⟨yv, zv, hy, hzv, rfl⟩ := eval_ofBool h
    rw [cst_eq hz] at hzv
    cases hzv
    exact ⟨yv, hy, rfl⟩
  unsigned ub h := by
    simp only [Term.Consistent] at cu
    simp only [Term.denote] at h
    rw [← cu.2.2] at h
    obtain ⟨pv, qv, hp, hq, rfl⟩ := eval_ofBool h
    exact ⟨pv, qv, hp, hq, rfl⟩
  y := by
    simp only [Term.Consistent] at cz
    exact cz.1

/-- Theorem 1 for `simplifyUnsignedRangeCheck`: every value the model returns refines the `and` (if `isAnd`) or the
`or` of `ZeroICmp` and `UnsignedICmp`, with any flags, at every width, in every run the compares are consistent with,
poison and `samesign` included, given sound analyses. -/
theorem simplifyUnsignedRangeCheck.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (zc uc : Term 1) (isAnd : Bool)
    (f : Flags) (cz : zc.Consistent ρ) (cu : uc.Consistent ρ) {r : Repl 1}
    (h : simplifyUnsignedRangeCheck o zc uc isAnd = .value r) :
    Refines ((andOrSrc isAnd f zc uc).eval ρ) (r.eval ρ) := by
  unfold simplifyUnsignedRangeCheck at h
  cases zc
  case icmp v id eqp s y z =>
    simp only [steps] at h
    by_cases hc : (zero z && isEquality eqp) = true
    · simp only [hc, ↓reduceIte] at h
      simp only [Bool.and_eq_true] at hc
      cases uc
      case icmp v' id' up s' p q =>
        simp only at h
        cases hp : sameWidth (v := v) p with
        | none => simp [hp, run] at h
        | some p' =>
        cases hq : sameWidth (v := v) q with
        | none => simp [hp, hq, run] at h
        | some q' =>
        simp only [hp, hq] at h
        obtain ⟨rfl, rfl⟩ := sameWidth_eq hp
        obtain ⟨e, rfl⟩ := sameWidth_eq hq
        cases e
        exact run_sound (inner_sound ρ o ho _ _ eqp y up p q isAnd f (rangeCheck hc.1 cz cu)) h
      all_goals simp [run] at h
    · have hc' : (zero z && isEquality eqp) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      simp [run] at h
  all_goals simp [steps, run] at h

/-- `andOrSrc` with its operands the other way round is the same: `and` and `or` commute. -/
theorem ICmp.andOrSrc_comm (ρ : Env) (isAnd : Bool) (f : Flags) (a b : Term 1) :
    (andOrSrc isAnd f a b).eval ρ = (andOrSrc isAnd f b a).eval ρ := by
  show (if isAnd then BinOp.and else BinOp.or).eval f (a.denote ρ) (b.denote ρ) =
    (if isAnd then BinOp.and else BinOp.or).eval f (b.denote ρ) (a.denote ρ)
  cases ha : a.denote ρ <;> cases hb : b.denote ρ <;> cases isAnd <;>
    simp [BinOp.eval, Val.and, Val.or, Val.map₂, BitVec.and_comm, BitVec.or_comm]

/-- `simplifyUnsignedRangeCheck.sound` for the call with the compares the other way round, as
`simplifyAndOfICmps(Op0, Op1)` makes it second: `simplifyUnsignedRangeCheck(Op1, Op0, ...)`. -/
theorem simplifyUnsignedRangeCheck.sound_swap (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (zc uc : Term 1)
    (isAnd : Bool) (f : Flags) (cz : zc.Consistent ρ) (cu : uc.Consistent ρ) {r : Repl 1}
    (h : simplifyUnsignedRangeCheck o zc uc isAnd = .value r) :
    Refines ((andOrSrc isAnd f uc zc).eval ρ) (r.eval ρ) := by
  rw [andOrSrc_comm]
  exact sound ρ o ho zc uc isAnd f cz cu h

end Peephole.IS
