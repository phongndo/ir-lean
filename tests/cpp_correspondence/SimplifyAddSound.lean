import IRLean.Int
import IRLean.Refine
import SimplifyAddModel

/-! # Every value the `simplifyAddInst` model returns is right, at every width

`simplifyAddInst_sound` says: for every width, both flags, every recursion budget, and operands whose values are in
IRLean's domain, if the model of `SimplifyAddModel.lean` returns a value, that value is defined and refines the `add`
it replaces, in IRLean's semantics. Either the `add` is poison there, or the value is the `add`'s value.
`simplifyAddInst_refines` says the same with the shared relation, `IRLean.Refines`.

That's a theorem about the model. It says the rewrites the model makes are right. It doesn't say the C++ makes the
same ones: that's the manual translation `tests/cpp_correspondence.py` checks against the pinned source and `opt`.

What the operands mean: `denote ρ` gives each operand's value, where `ρ` gives each instruction and argument's.
`Consistent ρ` says each instruction's value is what its operation gives on its operands' values, so one `Value *`
has one value, as SSA has it. An `undef` anywhere has no value here, so the theorem says nothing about operands that
reach one: IRLean's values are a value or poison, and an `undef` can be a different value at each use. -/

namespace CppCorrespondence.SimplifyAdd

open IRLean

variable {w : Nat}

/-- An operand's value, given the value `ρ id` of each argument and instruction, or `none` where it reaches an
`undef`. -/
def Operand.denote (ρ : Nat → Val w) : Operand w → Option (Val w)
  | .const c => some (some c)
  | .poison => some none
  | .undef => none
  | .sub _ nuw nsw a b => do pure (Val.sub (← a.denote ρ) (← b.denote ρ) nuw nsw)
  | .xor _ a b => do pure (Val.xor (← a.denote ρ) (← b.denote ρ))
  | .add _ nuw nsw a b => do pure (Val.add (← a.denote ρ) (← b.denote ρ) nuw nsw)
  | .other id => some (ρ id)

/-- Each instruction in the tree has the value `ρ` gives its identity, so two operands with one identity have one
value. -/
def Operand.Consistent (ρ : Nat → Val w) : Operand w → Prop
  | .const _ | .poison | .undef | .other _ => True
  | .sub id nuw nsw a b =>
    a.Consistent ρ ∧ b.Consistent ρ ∧ (Operand.sub id nuw nsw a b).denote ρ = some (ρ id)
  | .xor id a b => a.Consistent ρ ∧ b.Consistent ρ ∧ (Operand.xor id a b).denote ρ = some (ρ id)
  | .add id nuw nsw a b =>
    a.Consistent ρ ∧ b.Consistent ρ ∧ (Operand.add id nuw nsw a b).denote ρ = some (ρ id)

/-! ### Lemmas -/

/-- Two operands that are the same `Value *` have the same value. -/
theorem denote_of_specific {ρ : Nat → Val w} {s v : Operand w} {vs vv : Val w}
    (cs : s.Consistent ρ) (cv : v.Consistent ρ) (h : specific s v = true)
    (hs : s.denote ρ = some vs) (hv : v.denote ρ = some vv) : vv = vs := by
  have key : ∀ (x : Operand w) (vx : Val w), x.Consistent ρ → x.denote ρ = some vx →
      ∀ id, x.ident = .node id → vx = ρ id := by
    intro x vx cx hx id hid
    cases x with
    | const | poison | undef => simp [Operand.ident] at hid
    | sub i nuw nsw a b =>
      simp only [Operand.ident, Ident.node.injEq] at hid; subst hid
      exact Option.some.inj (hx.symm.trans cx.2.2)
    | xor i a b =>
      simp only [Operand.ident, Ident.node.injEq] at hid; subst hid
      exact Option.some.inj (hx.symm.trans cx.2.2)
    | add i nuw nsw a b =>
      simp only [Operand.ident, Ident.node.injEq] at hid; subst hid
      exact Option.some.inj (hx.symm.trans cx.2.2)
    | other i =>
      simp only [Operand.ident, Ident.node.injEq] at hid; subst hid
      simpa [Operand.denote] using hx.symm
  simp only [specific, beq_iff_eq] at h
  cases s with
  | const c =>
    cases v <;> simp [Operand.ident] at h
    subst h; simp [Operand.denote] at hs hv; rw [← hs, ← hv]
  | poison =>
    cases v <;> simp [Operand.ident] at h
    simp [Operand.denote] at hs hv; rw [← hs, ← hv]
  | undef => simp [Operand.denote] at hs
  | sub i _ _ _ _ | xor i _ _ | add i _ _ _ _ | other i =>
    rw [key _ _ cv hv i h, key _ _ cs hs i rfl]

theorem cstPred_const {p : BitVec w → Bool} {v : Operand w} (h : cstPred p v = true) :
    ∃ c, v = .const c ∧ p c = true := by
  cases v <;> simp_all [cstPred]

theorem add_comm (a b : Val w) (nuw nsw : Bool) : Val.add a b nuw nsw = Val.add b a nuw nsw := by
  cases a <;> cases b <;> simp only [Val.add]
  rename_i x y
  have hu : x.uaddOverflow y = y.uaddOverflow x := by simp [BitVec.uaddOverflow, Nat.add_comm]
  have hs : x.saddOverflow y = y.saddOverflow x := by simp [BitVec.saddOverflow, Int.add_comm]
  rw [hu, hs, BitVec.add_comm]

/-- What every rewrite here comes down to: if the `add` of two values isn't poison, it's `r`. -/
theorem refines_of_sum {x y r : BitVec w} {nuw nsw : Bool} (h : x + y = r) :
    Val.add (some x) (some y) nuw nsw = none ∨ some r = Val.add (some x) (some y) nuw nsw := by
  simp only [Val.add]; split <;> simp [h]

/-- Adding `intMin` only flips the sign bit: no lower bit carries into it, and its carry out is dropped. -/
theorem add_intMin (x : BitVec w) : x + BitVec.intMin w = x ^^^ BitVec.intMin w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_add hi, BitVec.getLsbD_xor]
  suffices BitVec.carry i x (BitVec.intMin w) false = false by simp [this]
  simp only [BitVec.carry, BitVec.intMin, BitVec.toNat_twoPow, Bool.toNat_false, Nat.add_zero,
    decide_eq_false_iff_not, Nat.not_le]
  have hdiv : 2 ^ i ∣ 2 ^ (w - 1) % 2 ^ w := by
    rw [Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by omega))]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero]
  exact Nat.mod_lt _ (Nat.two_pow_pos i)

/-- `add nuw x, -1` doesn't wrap only when `x` is 0. -/
theorem eq_zero_of_not_uaddOverflow_allOnes {x : BitVec w}
    (h : x.uaddOverflow (BitVec.allOnes w) = false) : x = 0#w := by
  simp only [BitVec.uaddOverflow, BitVec.toNat_allOnes, decide_eq_false_iff_not, Nat.not_le] at h
  have : 0 < 2 ^ w := Nat.two_pow_pos w
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

theorem denote_sub {ρ : Nat → Val w} {id : Nat} {nuw nsw : Bool} {a b : Operand w} {v : Val w}
    (h : (Operand.sub id nuw nsw a b).denote ρ = some v) :
    ∃ va vb, a.denote ρ = some va ∧ b.denote ρ = some vb ∧ v = Val.sub va vb nuw nsw := by
  simp only [Operand.denote, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨va, ha, vb, hb, rfl⟩ := h
  exact ⟨va, vb, ha, hb, rfl⟩

theorem denote_xor {ρ : Nat → Val w} {id : Nat} {a b : Operand w} {v : Val w}
    (h : (Operand.xor id a b).denote ρ = some v) :
    ∃ va vb, a.denote ρ = some va ∧ b.denote ρ = some vb ∧ v = Val.xor va vb := by
  simp only [Operand.denote, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨va, ha, vb, hb, rfl⟩ := h
  exact ⟨va, vb, ha, hb, rfl⟩

theorem add_none_left (b : Val w) (nuw nsw : Bool) : Val.add none b nuw nsw = none := rfl

theorem add_none_right (a : Val w) (nuw nsw : Bool) : Val.add a none nuw nsw = none := by
  cases a <;> rfl

theorem sub_none_left (b : Val w) (nuw nsw : Bool) : Val.sub none b nuw nsw = none := rfl

theorem sub_none_right (a : Val w) (nuw nsw : Bool) : Val.sub a none nuw nsw = none := by
  cases a <;> rfl

/-- `a + (b - a)` and `(b - a) + a` refine `b`, whatever the flags on either. -/
theorem refines_sub_cancel (a b : Val w) (nuw nsw snuw snsw : Bool) :
    Val.add (Val.sub b a snuw snsw) a nuw nsw = none ∨ b = Val.add (Val.sub b a snuw snsw) a nuw nsw := by
  cases a with
  | none => exact Or.inl (add_none_right _ _ _)
  | some x =>
  cases b with
  | none => exact Or.inl rfl
  | some y =>
  simp only [Val.sub]
  split
  · exact Or.inl rfl
  · exact refines_of_sum (BitVec.sub_add_cancel y x)

/-- `(0 - a) + a` refines 0. -/
theorem refines_neg (a : Val w) (nuw nsw snuw snsw : Bool) :
    Val.add (Val.sub (some 0#w) a snuw snsw) a nuw nsw = none ∨
      some 0#w = Val.add (Val.sub (some 0#w) a snuw snsw) a nuw nsw :=
  refines_sub_cancel a (some 0#w) nuw nsw snuw snsw

/-- `(a - b) + (b - a)` refines 0. -/
theorem refines_sub_sub (a b : Val w) (nuw nsw f1 f2 f3 f4 : Bool) :
    Val.add (Val.sub a b f1 f2) (Val.sub b a f3 f4) nuw nsw = none ∨
      some 0#w = Val.add (Val.sub a b f1 f2) (Val.sub b a f3 f4) nuw nsw := by
  cases a with
  | none => exact Or.inl rfl
  | some x =>
  cases b with
  | none => exact Or.inl rfl
  | some y =>
  simp only [Val.sub]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl (add_none_right _ _ _)
    · refine refines_of_sum ?_
      rw [show y - x = -(x - y) by rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.add_comm],
        BitVec.add_right_neg]

/-- `~a + a` refines all ones, with `~a` as either `xor`. -/
theorem refines_not (a : Val w) (nuw nsw : Bool) :
    (Val.add (Val.xor (some (BitVec.allOnes w)) a) a nuw nsw = none ∨
      some (BitVec.allOnes w) = Val.add (Val.xor (some (BitVec.allOnes w)) a) a nuw nsw) ∧
    (Val.add (Val.xor a (some (BitVec.allOnes w))) a nuw nsw = none ∨
      some (BitVec.allOnes w) = Val.add (Val.xor a (some (BitVec.allOnes w))) a nuw nsw) := by
  cases a with
  | none => exact ⟨Or.inl rfl, Or.inl rfl⟩
  | some x =>
  simp only [Val.xor, Val.map₂, BitVec.allOnes_xor, BitVec.xor_allOnes]
  have : ~~~x + x = BitVec.allOnes w := by rw [BitVec.add_comm, BitVec.add_not_self]
  exact ⟨refines_of_sum this, refines_of_sum this⟩

/-- `(y ^ signmask) + signmask` refines `y`, whatever the flags. -/
theorem refines_signMask (y : Val w) (nuw nsw : Bool) :
    Val.add (Val.xor y (some (BitVec.intMin w))) (some (BitVec.intMin w)) nuw nsw = none ∨
      y = Val.add (Val.xor y (some (BitVec.intMin w))) (some (BitVec.intMin w)) nuw nsw := by
  cases y with
  | none => exact Or.inl rfl
  | some x =>
  simp only [Val.xor, Val.map₂]
  exact refines_of_sum (by rw [add_intMin, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])

/-- `add nuw x, -1` refines all ones. -/
theorem refines_nuw_allOnes (a : Val w) (nsw : Bool) :
    Val.add a (some (BitVec.allOnes w)) true nsw = none ∨
      some (BitVec.allOnes w) = Val.add a (some (BitVec.allOnes w)) true nsw := by
  cases a with
  | none => exact Or.inl rfl
  | some x =>
  simp only [Val.add, Bool.true_and]
  cases hov : x.uaddOverflow (BitVec.allOnes w)
  · rw [eq_zero_of_not_uaddOverflow_allOnes hov, BitVec.zero_add]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl (by simp)

/-! ### The theorem -/

/-- `afterFold`'s values refine the `add`. -/
theorem afterFold_sound (ρ : Nat → Val w) (op0 op1 r : Operand w) (isNSW isNUW : Bool) (maxRecurse : Nat)
    (v0 v1 : Val w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : op0.denote ρ = some v0) (h1 : op1.denote ρ = some v1)
    (h : afterFold op0 op1 isNSW isNUW maxRecurse = .value r) :
    ∃ vr, r.denote ρ = some vr ∧
      (Val.add v0 v1 isNUW isNSW = none ∨ vr = Val.add v0 v1 isNUW isNSW) := by
  unfold afterFold at h
  split at h
  · -- X + poison -> poison
    rename_i hp
    cases h
    simp only [beq_iff_eq] at hp; subst hp
    simp only [Operand.denote, Option.some.injEq] at h1; subst h1
    exact ⟨none, rfl, Or.inl (add_none_right _ _ _)⟩
  split at h
  · -- X + undef -> undef: poison is ruled out, and undef has no value here
    rename_i hp hu
    cases h
    cases op1 <;> simp_all [isUndefValue, Operand.denote]
  split at h
  · -- X + 0 -> X
    rename_i hz
    cases h
    obtain ⟨c, rfl, hc⟩ := cstPred_const hz
    simp only [beq_iff_eq] at hc; subst hc
    simp only [Operand.denote, Option.some.injEq] at h1; subst h1
    refine ⟨v0, h0, ?_⟩
    cases v0 with
    | none => exact Or.inl rfl
    | some x => exact refines_of_sum (BitVec.add_zero x)
  split at h
  · -- isKnownNegation -> 0
    rename_i hn
    cases h
    refine ⟨some 0#w, rfl, ?_⟩
    simp only [isKnownNegation, Bool.or_eq_true] at hn
    rcases hn with (hn | hn) | hn
    · -- op0 is 0 - op1
      cases op0 <;> simp only [isKnownNegation.negationOf, Bool.false_eq_true] at hn
      rename_i id nuw nsw z v
      simp only [Bool.and_eq_true] at hn
      obtain ⟨c, rfl, hc⟩ := cstPred_const hn.1
      simp only [beq_iff_eq] at hc; subst hc
      obtain ⟨va, vb, ha, hb, rfl⟩ := denote_sub h0
      simp only [Operand.denote, Option.some.injEq] at ha; subst ha
      rw [denote_of_specific c1 c0.2.1 hn.2 h1 hb]
      exact refines_neg v1 _ _ _ _
    · -- op1 is 0 - op0
      cases op1 <;> simp only [isKnownNegation.negationOf, Bool.false_eq_true] at hn
      rename_i id nuw nsw z v
      simp only [Bool.and_eq_true] at hn
      obtain ⟨c, rfl, hc⟩ := cstPred_const hn.1
      simp only [beq_iff_eq] at hc; subst hc
      obtain ⟨va, vb, ha, hb, rfl⟩ := denote_sub h1
      simp only [Operand.denote, Option.some.injEq] at ha; subst ha
      rw [denote_of_specific c0 c1.2.1 hn.2 h0 hb, add_comm]
      exact refines_neg v0 _ _ _ _
    · -- op0 is a - b, op1 is b - a
      cases op0 <;> cases op1 <;> simp only [isKnownNegation.subSwapped, Bool.false_eq_true] at hn
      simp only [Bool.and_eq_true] at hn
      obtain ⟨va, vb, ha, hb, rfl⟩ := denote_sub h0
      obtain ⟨vb', va', hb', ha', rfl⟩ := denote_sub h1
      rw [denote_of_specific c0.2.1 c1.1 hn.1 hb hb', denote_of_specific c0.1 c1.2.1 hn.2 ha ha']
      exact refines_sub_sub va vb _ _ _ _ _ _
  split at h
  · -- X + (Y - X) -> Y
    rename_i y hs
    cases h
    cases op1 <;> simp only [subSpecific, Option.ite_none_right_eq_some, Option.some.injEq,
      reduceCtorEq] at hs
    obtain ⟨hsp, rfl⟩ := hs
    obtain ⟨vy, vb, hy, hb, rfl⟩ := denote_sub h1
    rw [denote_of_specific c0 c1.2.1 hsp h0 hb, add_comm]
    exact ⟨vy, hy, refines_sub_cancel v0 vy _ _ _ _⟩
  split at h
  · -- (Y - X) + X -> Y
    rename_i y hs
    cases h
    cases op0 <;> simp only [subSpecific, Option.ite_none_right_eq_some, Option.some.injEq,
      reduceCtorEq] at hs
    obtain ⟨hsp, rfl⟩ := hs
    obtain ⟨vy, vb, hy, hb, rfl⟩ := denote_sub h0
    rw [denote_of_specific c1 c0.2.1 hsp h1 hb]
    exact ⟨vy, hy, refines_sub_cancel v1 vy _ _ _ _⟩
  split at h
  · -- X + ~X -> -1
    rename_i hn
    cases h
    refine ⟨some (BitVec.allOnes w), rfl, ?_⟩
    simp only [Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · -- op0 is ~op1
      cases op0 <;> simp only [notSpecific, Bool.false_eq_true] at hn
      obtain ⟨va, vb, ha, hb, rfl⟩ := denote_xor h0
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hn
      rcases hn with ⟨ho, hsp⟩ | ⟨ho, hsp⟩
      · obtain ⟨c, rfl, hc⟩ := cstPred_const ho
        simp only [beq_iff_eq] at hc; subst hc
        simp only [Operand.denote, Option.some.injEq] at ha; subst ha
        rw [denote_of_specific c1 c0.2.1 hsp h1 hb]
        exact (refines_not v1 _ _).1
      · obtain ⟨c, rfl, hc⟩ := cstPred_const ho
        simp only [beq_iff_eq] at hc; subst hc
        simp only [Operand.denote, Option.some.injEq] at hb; subst hb
        rw [denote_of_specific c1 c0.1 hsp h1 ha]
        exact (refines_not v1 _ _).2
    · -- op1 is ~op0
      cases op1 <;> simp only [notSpecific, Bool.false_eq_true] at hn
      obtain ⟨va, vb, ha, hb, rfl⟩ := denote_xor h1
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hn
      rw [add_comm]
      rcases hn with ⟨ho, hsp⟩ | ⟨ho, hsp⟩
      · obtain ⟨c, rfl, hc⟩ := cstPred_const ho
        simp only [beq_iff_eq] at hc; subst hc
        simp only [Operand.denote, Option.some.injEq] at ha; subst ha
        rw [denote_of_specific c0 c1.2.1 hsp h0 hb]
        exact (refines_not v0 _ _).1
      · obtain ⟨c, rfl, hc⟩ := cstPred_const ho
        simp only [beq_iff_eq] at hc; subst hc
        simp only [Operand.denote, Option.some.injEq] at hb; subst hb
        rw [denote_of_specific c0 c1.1 hsp h0 ha]
        exact (refines_not v0 _ _).2
  split at h
  · -- add nsw/nuw (xor Y, signmask), signmask -> Y
    rename_i y hg hx
    cases h
    -- Only the sign mask matters here: the rewrite is right whatever the flags.
    have hs : signMask op1 = true := by revert hg; cases signMask op1 <;> simp
    obtain ⟨c, rfl, hc⟩ := cstPred_const hs
    simp only [beq_iff_eq] at hc; subst hc
    simp only [Operand.denote, Option.some.injEq] at h1; subst h1
    cases op0 <;> simp only [xorSignMask, Option.ite_none_right_eq_some, Option.some.injEq,
      reduceCtorEq] at hx
    obtain ⟨hm, rfl⟩ := hx
    obtain ⟨c', rfl, hc'⟩ := cstPred_const hm
    simp only [beq_iff_eq] at hc'; subst hc'
    obtain ⟨vy, vb, hy, hb, rfl⟩ := denote_xor h0
    simp only [Operand.denote, Option.some.injEq] at hb; subst hb
    exact ⟨vy, hy, refines_signMask vy _ _⟩
  split at h
  · -- add nuw %x, -1 -> -1
    rename_i hg
    cases h
    simp only [Bool.and_eq_true] at hg
    obtain ⟨rfl, ho⟩ := hg
    obtain ⟨c, rfl, hc⟩ := cstPred_const ho
    simp only [beq_iff_eq] at hc; subst hc
    simp only [Operand.denote, Option.some.injEq] at h1; subst h1
    exact ⟨_, rfl, refines_nuw_allOnes v0 _⟩
  -- What's left delegates or returns null.
  split at h
  · cases h
  split at h
  · cases h
  split at h <;> cases h

/-- **Every value the model of `simplifyAddInst` returns is right.** At every width `w`, with any flags and
recursion budget, for operands that are consistent and in IRLean's domain, a returned value is defined, and either
the `add` it replaces is poison or the value is the `add`'s. `Val.add` takes `nuw` before `nsw`, and
`simplifyAddInst` takes `IsNSW` before `IsNUW`, as the C++ does. -/
theorem simplifyAddInst_sound (ρ : Nat → Val w) (op0 op1 r : Operand w) (isNSW isNUW : Bool)
    (maxRecurse : Nat) (v0 v1 : Val w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : op0.denote ρ = some v0) (h1 : op1.denote ρ = some v1)
    (h : simplifyAddInst op0 op1 isNSW isNUW maxRecurse = .value r) :
    ∃ vr, r.denote ρ = some vr ∧
      (Val.add v0 v1 isNUW isNSW = none ∨ vr = Val.add v0 v1 isNUW isNSW) := by
  unfold simplifyAddInst at h
  split at h
  · split at h
    · cases h
    · rw [add_comm v0 v1]
      exact afterFold_sound ρ op1 op0 r isNSW isNUW maxRecurse v1 v0 c1 c0 h1 h0 h
  · exact afterFold_sound ρ op0 op1 r isNSW isNUW maxRecurse v0 v1 c0 c1 h0 h1 h

/-- The same, as `IRLean.Refines`: the value returned refines the `add` it replaces. -/
theorem simplifyAddInst_refines (ρ : Nat → Val w) (op0 op1 r : Operand w) (isNSW isNUW : Bool)
    (maxRecurse : Nat) (v0 v1 : Val w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : op0.denote ρ = some v0) (h1 : op1.denote ρ = some v1)
    (h : simplifyAddInst op0 op1 isNSW isNUW maxRecurse = .value r) :
    ∃ vr, r.denote ρ = some vr ∧ Refines (Val.add v0 v1 isNUW isNSW) vr := by
  obtain ⟨vr, hr, hv⟩ := simplifyAddInst_sound ρ op0 op1 r isNSW isNUW maxRecurse v0 v1 c0 c1 h0 h1 h
  exact ⟨vr, hr, (Refine.val_iff _ _).2 hv⟩

end CppCorrespondence.SimplifyAdd
