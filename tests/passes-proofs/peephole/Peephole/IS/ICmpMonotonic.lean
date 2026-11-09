import Peephole.IS.ICmpBase

/-! # InstSimplify's `simplifyICmpUsingMonotonicValues`, and its rewrite for every input

`simplifyICmpUsingMonotonicValues` is at `llvm/lib/Analysis/InstructionSimplify.cpp:3208-3225` at `llvmorg-23.1.3`,
with `getUnsignedMonotonicValues` before it. For `icmp uge` and `icmp ult`, it collects values the left operand is
known to be at least, and values the right operand is known to be at most; one in both decides the comparison.

| ID | Rewrite |
| --- | --- |
| `IS.simplifyICmpUsingMonotonicValues.L3222` | `LHS >=u RHS` to true, and `LHS <u RHS` to false, where `LHS >=u V` and `V >=u RHS` for some `V` |

`getUnsignedMonotonicValues` recurses with a depth limit of 1: from `V` it adds `V`, and if `V` is an instruction,
the operands it reads, without looking into them. -/

namespace Peephole.IS

open IRLean ICmp

variable {w : Nat}

/-! ### `getUnsignedMonotonicValues` -/

/-- `getUnsignedMonotonicValues(Res, V, MonotonicType::GreaterEq, Q)` from depth 0: `V`, and values `V` is at least
by its operation: the operands of an `or` or a `uadd.sat`, and an operand of a `mul nuw` whose other operand is known
non-zero. -/
def ICmp.greaterValues (o : Oracle) (v : Term w) : List (Term w) :=
  v :: match v with
  | .bin _ .or _ x y => [x, y]
  | .bi _ .uaddSat x y => [x, y]
  | .bin _ .mul f x y =>
    if f.nuw then (if o.nonZero x then [y] else []) ++ (if o.nonZero y then [x] else []) else []
  | _ => []

/-- `getUnsignedMonotonicValues(Res, V, MonotonicType::LowerEq, Q)` from depth 0: `V`, and values `V` is at most by
its operation: the operands of an `and`, the first operand of a `urem`, `udiv` or `lshr`, and the first argument of a
`usub.sat`. -/
def ICmp.lowerValues (v : Term w) : List (Term w) :=
  v :: match v with
  | .bin _ .and _ x y => [x, y]
  | .bin _ .urem _ x _ | .bin _ .udiv _ x _ | .bin _ .lshr _ x _ => [x]
  | .bi _ .usubSat x _ => [x]
  | _ => []

namespace ICmp

theorem or_some {a b : Val w} {d : Bool} {z : BitVec w} (h : Val.or a b d = some z) :
    ∃ x y, a = some x ∧ b = some y ∧ z = x ||| y := by
  cases a <;> cases b <;> simp only [Val.or, reduceCtorEq] at h
  next x y =>
  split at h
  · cases h
  · exact ⟨x, y, rfl, rfl, (Option.some.inj h).symm⟩

theorem map₂_some {f : BitVec w → BitVec w → BitVec w} {a b : Val w} {z : BitVec w} (h : Val.map₂ f a b = some z) :
    ∃ x y, a = some x ∧ b = some y ∧ z = f x y := by
  cases a <;> cases b <;> simp only [Val.map₂, reduceCtorEq] at h
  next x y => exact ⟨x, y, rfl, rfl, (Option.some.inj h).symm⟩

theorem mul_nuw_some {a b : Val w} {nsw : Bool} {z : BitVec w} (h : Val.mul a b true nsw = some z) :
    ∃ x y, a = some x ∧ b = some y ∧ x.umulOverflow y = false ∧ z = x * y := by
  cases a <;> cases b <;> simp only [Val.mul, reduceCtorEq] at h
  next x y =>
  split at h
  · cases h
  · next hc =>
    simp only [Bool.true_and, Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    exact ⟨x, y, rfl, rfl, hc.1, (Option.some.inj h).symm⟩

/-- Each value `greaterValues` gives is at most `V`, and not poison where `V` isn't. -/
theorem greaterValues_le {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {v g : Term w} (hg : g ∈ greaterValues o v)
    (hc : v.Consistent ρ) {z : BitVec w} (hz : v.denote ρ = some z) :
    ∃ y, g.denote ρ = some y ∧ BitVec.ule y z = true := by
  simp only [greaterValues, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact ⟨z, hz, by simp [BitVec.ule_eq_decide]⟩
  · split at hg
    · next id f x y =>
      simp only [Term.Consistent, BinOp.eval] at hc
      have hd := ok_inj hc.2.2
      simp only [Term.denote] at hz
      rw [hz] at hd
      obtain ⟨a, b, ha, hb, rfl⟩ := or_some hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨a, ha, Lemmas.ule_or_self_left a b⟩
      · exact ⟨b, hb, Lemmas.ule_or_self_right a b⟩
    · next id x y =>
      simp only [Term.Consistent, BinIntr.eval, Val.uaddSat] at hc
      have hd := hc.2.2
      simp only [Term.denote] at hz
      rw [hz] at hd
      obtain ⟨a, b, ha, hb, rfl⟩ := map₂_some hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ⟨a, ha, Lemmas.ule_uaddSat_left a b⟩
      · exact ⟨b, hb, Lemmas.ule_uaddSat_right a b⟩
    · next id f x y =>
      split at hg
      · next hf =>
        simp only [Term.Consistent, BinOp.eval] at hc
        have hd := ok_inj hc.2.2
        simp only [Term.denote] at hz
        rw [hz, hf] at hd
        obtain ⟨a, b, ha, hb, hov, rfl⟩ := mul_nuw_some hd
        simp only [List.mem_append] at hg
        rcases hg with hg | hg
        · split at hg
          · next hx =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            subst hg
            exact ⟨b, hb, Lemmas.ule_mul_right hov (ho.nonZero x a hx ha)⟩
          · cases hg
        · split at hg
          · next hy =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            subst hg
            exact ⟨a, ha, Lemmas.ule_mul_left hov (ho.nonZero y b hy hb)⟩
          · cases hg
      · cases hg
    · cases hg

theorem urem_some {a b : Val w} {z : BitVec w} (h : Val.urem a b = Outcome.ok (some z)) :
    ∃ x y, a = some x ∧ b = some y ∧ z = x % y := by
  cases b with
  | none => simp [Val.urem, Outcome.ub, Outcome.ok] at h
  | some y =>
  simp only [Val.urem] at h
  split at h
  · simp [Outcome.ub, Outcome.ok] at h
  · cases a with
    | none => simp [Outcome.ok] at h
    | some x => exact ⟨x, y, rfl, rfl, (Option.some.inj (ok_inj h)).symm⟩

theorem udiv_some {a b : Val w} {e : Bool} {z : BitVec w} (h : Val.udiv a b e = Outcome.ok (some z)) :
    ∃ x y, a = some x ∧ b = some y ∧ z = x / y := by
  cases b with
  | none => simp [Val.udiv, Outcome.ub, Outcome.ok] at h
  | some y =>
  simp only [Val.udiv] at h
  split at h
  · simp [Outcome.ub, Outcome.ok] at h
  · cases a with
    | none => simp [Outcome.ok] at h
    | some x =>
      have h' := ok_inj h
      split at h'
      · cases h'
      · exact ⟨x, y, rfl, rfl, (Option.some.inj h').symm⟩

theorem lshr_some {a b : Val w} {e : Bool} {z : BitVec w} (h : Val.lshr a b e = some z) :
    ∃ x y, a = some x ∧ b = some y ∧ z = x >>> y := by
  cases a <;> cases b <;> simp only [Val.lshr, reduceCtorEq] at h
  next x y =>
  split at h
  · cases h
  · split at h
    · cases h
    · exact ⟨x, y, rfl, rfl, (Option.some.inj h).symm⟩

/-- Each value `lowerValues` gives is at least `V`, and not poison where `V` isn't. -/
theorem lowerValues_ge {ρ : Env} {v l : Term w} (hl : l ∈ lowerValues v) (hc : v.Consistent ρ) {z : BitVec w}
    (hz : v.denote ρ = some z) : ∃ y, l.denote ρ = some y ∧ BitVec.ule z y = true := by
  simp only [lowerValues, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact ⟨z, hz, by simp [BitVec.ule_eq_decide]⟩
  · split at hl
    · next id f x y =>
      simp only [Term.Consistent, BinOp.eval, Val.and] at hc
      have hd := ok_inj hc.2.2
      simp only [Term.denote] at hz
      rw [hz] at hd
      obtain ⟨a, b, ha, hb, rfl⟩ := map₂_some hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨a, ha, Lemmas.and_ule_left a b⟩
      · exact ⟨b, hb, Lemmas.and_ule_right a b⟩
    · next id f x y =>
      simp only [Term.Consistent, BinOp.eval] at hc
      simp only [Term.denote] at hz
      rw [hz] at hc
      obtain ⟨a, b, ha, hb, rfl⟩ := urem_some hc.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact ⟨a, ha, Lemmas.umod_ule a b⟩
    · next id f x y =>
      simp only [Term.Consistent, BinOp.eval] at hc
      simp only [Term.denote] at hz
      rw [hz] at hc
      obtain ⟨a, b, ha, hb, rfl⟩ := udiv_some hc.2.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact ⟨a, ha, Lemmas.udiv_ule a b⟩
    · next id f x y =>
      simp only [Term.Consistent, BinOp.eval] at hc
      have hd := ok_inj hc.2.2
      simp only [Term.denote] at hz
      rw [hz] at hd
      obtain ⟨a, b, ha, hb, rfl⟩ := lshr_some hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact ⟨a, ha, Lemmas.ushiftRight_ule a b⟩
    · next id x y =>
      simp only [Term.Consistent, BinIntr.eval, Val.usubSat] at hc
      have hd := hc.2.2
      simp only [Term.denote] at hz
      rw [hz] at hd
      obtain ⟨a, b, ha, hb, rfl⟩ := map₂_some hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      exact ⟨a, ha, Lemmas.usubSat_ule a b⟩
    · cases hl

end ICmp

/-! ### The model -/

/-- Whether a value in `greaterValues o LHS` is in `lowerValues RHS`, by address: the C++'s loop over
`GreaterValues` testing `LowerValues.contains(GV)`. -/
def simplifyICmpUsingMonotonicValues.shared (o : Oracle) (lhs rhs : Term w) : Bool :=
  (greaterValues o lhs).any fun g => (lowerValues rhs).any fun l => specific g l

/-- `simplifyICmpUsingMonotonicValues(Pred, LHS, RHS, Q)`, step by step. -/
def simplifyICmpUsingMonotonicValues.steps (o : Oracle) (p : Pred) (lhs rhs : Term w) : List (Step 1) :=
  [ if p != .uge && p != .ult then .decline else .next,
    -- We have LHS uge GreaterValues and LowerValues uge RHS. If any of the GreaterValues and LowerValues are the
    -- same, it follows that LHS uge RHS.
    if shared o lhs rhs then .fire "IS.simplifyICmpUsingMonotonicValues.L3222" (getBool (p == .uge)) else .next ]

def simplifyICmpUsingMonotonicValues (o : Oracle) (p : Pred) (lhs rhs : Term w) : Result 1 :=
  run (simplifyICmpUsingMonotonicValues.steps o p lhs rhs)

/-! ### The rewrite -/

/-- `IS.simplifyICmpUsingMonotonicValues.L3222`: `LHS >=u RHS` to true and `LHS <u RHS` to false, where some `V` has
`LHS >=u V` and `V >=u RHS`. -/
theorem simplifyICmpUsingMonotonicValues.L3222 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (c0 : lhs.Consistent ρ) (c1 : rhs.Consistent ρ) (hp : p = .uge ∨ p = .ult)
    (h : shared o lhs rhs = true) :
    Refines ((src p s lhs rhs).eval ρ) ((getBool (p == .uge)).eval ρ) := by
  rw [getBool_eval]
  refine src_refines_const fun a b ha hb => ?_
  simp only [shared, List.any_eq_true] at h
  obtain ⟨g, hg, l, hl, hs⟩ := h
  obtain ⟨y, hy, hya⟩ := greaterValues_le ho hg c0 ha
  obtain ⟨y', hy', hby⟩ := lowerValues_ge hl c1 hb
  rw [specific_denote hs, hy] at hy'
  cases hy'
  simp only [BitVec.ule_eq_decide, decide_eq_true_eq] at hya hby
  rcases hp with rfl | rfl
  · show test .uge a b = true
    simp only [test, BitVec.ule_eq_decide, decide_eq_true_eq]
    omega
  · show test .ult a b = false
    simp only [test, BitVec.ult_eq_decide, decide_eq_false_iff_not]
    omega

/-! ### The fold -/

theorem simplifyICmpUsingMonotonicValues.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred)
    (s : Bool) (lhs rhs : Term w) (c0 : lhs.Consistent ρ) (c1 : rhs.Consistent ρ) :
    ∀ pre site r post, simplifyICmpUsingMonotonicValues.steps o p lhs rhs = pre ++ Step.fire site r :: post →
      (∀ st ∈ pre, st = .next) → Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) := by
  intro pre site r post hs hpre
  unfold steps at hs
  match pre, hs with
  | [], hs =>
    simp only [List.nil_append, List.cons.injEq] at hs
    split at hs <;> simp at hs
  | [s0], hs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hs
    obtain ⟨h0, h1, -⟩ := hs
    have := hpre s0 (by simp)
    subst this
    split at h0
    · cases h0
    · next hp =>
      split at h1 <;> simp only [Step.fire.injEq, reduceCtorEq] at h1
      next hc =>
      obtain ⟨-, rfl⟩ := h1
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hp
      exact L3222 ρ o ho p s lhs rhs c0 c1 (by by_cases h : p = .uge <;> simp_all) hc
  | _ :: _ :: pre', hs =>
    simp only [List.cons_append, List.cons.injEq] at hs
    obtain ⟨-, -, hs⟩ := hs
    simp at hs

/-- Theorem 1 for `simplifyICmpUsingMonotonicValues`: every value the model returns refines the `icmp`, with or
without `samesign`, at every width, in every run its operands are consistent with, poison included, given sound
analyses. -/
theorem simplifyICmpUsingMonotonicValues.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (p : Pred) (s : Bool)
    (lhs rhs : Term w) (c0 : lhs.Consistent ρ) (c1 : rhs.Consistent ρ) {r : Repl 1}
    (h : simplifyICmpUsingMonotonicValues o p lhs rhs = .value r) :
    Refines ((src p s lhs rhs).eval ρ) (r.eval ρ) :=
  run_sound_ordered (steps_sound ρ o ho p s lhs rhs c0 c1) h

end Peephole.IS
