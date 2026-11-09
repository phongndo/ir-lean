import IRLean.Int
import IRLean.Refine

/-! # Facts about `add`, at every width, that InstSimplify's rewrites of it rest on

Each is about values, not about LLVM's code: a candidate for the lemma store, which any proof about an `add` can use.
The rewrite each one was cut from is named in its docstring. #47 proved them first, in
`tests/cpp_correspondence/SimplifyAddSound.lean`, about its own model. The two with a hypothesis have its
counterexample at the end, which the store needs. -/

namespace Peephole.Lemmas

open IRLean

variable {w : Nat}

theorem add_comm (a b : Val w) (nuw nsw : Bool) : Val.add a b nuw nsw = Val.add b a nuw nsw := by
  cases a <;> cases b <;> simp only [Val.add]
  rename_i x y
  have hu : x.uaddOverflow y = y.uaddOverflow x := by simp [BitVec.uaddOverflow, Nat.add_comm]
  have hs : x.saddOverflow y = y.saddOverflow x := by simp [BitVec.saddOverflow, Int.add_comm]
  rw [hu, hs, BitVec.add_comm]

theorem add_none_right (a : Val w) (nuw nsw : Bool) : Val.add a none nuw nsw = none := by
  cases a <;> rfl

/-- If an `add` of two values isn't poison, it's their sum. -/
theorem add_refines_of_sum {x y r : BitVec w} {nuw nsw : Bool} (h : x + y = r) :
    Refines (Val.add (some x) (some y) nuw nsw) (some r) := by
  simp only [Refines, Val.add]
  split
  · trivial
  · simp [Refine.le, h]

/-- `(b - a) + a` refines `b`, whatever the flags on either. `IS.simplifyAddInst.L621`. -/
theorem add_sub_cancel_refines (a b : Val w) (nuw nsw snuw snsw : Bool) :
    Refines (Val.add (Val.sub b a snuw snsw) a nuw nsw) b := by
  cases a with
  | none => simp [Refines, add_none_right, Refine.le]
  | some x =>
  cases b with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some y =>
  simp only [Val.sub]
  split
  · simp [Refines, Val.add, Refine.le]
  · exact add_refines_of_sum (BitVec.sub_add_cancel y x)

/-- `(a - b) + (b - a)` refines 0. `IS.simplifyAddInst.L613`, through `isKnownNegation`. -/
theorem add_sub_sub_refines (a b : Val w) (nuw nsw f1 f2 f3 f4 : Bool) :
    Refines (Val.add (Val.sub a b f1 f2) (Val.sub b a f3 f4) nuw nsw) (some 0#w) := by
  cases a with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some x =>
  cases b with
  | none => simp [Refines, Val.sub, Val.add, Refine.le]
  | some y =>
  simp only [Val.sub]
  split
  · simp [Refines, Val.add, Refine.le]
  · split
    · simp [Refines, add_none_right, Refine.le]
    · refine add_refines_of_sum ?_
      rw [show y - x = -(x - y) by rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.add_comm],
        BitVec.add_right_neg]

/-- `~a + a` refines all ones, with `~a` written `xor -1, a`. `IS.simplifyAddInst.L626`. -/
theorem add_not_left_refines (a : Val w) (nuw nsw : Bool) :
    Refines (Val.add (Val.xor (some (BitVec.allOnes w)) a) a nuw nsw) (some (BitVec.allOnes w)) := by
  cases a with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some x =>
  simp only [Val.xor, Val.map₂, BitVec.allOnes_xor]
  exact add_refines_of_sum (by rw [BitVec.add_comm, BitVec.add_not_self])

/-- `~a + a` refines all ones, with `~a` written `xor a, -1`. `IS.simplifyAddInst.L626`. -/
theorem add_not_right_refines (a : Val w) (nuw nsw : Bool) :
    Refines (Val.add (Val.xor a (some (BitVec.allOnes w))) a nuw nsw) (some (BitVec.allOnes w)) := by
  cases a with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some x =>
  simp only [Val.xor, Val.map₂, BitVec.xor_allOnes]
  exact add_refines_of_sum (by rw [BitVec.add_comm, BitVec.add_not_self])

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

/-- `(y ^ signmask) + signmask` refines `y`, whatever the flags. `IS.simplifyAddInst.L633`. -/
theorem add_xor_signMask_refines (y : Val w) (nuw nsw : Bool) :
    Refines (Val.add (Val.xor y (some (BitVec.intMin w))) (some (BitVec.intMin w)) nuw nsw) y := by
  cases y with
  | none => simp [Refines, Val.xor, Val.map₂, Val.add, Refine.le]
  | some x =>
  simp only [Val.xor, Val.map₂]
  exact add_refines_of_sum (by rw [add_intMin, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero])

/-- `add nuw x, -1` doesn't wrap only when `x` is 0. -/
theorem eq_zero_of_not_uaddOverflow_allOnes {x : BitVec w}
    (h : x.uaddOverflow (BitVec.allOnes w) = false) : x = 0#w := by
  simp only [BitVec.uaddOverflow, BitVec.toNat_allOnes, decide_eq_false_iff_not, Nat.not_le] at h
  have : 0 < 2 ^ w := Nat.two_pow_pos w
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- `add nuw x, -1` refines all ones, since `x` can only be 0. `IS.simplifyAddInst.L637`. -/
theorem add_nuw_allOnes_refines (a : Val w) (nsw : Bool) :
    Refines (Val.add a (some (BitVec.allOnes w)) true nsw) (some (BitVec.allOnes w)) := by
  cases a with
  | none => simp [Refines, Val.add, Refine.le]
  | some x =>
  simp only [Refines, Val.add, Bool.true_and]
  cases hov : x.uaddOverflow (BitVec.allOnes w)
  · rw [eq_zero_of_not_uaddOverflow_allOnes hov, BitVec.zero_add]
    split
    · trivial
    · simp [Refine.le]
  · simp [Refine.le]

end Peephole.Lemmas

/-! ### Counterexamples, for the lemma store

For each hypothesis `h` of a lemma above, `drop_h` says the lemma without it is false, and `sat` that its hypotheses
can all hold, by the names and in the form `tools/store/store.py` looks for. -/

/-- In `i1`, `0 + 0` is `0`, which `1` doesn't refine. -/
theorem LemmaStore.Counter.Peephole.Lemmas.add_refines_of_sum.drop_h :
    ¬ ∀ {w : Nat} {x y r : BitVec w} {nuw nsw : Bool},
      IRLean.Refines (IRLean.Val.add (some x) (some y) nuw nsw) (some r) :=
  fun h => absurd (show (some 1#1 : IRLean.Val 1) = some (0#1 + 0#1) from @h 1 0#1 0#1 1#1 false false) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.add_refines_of_sum.sat :
    ∃ (w : Nat) (x y r : BitVec w) (_ _ : Bool), x + y = r :=
  ⟨0, 0#0, 0#0, 0#0, false, false, rfl⟩

/-- In `i1`, `1` isn't `0`, and `1 + -1` wraps. -/
theorem LemmaStore.Counter.Peephole.Lemmas.eq_zero_of_not_uaddOverflow_allOnes.drop_h :
    ¬ ∀ {w : Nat} {x : BitVec w}, x = 0#w :=
  fun h => absurd (@h 1 1#1) (by decide)

theorem LemmaStore.Counter.Peephole.Lemmas.eq_zero_of_not_uaddOverflow_allOnes.sat :
    ∃ (w : Nat) (x : BitVec w), x.uaddOverflow (BitVec.allOnes w) = false :=
  ⟨1, 0#1, by decide⟩
