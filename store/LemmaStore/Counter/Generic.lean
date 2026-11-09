import IRLean.Generic.Arith
import IRLean.Generic.Bitwise

/-! # Counterexamples for the rewrites at every width

For each hypothesis of a lemma from `IRLean.Generic`, the lemma without it is false: `drop_<hypothesis>` gives one
input where it fails. For each lemma with hypotheses, `sat` gives one input where they all hold. Most inputs are the
ones `tests/generic_rewrites/RewriteCounter.lean` uses. `tools/store/store.py check` checks each states exactly what it
has to.

Two of `IRLean.Generic`'s lemmas have no counterexample here, because none exists: `shl_lshr_eq_iff` and
`shl_sshr_eq_iff` hold without their bound on `k`, since past the width both sides say `x = 0`. The store refuses
them for that, as `docs/lemma-store.md` records. -/

namespace LemmaStore.Counter

open IRLean

/-- A source that's the value `x` only allows `x`. -/
theorem not_refines {w : Nat} {a b : Val w} (x : BitVec w) (ha : a = some x) (hb : b ≠ some x) : ¬ Refines a b := by
  subst ha; exact fun r => hb ((Refine.val_some x b).1 r)

/-! ### `IRLean.Generic.BitVec` -/

/-- Past the width, `BitVec.ofNat` wraps: `1` at width zero is `0`. -/
theorem IRLean.Generic.toNat_ofNat_of_lt.drop_hk : ¬ ∀ {w k : Nat}, (BitVec.ofNat w k).toNat = k :=
  fun h => absurd (@h 0 1) (by decide)

theorem IRLean.Generic.toNat_ofNat_of_lt.sat : ∃ (w k : Nat), k < w := ⟨1, 0, Nat.one_pos⟩

/-- At `k = w`, `2 ^ k` wraps to `0`, which never overflows, while shifting `1` out and back loses it. -/
theorem IRLean.Generic.umulOverflow_twoPow.drop_hk :
    ¬ ∀ {w : Nat} (x : BitVec w) {k : Nat}, x.umulOverflow (BitVec.twoPow w k) = !decide ((x <<< k) >>> k = x) :=
  fun h => absurd (@h 1 1#1 1) (by decide)

theorem IRLean.Generic.umulOverflow_twoPow.sat : ∃ (w : Nat) (_ : BitVec w) (k : Nat), k < w :=
  ⟨1, 0#1, 0, Nat.one_pos⟩

/-- At `k + 1 = w`, `2 ^ k` is the signed minimum: `1 * -2` fits in `i2`, and shifting `1` left and back doesn't. -/
theorem IRLean.Generic.smulOverflow_twoPow.drop_hk :
    ¬ ∀ {w : Nat} (x : BitVec w) {k : Nat},
      x.smulOverflow (BitVec.twoPow w k) = !decide ((x <<< k).sshiftRight k = x) :=
  fun h => absurd (@h 2 1#2 1) (by decide)

theorem IRLean.Generic.smulOverflow_twoPow.sat : ∃ (w : Nat) (_ : BitVec w) (k : Nat), k + 1 < w :=
  ⟨2, 0#2, 0, by decide⟩

/-! ### `IRLean.Generic.Arith` -/

/-- `mul nsw i1 1, 1` is poison, since `-1 * -1` doesn't fit. -/
theorem IRLean.Generic.mul_one.drop_h :
    ¬ ∀ {w : Nat} (a : Val w) (nuw nsw : Bool), Val.mul a (some 1#w) nuw nsw = a :=
  fun h => absurd (@h 1 (some 1#1) false true) (by decide)

theorem IRLean.Generic.mul_one.sat : ∃ (w : Nat) (_ : Val w) (_ nsw : Bool), nsw = false ∨ w ≠ 1 :=
  ⟨0, none, false, false, .inl rfl⟩

/-- In `i1`, `add 0, 0` is `0`, and `shl 0, 1` is poison. -/
theorem IRLean.Generic.add_self.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (nuw nsw : Bool), Val.add a a nuw nsw = Val.shl a (some 1#w) nuw nsw :=
  fun h => absurd (@h 1 (some 0#1) false false) (by decide)

theorem IRLean.Generic.add_self.sat : ∃ (w : Nat) (_ : Val w) (_ _ : Bool), 1 < w :=
  ⟨2, none, false, false, by decide⟩

/-- `mul 1, 3` is `3`, and `shl 1, 1` is `2`: the constant has to be `2 ^ k`. -/
theorem IRLean.Generic.mul_twoPow.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} {k : Nat}, k < w → ∀ (nuw nsw : Bool), nsw = false ∨ k + 1 < w →
      Val.mul a (some c) nuw nsw = Val.shl a (some (BitVec.ofNat w k)) nuw nsw :=
  fun h => absurd (@h 8 (some 1#8) 3#8 1 (by decide) false false (.inl rfl)) (by decide)

/-- `twoPow 8 8` is `0`, so `mul 1, 0` is `0`, and `shl 1, 8` is poison. -/
theorem IRLean.Generic.mul_twoPow.drop_hk :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} {k : Nat}, c = BitVec.twoPow w k → ∀ (nuw nsw : Bool),
      nsw = false ∨ k + 1 < w → Val.mul a (some c) nuw nsw = Val.shl a (some (BitVec.ofNat w k)) nuw nsw :=
  fun h => absurd (@h 8 (some 1#8) (BitVec.twoPow 8 8) 8 rfl false false (.inl rfl)) (by decide)

/-- `mul nsw i8 1, -128` is `-128`, and `shl nsw i8 1, 7` is poison. -/
theorem IRLean.Generic.mul_twoPow.drop_hs :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} {k : Nat}, c = BitVec.twoPow w k → k < w → ∀ (nuw nsw : Bool),
      Val.mul a (some c) nuw nsw = Val.shl a (some (BitVec.ofNat w k)) nuw nsw :=
  fun h => absurd (@h 8 (some 1#8) (BitVec.twoPow 8 7) 7 rfl (by decide) false true) (by decide)

theorem IRLean.Generic.mul_twoPow.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (k : Nat) (_ nsw : Bool),
      c = BitVec.twoPow w k ∧ k < w ∧ (nsw = false ∨ k + 1 < w) :=
  ⟨1, none, BitVec.twoPow 1 0, 0, false, false, rfl, Nat.one_pos, .inl rfl⟩

theorem IRLean.Generic.mul_twoPow_refines.drop_hc :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} {k : Nat}, k < w → ∀ (nuw nsw : Bool),
      Refines (Val.mul a (some c) nuw nsw)
        (Val.shl a (some (BitVec.ofNat w k)) nuw (nsw && decide (k + 1 < w))) :=
  fun h => not_refines 3#8 (by decide) (by decide) (@h 8 (some 1#8) 3#8 1 (by decide) false false)

theorem IRLean.Generic.mul_twoPow_refines.drop_hk :
    ¬ ∀ {w : Nat} (a : Val w) {c : BitVec w} {k : Nat}, c = BitVec.twoPow w k → ∀ (nuw nsw : Bool),
      Refines (Val.mul a (some c) nuw nsw)
        (Val.shl a (some (BitVec.ofNat w k)) nuw (nsw && decide (k + 1 < w))) :=
  fun h => not_refines 0#8 (by decide) (by decide) (@h 8 (some 1#8) (BitVec.twoPow 8 8) 8 rfl false false)

theorem IRLean.Generic.mul_twoPow_refines.sat :
    ∃ (w : Nat) (_ : Val w) (c : BitVec w) (k : Nat) (_ _ : Bool), c = BitVec.twoPow w k ∧ k < w :=
  ⟨1, none, BitVec.twoPow 1 0, 0, false, false, rfl, Nat.one_pos⟩

/-- At width zero, `1` is `0`, and dividing by it is undefined. -/
theorem IRLean.Generic.udiv_one.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (exact : Bool), Val.udiv a (some 1#w) exact = Outcome.ok a := fun h => by
  have := @h 0 (some 0#0) false
  rw [show Val.udiv (some 0#0) (some 1#0) false = Outcome.ub .divByZero from rfl] at this
  simp [Outcome.ub, Outcome.ok] at this

theorem IRLean.Generic.udiv_one.sat : ∃ (w : Nat) (_ : Val w) (_ : Bool), 0 < w := ⟨1, none, false, Nat.one_pos⟩

/-- In `i1`, `1` is `-1`, and dividing `-1` by it overflows, which is undefined. -/
theorem IRLean.Generic.sdiv_one.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (exact : Bool), Val.sdiv a (some 1#w) exact = Outcome.ok a := fun h => by
  have := @h 1 (some 1#1) false
  rw [show Val.sdiv (some 1#1) (some 1#1) false = Outcome.ub .divOverflow from rfl] at this
  simp [Outcome.ub, Outcome.ok] at this

theorem IRLean.Generic.sdiv_one.sat : ∃ (w : Nat) (_ : Val w) (_ : Bool), 1 < w := ⟨2, none, false, by decide⟩

/-! ### `IRLean.Generic.Bitwise` -/

/-- At width zero no shift amount is in range, so shifting by `0` is poison. -/
theorem IRLean.Generic.shl_zero.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (nuw nsw : Bool), Val.shl a (some 0#w) nuw nsw = a :=
  fun h => absurd (@h 0 (some 0#0) false false) (by decide)

theorem IRLean.Generic.shl_zero.sat : ∃ (w : Nat) (_ : Val w) (_ _ : Bool), 0 < w :=
  ⟨1, none, false, false, Nat.one_pos⟩

theorem IRLean.Generic.lshr_zero.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (exact : Bool), Val.lshr a (some 0#w) exact = a :=
  fun h => absurd (@h 0 (some 0#0) false) (by decide)

theorem IRLean.Generic.lshr_zero.sat : ∃ (w : Nat) (_ : Val w) (_ : Bool), 0 < w := ⟨1, none, false, Nat.one_pos⟩

theorem IRLean.Generic.ashr_zero.drop_hw :
    ¬ ∀ {w : Nat} (a : Val w) (exact : Bool), Val.ashr a (some 0#w) exact = a :=
  fun h => absurd (@h 0 (some 0#0) false) (by decide)

theorem IRLean.Generic.ashr_zero.sat : ∃ (w : Nat) (_ : Val w) (_ : Bool), 0 < w := ⟨1, none, false, Nat.one_pos⟩

end LemmaStore.Counter
