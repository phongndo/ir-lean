import Peephole.Term

/-! # What a fold asks an analysis, and what a sound answer means

Folds ask LLVM's analyses about their operands: `computeKnownBits`, `isKnownNonZero`, `isKnownToBeAPowerOfTwo`,
`ComputeNumSignBits`, `isGuaranteedNotToBePoison`, `isImpliedCondition` and others, in
`llvm/lib/Analysis/ValueTracking.cpp`. A model doesn't compute their answers. It takes them from an `Oracle`, and a
theorem about a fold holds for every oracle that's `Sound` in the run: each answer it gives is true of the values the
run gives the operands. LLVM's analyses being sound is [PASS-01](../../../../docs/llvm-verification-tasks.md), so a
fold's theorem rests on it, by name, as this hypothesis.

An answer is about an operand that isn't poison, as LLVM's are: `isKnownNonZero(V)` holds of a `V` that's poison too.
Analyses that use the context, such as assumptions and dominating conditions, give answers true at the instruction
being folded, which is the run `Sound` is about. -/

namespace Peephole

open IRLean

/-- Answers to the analyses folds ask, for every operand, at every width. -/
structure Oracle where
  /-- `computeKnownBits(V).Zero`: bits known to be 0. -/
  knownZero : {w : Nat} → Term w → BitVec w
  /-- `computeKnownBits(V).One`: bits known to be 1. -/
  knownOne : {w : Nat} → Term w → BitVec w
  /-- `isKnownNonZero(V)`. -/
  nonZero : {w : Nat} → Term w → Bool
  /-- `isKnownToBeAPowerOfTwo(V, OrZero)`. -/
  powerOfTwo : {w : Nat} → Bool → Term w → Bool
  /-- `ComputeNumSignBits(V)`: how many of the top bits are copies of the sign bit, at least 1. -/
  signBits : {w : Nat} → Term w → Nat
  /-- `isGuaranteedNotToBePoison(V)`. -/
  notPoison : {w : Nat} → Term w → Bool
  /-- `isKnownNonEqual(A, B)`. -/
  nonEqual : {w : Nat} → Term w → Term w → Bool
  /-- `isImpliedCondition(A, B, ...)`: `some true` if `B` is true whenever `A` is, `some false` if `B` is false
  whenever `A` is true. -/
  implies : Term 1 → Term 1 → Option Bool

/-- Every answer `o` gives is true in the run `ρ`. -/
structure Oracle.Sound (o : Oracle) (ρ : Env) : Prop where
  knownZero : ∀ {w} (t : Term w) (x : BitVec w), t.denote ρ = some x → x &&& o.knownZero t = 0#w
  knownOne : ∀ {w} (t : Term w) (x : BitVec w), t.denote ρ = some x → x &&& o.knownOne t = o.knownOne t
  nonZero : ∀ {w} (t : Term w) (x : BitVec w), o.nonZero t = true → t.denote ρ = some x → x ≠ 0#w
  powerOfTwo : ∀ {w} (orZero : Bool) (t : Term w) (x : BitVec w), o.powerOfTwo orZero t = true →
    t.denote ρ = some x → x.toNat.isPowerOfTwo ∨ (orZero = true ∧ x = 0#w)
  signBits : ∀ {w} (t : Term w) (x : BitVec w), t.denote ρ = some x →
    ∀ i, i < o.signBits t → i < w → x.getMsbD i = x.msb
  notPoison : ∀ {w} (t : Term w), o.notPoison t = true → t.denote ρ ≠ none
  nonEqual : ∀ {w} (a b : Term w) (x y : BitVec w), o.nonEqual a b = true →
    a.denote ρ = some x → b.denote ρ = some y → x ≠ y
  implies : ∀ (a b : Term 1) (r : Bool), o.implies a b = some r → a.denote ρ = some 1#1 →
    b.denote ρ = none ∨ b.denote ρ = some (BitVec.ofBool r)

/-- The oracle that knows nothing: no bit known, nothing proved. It's sound in every run, and models compare against
`opt` with it where an analysis has nothing to go on, as for function arguments. -/
def Oracle.none : Oracle where
  knownZero _ := 0#_
  knownOne _ := 0#_
  nonZero _ := false
  powerOfTwo _ _ := false
  signBits _ := 1
  notPoison _ := false
  nonEqual _ _ := false
  implies _ _ := Option.none

theorem Oracle.none_sound (ρ : Env) : Oracle.none.Sound ρ where
  knownZero _ _ _ := by simp [Oracle.none]
  knownOne _ _ _ := by simp [Oracle.none]
  nonZero _ _ h := by simp [Oracle.none] at h
  powerOfTwo _ _ _ h := by simp [Oracle.none] at h
  signBits _ x _ i hi _ := by
    simp only [Oracle.none, Nat.lt_one_iff] at hi
    subst hi
    simp [BitVec.msb_eq_getMsbD_zero]
  notPoison _ h := by simp [Oracle.none] at h
  nonEqual _ _ _ _ h := by simp [Oracle.none] at h
  implies _ _ _ h := by simp [Oracle.none] at h

end Peephole
