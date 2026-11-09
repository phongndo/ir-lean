import IRLean.Lanes
import IRLean.Refine

/-! Scalable vectors, `<vscale x N x iM>`, and `vscale`.

LangRef 23.1.3: "For scalable vectors, the total number of elements is a constant multiple (called vscale) of the
specified number of elements; vscale is a positive power-of-two integer that is unknown at compile time and the same
hardware-dependent constant for all scalable vectors at run time." And of `llvm.vscale`: "`vscale` is a positive
power-of-two integer that is constant throughout program execution, but is unknown at compile time."

So `vscale` is a fact about the machine, fixed for a whole run, and the same for every function in it. The model makes
it a parameter: a function in a module with scalable vectors, `llvm.vscale` or `vscale_range` takes a `VScale` first,
passes it to every function it calls, and a `<vscale x N x iM>` is a `Vec (vs.val * N) M`. `IRLean.Refines` then
quantifies over it as over any argument: for every `vscale`, the same one on both sides. It isn't a choice, through
`IRLean.Choice`: `Refines` lets the source choose after the target, so the source could pick another `vscale` than the
target's, and an optimizer can't assume that. docs/scalable-vectors.md has the decision and why.

`VScale` is `2 ^ log`, so every value of it is a positive power of two, and every positive power of two is one. -/

namespace IRLean

/-- `vscale`, as `2 ^ log`. -/
structure VScale where
  log : Nat
  deriving Repr, DecidableEq, Inhabited

namespace VScale

@[llvm] def val (vs : VScale) : Nat := 2 ^ vs.log

/-- `vscale_range(lo, hi)`, with `hi` 0 for no maximum. LangRef: it "indicates `vscale` is a power-of-two within a
specified range", and "Functions that don't include this attribute make no assumptions about the range of
`vscale`." A function that has it may assume it, so a run outside the range is undefined. It's an assumption the
function makes about the machine, so its reason is `assumeFailed`, as for `llvm.assume`. -/
@[llvm, inline] def range (lo hi : Nat) (vs : VScale) (k : Outcome α) : Outcome α :=
  if lo ≤ vs.val ∧ (hi = 0 ∨ vs.val ≤ hi) then k else Outcome.ub .assumeFailed

/-- `llvm.vscale.iW`. LangRef: "If the result value does not fit in the result type, then the result is a poison
value." -/
@[llvm] def value (w : Nat) (vs : VScale) : Val w :=
  if vs.val < 2 ^ w then some (BitVec.ofNat w vs.val) else none

end VScale

namespace Vec

/-- `llvm.stepvector`: lane `i` is `i`. LangRef: "If the sequence value exceeds the allowed limit for the element
type then the result for that lane is truncated." -/
@[llvm] def stepvector (n w : Nat) : Vec n w := Vector.ofFn fun i => some (BitVec.ofNat w i)

/-- `llvm.vector.reverse`: the lanes in reverse order. -/
@[llvm] def reverse (a : Vec n w) : Vec n w := Vector.ofFn fun i => a.lane (n - 1 - i)

/-- `llvm.vector.insert`: `b`'s lanes over `a`'s from lane `start`, which is the index times `vscale` when `b` is
scalable. LangRef: "Elements `idx` through (`idx` + num_elements(`subvec`) - 1) must be valid `vec` indices. If this
condition cannot be determined statically but is false at runtime, then the result vector is a poison value." -/
@[llvm] def insertSub (start : Nat) (a : Vec n w) (b : Vec m w) : Vec n w :=
  if start + m ≤ n then
    Vector.ofFn fun i => if start ≤ i.val ∧ i.val < start + m then b.lane (i.val - start) else a[i]
  else HasPoison.poison

/-- `llvm.vector.extract`: `k` lanes of `a` from lane `start`, which is the index times `vscale` when the result is
scalable, or poison if they aren't all lanes of `a`, as for `insertSub`. -/
@[llvm] def extractSub (k start : Nat) (a : Vec n w) : Vec k w :=
  if start + k ≤ n then Vector.ofFn fun i => a.lane (start + i.val) else HasPoison.poison

/-- `shufflevector` of a scalable vector with an all-zero mask, the only mask besides poison LLVM allows on one:
lane 0 in every lane of the result. -/
@[llvm] def splat0 (k : Nat) (a : Vec n w) : Vec k w := Vector.replicate k (a.lane 0)

end Vec

/-- Refinement of a function whose result type depends on its argument, such as one taking a `VScale`: for every
argument, the results are related. Below `IRLean.Refine`'s own instance for functions, so a function whose result
type doesn't depend on its argument gets that one, as it did before. -/
instance (priority := low) {α : Type} {β : α → Type} [∀ a, Refine (β a)] : Refine ((a : α) → β a) where
  le f g := ∀ a, Refine.le (f a) (g a)
  trans h₁ h₂ a := Refine.trans (h₁ a) (h₂ a)

theorem Refine.pi {α : Type} {β : α → Type} [∀ a, Refine (β a)] (f g : (a : α) → β a) :
    Refine.le f g ↔ ∀ a, Refine.le (f a) (g a) := Iff.rfl

end IRLean
