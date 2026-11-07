import IRLean.Attr
import Std.Tactic.BVDecide

/-! The shape every emitted function shares: values, outcomes, and the block driver. -/

namespace IRLean

/-- An LLVM integer of width `w`. `none` is poison. -/
abbrev Val (w : Nat) := Option (BitVec w)

/-- Why a run stopped with undefined behavior, as LLVM defines it. -/
inductive UB where
  | branchOnPoison
  | switchOnPoison
  | assumeFailed
  | unreachable
  | divByZero
  | divByPoison
  | divOverflow
  | noundefPoison
  | badAccess
  | misaligned
  | poisonPointer
  /-- A write to a constant, or to a stack object outside its lifetime. -/
  | writeToConstant
  | overlappingCopy
  /-- `free` of something `malloc` didn't return, or that's already freed. -/
  | badFree
  /-- A write that `readonly` or `memory(read)` rules out. -/
  | forbiddenWrite
  /-- An access through a `readnone` argument. -/
  | forbiddenAccess
  /-- An access through an argument whose function returned without capturing its provenance. -/
  | expiredProvenance
  /-- `free` through a `nofree` argument. -/
  | forbiddenFree
  deriving Repr, DecidableEq, Inhabited

/-- Why the model stopped instead of choosing an answer. These aren't undefined in LLVM, or LLVM's rules
for them are unsettled, so a proof of `.ok` still holds in LLVM, but a proof that one of these happens
says nothing about LLVM. -/
inductive ModelStop where
  /-- `freeze` of poison picks an arbitrary value. -/
  | freezePoison
  /-- `strlen` of a string with an uninitialized byte before its end. -/
  | readUninit
  /-- Reading a stored pointer as an integer, or a partial or misaligned pointer. -/
  | pointerBytes
  /-- A call through a pointer to no function this module defines with the call's signature. -/
  | unknownCallee
  /-- `llvm.assume` with a bundle about poison, which LangRef doesn't settle. -/
  | assumeOnPoison
  /-- An access `memory(...)` lists as `none`. LLVM only rules out accesses observed from outside the
  function, and the model can't tell whether this one is. -/
  | unobservableAccess
  /-- A look at an address `captures` left out. LLVM only rules out a look that changes what's observed,
  which depends on what other addresses would have done. -/
  | addressObserved
  /-- A function returning something other than its `returned` argument. LangRef says it always returns
  that argument, but not what happens if it doesn't. -/
  | returnedDiffers
  /-- A `noalias` result that isn't new in this call. LLVM only rules out storage the caller can reach,
  and the model can't tell whether it can. -/
  | noaliasResult
  /-- A call to a function outside the module that promises not to return, such as an abort. What it does isn't
  modeled, only that the code after it doesn't run. -/
  | noReturnCall
  deriving Repr, DecidableEq, Inhabited

/-- Why a run ended without a result. -/
inductive Stop where
  | undefined (reason : UB)
  | model (reason : ModelStop)
  deriving Repr, DecidableEq, Inhabited

/-- What running code does. The outer `none` means it never finishes. -/
abbrev Outcome (α : Type) := Option (Except Stop α)

namespace Outcome
@[llvm] def ok (x : α) : Outcome α := some (.ok x)
@[llvm] def ub (reason : UB) : Outcome α := some (.error (.undefined reason))
@[llvm] def stop (reason : ModelStop) : Outcome α := some (.error (.model reason))
end Outcome

/-- Runs `k` on the result of `x`, stopping if `x` stopped or never finishes. -/
@[llvm, inline] def andThen (x : Outcome α) (k : α → Outcome β) : Outcome β :=
  match x with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok a) => k a

/-- Reads an `i1` from a comparison back as the condition it came from. -/
@[llvm, simp] theorem ofBool_eq_one (b : Bool) : (BitVec.ofBool b = 1#1) = (b = true) := by
  cases b <;> decide

/-- What a basic block does last. -/
inductive Next (β ρ : Type) where
  | jump (next : β)
  | ret (value : ρ)

/-- Runs blocks until one returns. Blocks are data, so this is the only recursive function an
emitted non-recursive LLVM function needs. -/
def run (step : β → Outcome (Next β ρ)) (b : β) : Outcome ρ :=
  match step b with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok (.ret r)) => some (.ok r)
  | some (.ok (.jump next)) => run step next
partial_fixpoint

@[llvm] def jump (b : β) : Outcome (Next β ρ) := Outcome.ok (.jump b)

@[llvm] def ret (v : ρ) : Outcome (Next β ρ) := Outcome.ok (.ret v)

@[llvm] def unreachable : Outcome α := Outcome.ub .unreachable

/-- Branching on poison is undefined behavior. -/
@[llvm] def br (c : Val 1) (t e : β) : Outcome (Next β ρ) :=
  match c with
  | none => Outcome.ub .branchOnPoison
  | some b => jump (if b == 1#1 then t else e)

/-- Switching on poison is undefined behavior. `k` chooses the block from the value. -/
@[llvm] def sw (x : Val w) (k : BitVec w → Outcome α) : Outcome α :=
  match x with
  | none => Outcome.ub .switchOnPoison
  | some v => k v

/-- `llvm.assume`: anything other than true is undefined behavior. -/
@[llvm, inline] def assume (c : Val 1) (k : Outcome α) : Outcome α :=
  match c with
  | some b => if b == 1#1 then k else Outcome.ub .assumeFailed
  | none => Outcome.ub .assumeFailed

/-- The `noundef` attribute: a poison value here is undefined behavior. -/
@[llvm, inline] def noundef {τ : Type} (x : Option τ) (k : Outcome α) : Outcome α :=
  match x with
  | none => Outcome.ub .noundefPoison
  | some _ => k

/-- A call through a pointer: `k` picks the function. -/
@[llvm] def indirect {τ : Type} (p : Option τ) (k : τ → Outcome α) : Outcome α :=
  match p with
  | none => Outcome.ub .poisonPointer
  | some q => k q

/-- A branch whose arms are already computations, for recursive functions, where a block calls the
next one directly instead of returning it to the driver. -/
@[llvm, inline] def branch (c : Val 1) (t e : Outcome α) : Outcome α :=
  match c with
  | none => Outcome.ub .branchOnPoison
  | some b => if b == 1#1 then t else e

section Monotone
open Lean.Order

/-! Lean needs these to accept a recursive function whose recursive calls pass through the helpers
above. -/

variable {γ : Sort _} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem monotone_andThen (x : γ → Outcome α) (k : γ → α → Outcome β)
    (hx : monotone x) (hk : monotone k) : monotone fun g => andThen (x g) (k g) := by
  intro g g' h
  have h1 := hx g g' h
  have h2 := hk g g' h
  simp only [andThen]
  revert h1
  generalize x g = a
  generalize x g' = b
  intro h1
  cases h1 with
  | bot => exact FlatOrder.rel.bot
  | refl =>
    split
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl
    · exact h2 _

@[partial_fixpoint_monotone]
theorem monotone_branch (c : Val 1) (t e : γ → Outcome α)
    (ht : monotone t) (he : monotone e) : monotone fun g => branch c (t g) (e g) := by
  intro g g' h
  simp only [branch]
  split
  · exact FlatOrder.rel.refl
  · split
    · exact ht g g' h
    · exact he g g' h

@[partial_fixpoint_monotone]
theorem monotone_sw (x : Val w) (k : γ → BitVec w → Outcome α)
    (hk : monotone k) : monotone fun g => sw x (k g) := by
  intro g g' h
  simp only [sw]
  split
  · exact FlatOrder.rel.refl
  · exact hk g g' h _

@[partial_fixpoint_monotone]
theorem monotone_assume (c : Val 1) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => assume c (k g) := by
  intro g g' h
  simp only [assume]
  split
  · split
    · exact hk g g' h
    · exact FlatOrder.rel.refl
  · exact FlatOrder.rel.refl

@[partial_fixpoint_monotone]
theorem monotone_noundef {τ : Type} (x : Option τ) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => noundef x (k g) := by
  intro g g' h
  simp only [noundef]
  split
  · exact FlatOrder.rel.refl
  · exact hk g g' h

@[partial_fixpoint_monotone]
theorem monotone_indirect {τ : Type} (p : Option τ) (k : γ → τ → Outcome α)
    (hk : monotone k) : monotone fun g => indirect p (k g) := by
  intro g g' h
  simp only [indirect]
  split
  · exact FlatOrder.rel.refl
  · exact hk g g' h _

end Monotone

/-- Types that have a poison value: integers, and tuples of them for LLVM structs. -/
class HasPoison (α : Type) where
  poison : α

instance : HasPoison (Option τ) := ⟨none⟩
instance : HasPoison Unit := ⟨()⟩
instance [HasPoison α] [HasPoison β] : HasPoison (α × β) := ⟨HasPoison.poison, HasPoison.poison⟩

/-- `select`: a poison condition gives poison, and only the chosen arm matters. -/
@[llvm] def select [HasPoison α] (c : Val 1) (t e : α) : α :=
  match c with
  | none => HasPoison.poison
  | some b => if b == 1#1 then t else e

end IRLean
