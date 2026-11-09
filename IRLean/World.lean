import IRLean.Basic
import IRLean.Refine

/-! # Calls outside the module

What a run does when it calls a function the module only declares, and what `IRLean.Refines` asks of two such runs.
[`docs/calls.md`](../docs/calls.md) has the design, and why.

The outside world is an input. A function that calls outside the module takes a `World`, how every such call answers,
and the `Trace` of calls with effects made before it, after its arguments and memory, and `Refines` quantifies over
both as it does over arguments: source and target face the same world.

- A call that accesses no memory answers from `World.pure`, given only the call. Which of its possible answers a run
  gets is the run's choice, as for a `freeze`: `IRLean.Choice` numbers both. It goes in no trace, except the one a run
  that ends by unwinding from it ends with.
- A run ends as an `Exit`: it returned, with its trace, or a call it made never came back, or unwound. Two runs refine
  only with equal traces.

A promise a callee breaks is undefined behavior, `UB.outsideCall`, as LangRef says: a `noreturn` callee that returns, a
`nounwind` one that unwinds, and one without effects that never comes back under `willreturn`. So is unwinding through
a function or call marked `nounwind`. -/

namespace IRLean

/-- A value crossing into or out of a call outside the module: each lane as a number, or `none` for poison. -/
abbrev Lanes := List (Option Nat)

namespace Lanes

/-- An integer, as one lane. -/
@[llvm] def ofVal (x : Val w) : Lanes := [x.map BitVec.toNat]

/-- A vector, lane by lane. -/
@[llvm] def ofVec (v : Vector (Val w) n) : Lanes := v.toList.map (·.map BitVec.toNat)

/-- A lane as a value of width `w`: the number modulo `2 ^ w`, so every value is some answer. -/
@[llvm] def lane (w : Nat) : Option Nat → Val w
  | some k => some (BitVec.ofNat w k)
  | none => none

/-- The first lane as an integer of width `w`, and poison if there isn't one. -/
@[llvm] def toVal (w : Nat) (l : Lanes) : Val w := lane w (l.getD 0 none)

/-- The first `n` lanes as a vector, each poison if it isn't there. -/
@[llvm] def toVec (n w : Nat) (l : Lanes) : Vector (Val w) n := Vector.ofFn fun i => lane w (l.getD i.val none)

end Lanes

/-- A call outside the module: the callee's name, and each argument's lanes. -/
structure Event where
  callee : String
  args : List Lanes
  deriving DecidableEq, Repr, Inhabited

/-- The calls with effects a run has made, newest first. -/
abbrev Trace := List Event

/-- How a call outside the module answers. -/
inductive Answer where
  /-- It returns these lanes, read as the call's type. -/
  | ret (v : Lanes)
  /-- The callee's run is undefined. -/
  | undefined
  /-- It never comes back: it runs forever, ends the program, or jumps out of the caller. -/
  | stays
  /-- It unwinds. -/
  | unwinds
  deriving DecidableEq, Repr, Inhabited

/-- How the outside world answers every call. -/
structure World where
  /-- A call with effects, given the trace that ends with it. -/
  effect : Trace → Answer
  /-- A call that only reads memory, given the trace before it, the call, and the run's choice among its answers. -/
  read : Trace → Event → Nat → Answer
  /-- A call that accesses no memory, given only the call, and the run's choice among its answers. -/
  pure : Event → Nat → Answer

instance : Inhabited World := ⟨⟨fun _ => .ret [], fun _ _ _ => .ret [], fun _ _ => .ret []⟩⟩

/-- How a run that calls outside the module ends, with the trace of calls it made. -/
inductive Exit (α : Type) where
  /-- It returned `v`. -/
  | done (v : α) (t : Trace)
  /-- The call at the head of `t` never came back. -/
  | halted (t : Trace)
  /-- The call at the head of `t` unwound, and so did this function. -/
  | unwound (t : Trace)
  deriving DecidableEq, Repr

/-- What the declaration and the call promise of a callee outside the module. Each is checked against its answer. -/
structure Promises where
  noreturn : Bool := false
  willreturn : Bool := false
  nounwind : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace World

/-- How a call without effects ends, given its answer: `e` is the call, and `t` the trace before it. A call that never
comes back never finishes, which `willreturn` makes undefined. One that unwinds ends the run, with the call added to
the trace so the run says which call it was. -/
@[llvm] def quiet (a : Answer) (t : Trace) (e : Event) (p : Promises) : Outcome (Exit Lanes) :=
  match a with
  | .ret v => if p.noreturn then Outcome.ub .outsideCall else Outcome.ok (.done v t)
  | .undefined => Outcome.ub .outsideCall
  | .stays => if p.willreturn then Outcome.ub .outsideCall else none
  | .unwinds => if p.nounwind then Outcome.ub .outsideCall else Outcome.ok (.unwound (e :: t))

/-- A call that accesses no memory, at the run's choice `i` among the callee's answers. -/
@[llvm] def callPure (w : World) (t : Trace) (e : Event) (i : Nat) (p : Promises) : Outcome (Exit Lanes) :=
  quiet (w.pure e i) t e p

end World

namespace Exit

/-- Runs `k` on what a call that may not come back returned, with the trace after it. A call that didn't come back
ends the run through `stop`, as the call did. Unwinding through a function marked `nounwind` is undefined. -/
@[llvm, inline] def bind (nounwind : Bool) (x : Outcome (Exit α)) (stop : Exit ρ → Outcome γ)
    (k : α → Trace → Outcome γ) : Outcome γ :=
  andThen x fun r => match r with
    | .done a t => k a t
    | .halted t => stop (.halted t)
    | .unwound t => if nounwind then Outcome.ub .outsideCall else stop (.unwound t)

/-- A run that makes no calls outside the module, as one that does: it returns the trace it was given. A refinement
relating it to one that does lifts it with this. -/
@[llvm] def lift (x : Outcome α) (t : Trace) : Outcome (Exit α) := andThen x fun a => Outcome.ok (.done a t)

end Exit

/-- Two ends of a run: the same trace, and results that refine, or the same call not coming back the same way. -/
instance [Refine α] : Refine (Exit α) where
  le a b := match a with
    | .done x t => ∃ y, b = .done y t ∧ Refine.le x y
    | .halted t => b = .halted t
    | .unwound t => b = .unwound t
  trans {a b c} hab hbc := by
    match a, hab with
    | .done _ _, ⟨_, hb, hxy⟩ =>
      subst hb
      obtain ⟨z, hc, hyz⟩ := hbc
      exact ⟨z, hc, Refine.trans hxy hyz⟩
    | .halted _, hb => subst hb; exact hbc
    | .unwound _, hb => subst hb; exact hbc

instance [Refine α] [Refine.Reflexive α] : Refine.Reflexive (Exit α) where
  refl
    | .done x _ => ⟨x, rfl, Refine.Reflexive.refl x⟩
    | .halted _ => rfl
    | .unwound _ => rfl

namespace Refine

theorem exit_done [Refine α] (x : α) (t : Trace) (b : Exit α) :
    Refine.le (Exit.done x t) b ↔ ∃ y, b = .done y t ∧ Refine.le x y := Iff.rfl

theorem exit_done_done [Refine α] (x y : α) (s t : Trace) :
    Refine.le (Exit.done x s) (Exit.done y t) ↔ s = t ∧ Refine.le x y :=
  ⟨fun ⟨_, h, hxy⟩ => by cases h; exact ⟨rfl, hxy⟩, fun ⟨h, hxy⟩ => ⟨y, h ▸ rfl, hxy⟩⟩

theorem exit_halted [Refine α] (t : Trace) (b : Exit α) : Refine.le (Exit.halted t : Exit α) b ↔ b = .halted t :=
  Iff.rfl

theorem exit_unwound [Refine α] (t : Trace) (b : Exit α) :
    Refine.le (Exit.unwound t : Exit α) b ↔ b = .unwound t := Iff.rfl

/-- Two runs that make no calls outside the module, lifted: refinement of the runs. -/
theorem exit_lift [Refine α] (a b : Outcome α) (t : Trace) :
    Refine.le (Exit.lift a t) (Exit.lift b t) ↔ Refine.le a b := by
  match a, b with
  | none, none => exact iff_of_true rfl rfl
  | none, some (.error _) => exact iff_of_false (fun h => nomatch h) (fun h => nomatch h)
  | none, some (.ok _) => exact iff_of_false (fun h => nomatch h) (fun h => nomatch h)
  | some (.error (.undefined _)), _ => exact iff_of_true trivial trivial
  | some (.error (.model _)), _ => exact iff_of_false id id
  | some (.ok _), none => exact iff_of_false (fun ⟨_, h, _⟩ => nomatch h) (fun ⟨_, h, _⟩ => nomatch h)
  | some (.ok _), some (.error _) =>
    exact iff_of_false (fun ⟨_, h, _⟩ => nomatch h) (fun ⟨_, h, _⟩ => nomatch h)
  | some (.ok x), some (.ok y) =>
    refine ⟨fun ⟨_, h, hxy⟩ => ?_, fun ⟨_, h, hxy⟩ => ?_⟩
    · cases h
      exact ⟨y, rfl, ((exit_done_done x y t t).1 hxy).2⟩
    · cases h
      exact ⟨.done y t, rfl, (exit_done_done x y t t).2 ⟨rfl, hxy⟩⟩

end Refine

section Monotone
open Lean.Order

variable {γ' : Sort _} [PartialOrder γ']

/-- Lean needs this to accept a recursive function whose recursive calls pass through `Exit.bind`. -/
@[partial_fixpoint_monotone]
theorem monotone_exit_bind (nounwind : Bool) (x : γ' → Outcome (Exit α)) (stop : γ' → Exit ρ → Outcome γ)
    (k : γ' → α → Trace → Outcome γ) (hx : monotone x) (hs : monotone stop) (hk : monotone k) :
    monotone fun g => Exit.bind nounwind (x g) (stop g) (k g) := by
  unfold Exit.bind
  refine monotone_andThen x _ hx ?_
  intro g g' h r
  cases r with
  | done a t => exact hk g g' h a t
  | halted t => exact hs g g' h _
  | unwound t =>
    cases nounwind
    · exact hs g g' h _
    · exact FlatOrder.rel.refl

end Monotone

end IRLean
