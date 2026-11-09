import Peephole.Term

/-! # A fold, as the steps the C++ takes

A fold function tries its rewrites in order and stops at the first that applies. A model here writes it the same way:
a list of `Step`s, one for each statement in the C++ that can end the function, in the C++'s order. Each step falls
through, fires a rewrite, declines the whole fold, as a `return nullptr` in the middle does, or hands over to code the
model doesn't follow. `run` takes the first step that doesn't fall through.

A step that fires names its site, by the ID [`tests/llvm_scope/rewrites`](../../../llvm_scope/rewrites) gives it, so a
rewrite's proof is about one step: `run_sound` puts a fold's theorem together from a theorem for each step that fires.
A step's theorem may assume every step before it fell through, as the C++'s order lets it. -/

namespace Peephole

/-- What a fold answers. -/
inductive Result (w : Nat) where
  /-- Replace the instruction with this. -/
  | value (r : Repl w)
  /-- No change: `nullptr`, or `false`. -/
  | null
  /-- Whatever `callee` answers, which the model doesn't say. Nothing is claimed about it. -/
  | delegated (callee : String)
  deriving Inhabited

/-- One statement that can end a fold. -/
inductive Step (w : Nat) where
  | next
  /-- The rewrite at this site: the instruction is replaced with `r`. -/
  | fire (site : String) (r : Repl w)
  | decline
  | delegate (callee : String)

variable {w : Nat}

/-- The first step that doesn't fall through. -/
def run : List (Step w) → Result w
  | [] => .null
  | .next :: rest => run rest
  | .fire _ r :: _ => .value r
  | .decline :: _ => .null
  | .delegate c :: _ => .delegated c

/-- When a fold answers `r`, one step fired `r`, and every step before it fell through. -/
theorem run_value {steps : List (Step w)} {r : Repl w} (h : run steps = .value r) :
    ∃ pre site post, steps = pre ++ Step.fire site r :: post ∧ ∀ s ∈ pre, s = .next := by
  induction steps with
  | nil => simp [run] at h
  | cons s rest ih =>
    cases s with
    | next =>
      obtain ⟨pre, site, post, h1, h2⟩ := ih h
      exact ⟨.next :: pre, site, post, by simp [h1], by simpa using h2⟩
    | fire site r' =>
      simp only [run, Result.value.injEq] at h
      subst h
      exact ⟨[], site, rest, rfl, by simp⟩
    | decline => simp [run] at h
    | delegate c => simp [run] at h

/-- A fold's answer has `P` if every step that fires does. -/
theorem run_sound {P : Repl w → Prop} {steps : List (Step w)}
    (h : ∀ site r, Step.fire site r ∈ steps → P r) {r : Repl w} (hr : run steps = .value r) : P r := by
  obtain ⟨pre, site, post, h1, -⟩ := run_value hr
  exact h site r (by simp [h1])

/-- As `run_sound`, where a step's theorem may assume the steps before it fell through. -/
theorem run_sound_ordered {P : Repl w → Prop} {steps : List (Step w)}
    (h : ∀ pre site r post, steps = pre ++ Step.fire site r :: post → (∀ s ∈ pre, s = .next) → P r) {r : Repl w}
    (hr : run steps = .value r) : P r := by
  obtain ⟨pre, site, post, h1, h2⟩ := run_value hr
  exact h pre site r post h1 h2

/-- The site a fold's answer came from: what the comparison with `opt` reports. -/
def firedSite : List (Step w) → Option String
  | [] => none
  | .next :: rest => firedSite rest
  | .fire s _ :: _ => some s
  | _ :: _ => none

end Peephole
