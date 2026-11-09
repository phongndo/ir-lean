import LemmaStore
import LemmaStore.Normal
import Lean.LibrarySuggestions.Default

/-! # Finding a stored lemma

Retrieval, exact first:

1. **By key.** The statement's key, from `LemmaStore.Normal`, against each stored lemma's, with an equation or an
   equivalence also tried the other way round.
2. **By the conclusion's shape.** A `DiscrTree` over the stored lemmas' conclusions, as `simp`, `exact?` and `rw?`
   index lemmas, then unification. A lemma whose conclusion becomes the goal is a match, with its hypotheses,
   instantiated, left as side conditions. That's how a constant the lemma lifts into a hypothesis, such as `mul_twoPow`'s
   `c = BitVec.twoPow w k`, matches a goal with `8#32`, leaving `8#32 = BitVec.twoPow 32 3` to prove.
3. **Lean's own premise selection.** `selector` puts the store's matches first and the default selector's after them,
   and is registered with `@[library_suggestions]`, so importing this module lets `grind +suggestions`,
   `simp? +suggestions` and `try?` see the store with no new tactic.

Nothing here is trusted. A match only says what to try: a proof that uses it is checked by the kernel like any other. -/

open Lean Meta

namespace LemmaStore

/-- A stored lemma that applies to a goal. -/
structure Match where
  name : Name
  /-- `exact`: the same statement, by key. `instance`: the lemma's conclusion, instantiated, is the goal's. -/
  tier : String
  /-- Whether the goal is the lemma's equation or equivalence the other way round. -/
  reversed : Bool := false
  /-- The lemma's hypotheses, instantiated, that a use has to prove. -/
  sideConditions : Array Expr := #[]
  /-- Whether `decide` closes each side condition, which needs it to have no free variables. -/
  decided : Array Bool := #[]
  /-- How many of the lemma's variables the goal leaves free. -/
  unassigned : Nat := 0

/-- The stored lemmas' conclusions, indexed by shape. -/
def tree (names : Array Name) : MetaM (DiscrTree Name) := do
  let mut t := DiscrTree.empty
  for n in names do
    let info ← getConstInfo n
    let type ← instantiateTypeLevelParams info.toConstantVal (← mkFreshLevelMVarsFor info)
    let (_, _, concl) ← forallMetaTelescope type
    t ← t.insert concl n
  return t

/-- An equation's or equivalence's sides swapped. -/
def swapSides (e : Expr) : Option Expr :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Eq us, #[α, a, b] => some (mkApp3 (.const ``Eq us) α b a)
  | .const ``Iff [], #[a, b] => some (mkApp2 (.const ``Iff []) b a)
  | _, _ => none

/-- Whether `decide` proves `p`: it has no free variables or metavariables, and its `Decidable` instance evaluates to
`true`. -/
def decides (p : Expr) : MetaM Bool := do
  if p.hasFVar || p.hasMVar then return false
  try
    let d ← mkDecide p
    let r ← withAtLeastTransparency .default <| whnf d
    return r.isConstOf ``true
  catch _ => return false

/-- `n` applied to `goal`, if its conclusion unifies with it, and what's left to prove. `goal` may mention the free
variables of the local context, and a side condition that's one of its hypotheses isn't left. -/
def instantiate? (n : Name) (goal : Expr) (reversed : Bool) : MetaM (Option Match) := do
  let info ← getConstInfo n
  let type ← instantiateTypeLevelParams info.toConstantVal (← mkFreshLevelMVarsFor info)
  let (ms, bis, concl) ← forallMetaTelescope type
  let some concl := if reversed then swapSides concl else some concl | return none
  unless ← withReducible (isDefEq concl goal) do return none
  let mut side := #[]
  let mut decided := #[]
  let mut unassigned := 0
  for m in ms, bi in bis do
    if ← m.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType m)
    if bi.isInstImplicit then
      if let some inst ← synthInstance? t then
        if ← isDefEq m inst then continue
    if ← isProp t then
      if (← findLocalDeclWithType? t).isSome then continue
      side := side.push t
      decided := decided.push (← decides t)
    else
      unassigned := unassigned + 1
  return some { name := n, tier := "instance", reversed, sideConditions := side, decided, unassigned }

/-- The stored lemmas among `names` whose conclusion, instantiated, is `goal`, either way round. -/
def instances (names : Array Name) (goal : Expr) : MetaM (Array Match) := do
  let t ← tree names
  let mut out := #[]
  for reversed in [false, true] do
    let some g := if reversed then swapSides goal else some goal | continue
    for n in ← t.getMatch g do
      if out.any (·.name == n) then continue
      if let some m ← withoutModifyingState (instantiate? n goal reversed) then out := out.push m
  return out

/-- A goal's matches in the store, for `selector`: lemmas whose conclusion becomes the goal, those with no side
conditions left first. -/
def suggest (goal : MVarId) : MetaM (Array Name) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let ms ← instances catalog target
  let (closed, open_) := ms.partition fun m => m.unassigned == 0 && m.decided.all id
  return (closed ++ open_).map (·.name)

open LibrarySuggestions in
/-- The store's matches first, then what Lean's default selector suggests. -/
@[library_suggestions]
def selector : Selector := fun g c => do
  let mine ← suggest g
  let mine ← mine.filterM c.filter
  let rest ← (sineQuaNonSelector.filterGrindAnnotated.intersperse currentFile) g c
  let rest := rest.filter fun s => !mine.contains s.name
  let mine : Array Suggestion := mine.map fun n => { name := n, score := 1.0 }
  return (mine ++ rest).take c.maxSuggestions

end LemmaStore
