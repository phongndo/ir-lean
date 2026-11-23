import IRLean
import Lean.Elab.Tactic

/-! From slices that are equal to a whole function, where the rest of the two functions is the same text.

`IRLean/Cut.lean`'s lemma between blocks, `Outcome.Sim.run`, and `IRLean/CutPromised.lean`'s for a run under a promise,
`Outcome.Sim.promised`, ask that related blocks step to related blocks. Here two blocks are related when they have the
same name and the same fields, memory included, and what two runs return is related when it's equal. So a block that's
the same code on both sides needs no fact about any operation, `IRLean/Mono.lean`'s included: `sim_same` walks it and
gives each instruction's result one name for both sides. Inside a cut the two sides differ. There `cut_store` writes
what each side stores as an expression of the values that enter the cut, and replaces the target's by the source's with
the proof that the two slices are equal. `call_same` steps over a call of a function that has such a theorem of its
own.

Nothing here is about one kernel. What it covers: cuts whose slices are equal, not only refined, and whose results
leave through `store`s of vectors in the cut's block, and the three checks in `checks`. -/

open Lean Meta Elab Tactic

namespace IRLean.Whole

/-- The same instruction on both sides, and then code related on what it gives. -/
theorem andThen_same (α β β' : Type) (s : β → β' → Prop) (x : Outcome α) (k : α → Outcome β) (k' : α → Outcome β')
    (hk : ∀ a, Outcome.Sim s (k a) (k' a)) : Outcome.Sim s (andThen x k) (andThen x k') :=
  Outcome.Sim.andThen (r := Eq) (Outcome.Sim.refl (fun _ => rfl) x) fun a b h => by subst h; exact hk a

/-- A store of what a cut gives, and the same store of an equal value. -/
theorem andThen_storeVec_cut {n w : Nat} {β β' : Type} {s : β → β' → Prop} {m : Mem} {p : PtrVal} {a : Nat}
    {x x' : Vec n w} {k : Mem → Outcome β} {k' : Mem → Outcome β'} (h : x' = x)
    (hk : ∀ m', Outcome.Sim s (k m') (k' m')) :
    Outcome.Sim s (andThen (Mem.storeVec m p x a) k) (andThen (Mem.storeVec m p x' a) k') := by
  subst h; exact andThen_same _ _ _ _ _ _ _ hk

/-- Two slices of one block each, with equal runs, return equal values. -/
theorem ret_eq_of_run_eq {β β' ρ : Type} {step : β → Outcome (Next β ρ)} {step' : β' → Outcome (Next β' ρ)} {b : β}
    {b' : β'} {x x' : ρ} (hs : step b = ret x) (ht : step' b' = ret x') (h : run step' b' = run step b) : x' = x := by
  rw [run_ret _ hs, run_ret _ ht] at h
  simpa [Outcome.ok] using h

/-- Blocks that are the same block return the same thing, and jump to the same block. -/
theorem jump_same {β β' ρ : Type} {f : β → β'} {b : β} {b' : β'} (h : f b = b') :
    Outcome.Sim (Next.Rel (fun x y => f x = y) (@Eq ρ)) (jump b) (jump b') := Outcome.Sim.jump h

theorem ret_same {β β' ρ : Type} {f : β → β'} (x : ρ) :
    Outcome.Sim (Next.Rel (fun x y => f x = y) (@Eq ρ)) (ret x : Outcome (Next β ρ)) (ret x) := Outcome.Sim.ret rfl

theorem br_same {β β' ρ : Type} {f : β → β'} (c : Val 1) {t e : β} {t' e' : β'} (ht : f t = t') (he : f e = e') :
    Outcome.Sim (Next.Rel (fun x y => f x = y) (@Eq ρ)) (br c t e) (br c t' e') :=
  Outcome.Sim.br (Refine.refl_val c) ht he

/-- A call of the source's function and the same call of the target's, where the target's function does what the
source's does, and then code related on what the call gives. -/
theorem andThen_sim_eq {α β β' : Type} {s : β → β' → Prop} {x x' : Outcome α} {k : α → Outcome β}
    {k' : α → Outcome β'} (hx : Outcome.Sim Eq x x') (hk : ∀ a, Outcome.Sim s (k a) (k' a)) :
    Outcome.Sim s (andThen x k) (andThen x' k') :=
  Outcome.Sim.andThen hx fun a b h => by subst h; exact hk a

/-! The same check on both sides, before code that's related. A check goes on to the code after it, or is undefined or
stops the model whatever that code is. -/

theorem noundef_same {α β τ : Type} (s : α → β → Prop) (x : Option τ) (k : Outcome α) (k' : Outcome β)
    (h : Outcome.Sim s k k') : Outcome.Sim s (noundef x k) (noundef x k') := by
  cases x with
  | none => exact trivial
  | some _ => exact h

theorem dereferenceable_same {α β : Type} (s : α → β → Prop) (m : Mem) (p : PtrVal) (n : Nat) (k : Outcome α)
    (k' : Outcome β) (h : Outcome.Sim s k k') :
    Outcome.Sim s (Mem.dereferenceable m p n k) (Mem.dereferenceable m p n k') := by
  unfold Mem.dereferenceable
  cases m.access p n 1 with
  | error e => exact trivial
  | ok _ => exact h

theorem observeAddress_same {α β : Type} (s : α → β → Prop) (p : PtrVal) (c : Bool) (k : Outcome α)
    (k' : Outcome β) (h : Outcome.Sim s k k') :
    Outcome.Sim s (Mem.observeAddress p c k) (Mem.observeAddress p c k') := by
  cases p with
  | none => exact h
  | some q =>
    show Outcome.Sim s
      (if q.tags.any (fun t => t.noAddress && !(c && t.nullCheck)) then Outcome.stop .addressObserved else k)
      (if q.tags.any (fun t => t.noAddress && !(c && t.nullCheck)) then Outcome.stop .addressObserved else k')
    cases q.tags.any (fun t => t.noAddress && !(c && t.nullCheck)) with
    | true => exact trivial
    | false => exact h

/-- The checks `walk` steps over: the check, its lemma above, and how many arguments it has after its types, the code
after it last. -/
private def checks : List (Name × Name × Nat) :=
  [(``IRLean.noundef, ``noundef_same, 2), (``Mem.dereferenceable, ``dereferenceable_same, 4),
    (``Mem.observeAddress, ``observeAddress_same, 3)]

/-- `e` with the `let`s at its head replaced by their values. -/
private partial def zetaHead (e : Expr) : Expr :=
  match e.headBeta with
  | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
  | .mdata _ e => zetaHead e
  | e => e

/-- `e` with each proof the elaborator took out of a definition as a theorem of its own, `f._proof_N`, put back. Two
translations of the same instruction name these apart, `Base.f.step._proof_3` and `Cand.f.step._proof_3`: a vector
constant's proof that it has its length is one. With them put back the two are the same term. -/
private def inlineProofs (e : Expr) : CoreM Expr := do
  let env ← getEnv
  return e.replace fun e =>
    match e with
    | .const (.str p s) ls =>
      if s.startsWith "_proof_" then
        match env.find? (.str p s) with
        | some (.thmInfo t) => some (t.value.instantiateLevelParams t.levelParams ls)
        | _ => none
      else none
    | _ => none

/-- A block's `step` at a block, unfolded to the block's code, with its `let`s kept. -/
private def unfoldStep (e : Expr) : MetaM Expr := do
  let some e ← unfoldDefinition? e | return e
  inlineProofs (← withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e))

/-- The parts of a goal `Outcome.Sim r a b`: the relation with its types, as a function of the two runs, and the
runs. -/
private def simGoal (g : MVarId) (who : String) : MetaM ((Expr → Expr → Expr) × Array Expr) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Outcome.Sim 5 do throwError "{who}: the goal isn't an Outcome.Sim"
  let args := t.getAppArgs
  return (fun a b => mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, a, b], args)

/-- The code after an instruction, as a function of what the instruction gives, with the bound variable loose. -/
private def bodyOf (k : Expr) : Expr :=
  if k.isLambda then k.bindingBody! else mkApp (k.liftLooseBVars 0 1) (mkBVar 0)

/-- Walks a goal `Outcome.Sim r a b` while `a` and `b` start with the same instruction. A `let` of the same value on
both sides becomes one variable for both, with the `let`'s name and no value, and an `andThen` of the same run one
variable for what it returns. With `zeta`, `let`s are replaced by their values on each side instead, the two sides
needn't have the same ones, and only an `andThen` of the same run is stepped over. A check that's the same on both sides
is stepped over too. Stops where the two differ, or at a block's last instruction, and returns that goal. -/
partial def walk (g : MVarId) (zeta : Bool) : MetaM MVarId := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Outcome.Sim 5 do return g
  let args := t.getAppArgs
  let mk (a b : Expr) : Expr := mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, a, b]
  let lhs := if zeta then zetaHead args[3]! else args[3]!.headBeta
  let rhs := if zeta then zetaHead args[4]! else args[4]!.headBeta
  match lhs, rhs with
  | .letE n ty v b _, .letE _ ty' v' b' _ =>
    -- Not reached with `zeta`.
    unless v == v' && ty == ty' do return g
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkForall n .default ty (mk b b')) (← g.getTag)
    g.assign (mkApp g' v)
    let (_, g'') ← g'.mvarId!.intro n
    walk g'' zeta
  | _, _ =>
    if lhs.isAppOfArity ``IRLean.andThen 4 && rhs.isAppOfArity ``IRLean.andThen 4 &&
        lhs.appFn!.appArg! == rhs.appFn!.appArg! then
      let α := lhs.getAppArgs[0]!
      let k := lhs.appArg!
      let k' := rhs.appArg!
      let n := if k.isLambda then k.bindingName! else `a
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkForall n .default α (mk (bodyOf k) (bodyOf k'))) (← g.getTag)
      g.assign (mkAppN (mkConst ``andThen_same) #[α, args[0]!, args[1]!, args[2]!, lhs.appFn!.appArg!, k, k', g'])
      let (_, g'') ← g'.mvarId!.intro n
      walk g'' zeta
    else if let some (_, lemma, n) := checks.find? fun c => lhs.isAppOf c.1 && rhs.isAppOf c.1 then
      let la := lhs.getAppArgs
      let ra := rhs.getAppArgs
      unless la.size == ra.size && n ≤ la.size &&
          (List.range (n - 1)).all (fun i => la[la.size - n + i]! == ra[la.size - n + i]!) do
        return g
      let g' ← mkFreshExprSyntheticOpaqueMVar (mk la.back! ra.back!) (← g.getTag)
      g.assign (← mkAppM lemma (#[args[2]!] ++ la.extract (la.size - n) (la.size - 1) ++ #[la.back!, ra.back!, g']))
      walk g'.mvarId! zeta
    else
      -- A `match` on what an instruction gives, a pair for one, reduces once that has a name.
      let reduce (e : Expr) : MetaM Expr :=
        withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e)
      let lhs' ← reduce lhs
      let rhs' ← reduce rhs
      if lhs' != lhs || rhs' != rhs then
        walk (← g.replaceTargetDefEq (mk lhs' rhs')) zeta
      else if zeta && (lhs != args[3]! || rhs != args[4]!) then
        g.replaceTargetDefEq (mk lhs rhs)
      else
        return g

/-- Unfolds the two blocks' `step`s of a goal `Outcome.Sim r (step b) (step' b')` to the blocks' code. -/
elab "sim_unfold" : tactic => liftMetaTactic1 fun g => g.withContext do
  let (mk, args) ← simGoal g "sim_unfold"
  g.replaceTargetDefEq (mk (← unfoldStep args[3]!) (← unfoldStep args[4]!))

/-- Steps over the code that's the same on both sides of a goal `Outcome.Sim r a b`, naming each instruction's result
once for both, and stops at the first instruction that differs or at the block's last. -/
elab "sim_same" : tactic => liftMetaTactic1 fun g => walk g false

/-- Replaces the `let`s at the head of both sides of a goal `Outcome.Sim r a b` by their values, and steps over runs
that are then the same. -/
elab "sim_zeta" : tactic => liftMetaTactic1 fun g => walk g true

/-- Closes a goal about two blocks' last instruction, the same on both sides. -/
macro "sim_end" : tactic =>
  `(tactic| first
    | exact jump_same rfl
    | exact br_same _ rfl rfl
    | exact ret_same _)

/-- Checks that the walk stopped at the `let` of `n` on both sides, the first instruction of a cut. Where the two
sides differ before it, the proof stops here and says where. -/
elab "sim_at " n:ident : tactic => withMainContext do
  let (_, args) ← simGoal (← getMainGoal) "sim_at"
  let at_ (e : Expr) : MessageData :=
    match e.headBeta with
    | .letE x .. => m!"the `let` of {x}"
    | e => m!"{e.getAppFn}"
  match args[3]!.headBeta, args[4]!.headBeta with
  | .letE x .., .letE y .. =>
    unless x == n.getId && y == n.getId do
      throwError "sim_at: the two sides differ before the cut, which starts at {n.getId}: at the `let` of {x}"
  | l, r => throwError "sim_at: the two sides differ before the cut, which starts at {n.getId}: at {at_ l} and {at_ r}"

/-- At a call of a function whose two versions `h` relates: `h a b c m` says the target's does what the source's does,
for every argument. Steps over the call. -/
macro "call_same " h:term:max : tactic => `(tactic| refine andThen_sim_eq ($h ..) fun a => ?_)

/-- At a cut's store. `cut_store h (srcStep block) (tgtStep block)` replaces the value the target stores by the one the
source stores, where the source's value is what the slice `srcStep` returns from `block`, the target's what `tgtStep`
does, and `h` says the two slices' runs from `block` are equal. Each side's value has to be its slice's, to the
letter, once the `let`s of both are replaced by their values: nothing is unfolded to compare them, so a store of
anything else stops here, at once, with which side it is. -/
elab "cut_store " h:term:max ppSpace s:term:max ppSpace t:term:max : tactic => withMainContext do
  let g ← walk (← getMainGoal) true
  g.withContext do
  let (mk, args) ← simGoal g "cut_store"
  let lhs := args[3]!
  let rhs := args[4]!
  unless lhs.isAppOfArity ``IRLean.andThen 4 && rhs.isAppOfArity ``IRLean.andThen 4 do
    throwError "cut_store: the two sides aren't at an instruction that can be undefined"
  let store := lhs.appFn!.appArg!
  let store' := rhs.appFn!.appArg!
  unless store.isAppOfArity ``Mem.storeVec 6 && store'.isAppOfArity ``Mem.storeVec 6 do
    throwError "cut_store: the two sides aren't at a store of a vector"
  let sa := store.getAppArgs
  let sa' := store'.getAppArgs
  unless sa[0]! == sa'[0]! && sa[1]! == sa'[1]! && sa[2]! == sa'[2]! && sa[3]! == sa'[3]! && sa[5]! == sa'[5]! do
    throwError "cut_store: the two sides store to different places, or in different memories"
  -- What a slice returns from the block it's given, and the proof that its `step` there is that.
  let slice (stx : Syntax) (stored : Expr) (side : String) : TacticM (Expr × Expr × Expr) := do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize stx none)
    let u := zetaHead (← unfoldStep e)
    unless u.isAppOfArity ``IRLean.ret 3 do throwError "cut_store: the {side}'s slice isn't one block that returns"
    unless u.appArg! == stored do
      throwError "cut_store: the {side} doesn't store what its slice returns: {stx}"
    return (e.appFn!, e.appArg!, ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e u))
  let (step, b, hs) ← slice s sa[4]! "source"
  let (step', b', ht) ← slice t sa'[4]! "target"
  let ρ ← inferType sa[4]!
  let hr ← Term.elabTermEnsuringType h (← mkEq (← mkAppM ``IRLean.run #[step', b']) (← mkAppM ``IRLean.run #[step, b]))
  Term.synthesizeSyntheticMVarsNoPostponing
  let hr ← instantiateMVars hr
  let heq := mkAppN (mkConst ``ret_eq_of_run_eq)
    #[← inferType b, ← inferType b', ρ, step, step', b, b', sa[4]!, sa'[4]!, hs, ht, hr]
  let k := lhs.appArg!
  let k' := rhs.appArg!
  let n := if k.isLambda then k.bindingName! else `m
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkForall n .default (mkConst ``Mem) (mk (bodyOf k) (bodyOf k'))) (← g.getTag)
  g.assign (mkAppN (mkConst ``andThen_storeVec_cut)
    #[sa[0]!, sa[1]!, args[0]!, args[1]!, args[2]!, sa[2]!, sa[3]!, sa[5]!, sa[4]!, sa'[4]!, k, k', heq, g'])
  let (_, g'') ← g'.mvarId!.intro n
  replaceMainGoal [g'']

end IRLean.Whole
