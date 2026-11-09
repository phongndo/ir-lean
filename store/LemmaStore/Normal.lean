import Lean

/-! # The lemma store's normalizer

How the store gives one meaning one key. `docs/lemma-store.md` says what this does and doesn't identify.

A lemma's key is a hash of `serialize (← canonical type)`, its elaborated statement after:

- `≠`, `>` and `≥` are unfolded to `¬ =`, `<` and `≤`, which are reducible definitions of the same propositions;
- operands of every associative and commutative operator are put in one order, by core's `ac_nf` machinery;
- variables are ordered by where they first occur, the conclusion first, and hypotheses come after them, sorted;
- binder names, binder annotations and metadata are dropped.

`normalize` is the first two, which a use site can run on a goal too. A stored lemma has to be in that form already,
as Mathlib's `simpNF` linter asks of a simp lemma's left side, or a normalized goal could never match it. That's
`isNormal`. The variable order and the dropped names are only for the key.

The key is computed from the statement Lean elaborated, never from its text, so notation, names and implicit
arguments don't change it. Bump `version` whenever what this computes changes, since every key changes with it. -/

open Lean Meta

namespace LemmaStore.Normal

/-- Part of every key. -/
def version : Nat := 1

/-- `≠`, `>` and `≥` as `¬ =`, `<` and `≤`, which are what they're defined as. -/
def unfoldNotation (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => do
    match e.getAppFn, e.getAppArgs with
    | .const ``Ne [u], #[α, a, b] => return .done (mkNot (mkApp3 (.const ``Eq [u]) α a b))
    | .const ``GT.gt [u], #[α, i, a, b] => return .done (mkApp4 (.const ``LT.lt [u]) α i b a)
    | .const ``GE.ge [u], #[α, i, a, b] => return .done (mkApp4 (.const ``LE.le [u]) α i b a)
    | _, _ => return .continue)

/-- Metadata dropped everywhere, which the kernel ignores too. -/
def eraseMData (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun e => return .done e.consumeMData)

/-- The operands of each associative and commutative operator in one order, as `ac_nf` puts them. -/
def acNormalize (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := ← getSimpCongrTheorems)
    (config := Simp.neutralConfig)
  let (res, _) ← Simp.main e ctx (methods := { post := Lean.Meta.AC.post })
  return res.expr

/-- What a use site runs on a goal: notation unfolded and AC operands ordered. -/
def normalize (e : Expr) : MetaM Expr := do
  let e ← eraseMData (← instantiateMVars e)
  acNormalize (← unfoldNotation e)

/-- Whether `normalize` leaves `type` as it is, up to binder names and annotations. -/
def isNormal (type : Expr) : MetaM Bool := do
  let type ← eraseMData (← instantiateMVars type)
  return (← normalize type) == type

/-! ### Serializing

A total, explicit printing of a closed term: every constant by its full name with its universe levels, every argument
including implicit ones and instances, and bound variables by de Bruijn index, so two statements print the same exactly
when they're the same term up to binder names and annotations. -/

partial def serializeLevel (params : List Name) : Level → String
  | .zero => "0"
  | .succ l => s!"(+1 {serializeLevel params l})"
  | .max a b => s!"(max {serializeLevel params a} {serializeLevel params b})"
  | .imax a b => s!"(imax {serializeLevel params a} {serializeLevel params b})"
  | .param p => match params.idxOf? p with
    | some i => s!"u{i}"
    | none => s!"u?{p}"
  | .mvar _ => "?u"

/-- `fvars` names free variables, by their position, for a statement still open. -/
partial def serializeWith (params : List Name) (fvars : FVarId → Option Nat) : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar f => match fvars f with
    | some i => s!"${i}"
    | none => s!"$?{f.name}"
  | .mvar _ => "?m"
  | .sort l => s!"(Sort {serializeLevel params l.normalize})"
  | .const c ls =>
    if ls.isEmpty then c.toString else s!"{c}.\{{",".intercalate (ls.map (serializeLevel params ·.normalize))}}"
  | e@(.app ..) =>
    let args := e.getAppArgs.toList.map (serializeWith params fvars)
    s!"({serializeWith params fvars e.getAppFn} {" ".intercalate args})"
  | .lam _ t b _ => s!"(fun {serializeWith params fvars t} {serializeWith params fvars b})"
  | .forallE _ t b _ => s!"(∀ {serializeWith params fvars t} {serializeWith params fvars b})"
  | .letE _ t v b _ => s!"(let {serializeWith params fvars t} {serializeWith params fvars v} {serializeWith params fvars b})"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s.quote
  | .mdata _ e => serializeWith params fvars e
  | .proj s i e => s!"(proj {s} {i} {serializeWith params fvars e})"

def serialize (params : List Name) (e : Expr) : String := serializeWith params (fun _ => none) e

/-! ### The canonical statement -/

mutual
/-- `out`, then `x` after the variables of `ids` its type mentions. -/
partial def place (ids : Array FVarId) (x : FVarId) (out : Array FVarId) : MetaM (Array FVarId) := do
  if out.contains x then return out
  let out ← walk ids (← x.getType) out
  return if out.contains x then out else out.push x

/-- `out`, then the variables of `ids` in `e`, left to right. -/
partial def walk (ids : Array FVarId) (e : Expr) (out : Array FVarId) : MetaM (Array FVarId) := do
  match e with
  | .fvar f => if ids.contains f then place ids f out else return out
  | .app f a => walk ids a (← walk ids f out)
  | .lam _ t b _ | .forallE _ t b _ => walk ids b (← walk ids t out)
  | .letE _ t v b _ => walk ids b (← walk ids v (← walk ids t out))
  | .mdata _ e | .proj _ _ e => walk ids e out
  | _ => return out
end

/-- The free variables of `vars` in `es`, in the order a left-to-right walk first meets them, each after the variables
its own type mentions, and then the ones that never occur, in their order. -/
def firstOccurrence (vars : Array Expr) (es : Array Expr) : MetaM (Array Expr) := do
  let ids := vars.map (·.fvarId!)
  let mut out := #[]
  for e in es do
    out ← walk ids e out
  for x in ids do
    out ← place ids x out
  return out.map mkFVar

/-- Whether a binder's type is a proposition: a hypothesis, rather than a variable. -/
def isHypothesis (x : Expr) : MetaM Bool := do isProp (← inferType x)

/-- The statement in the form its key is computed from. Variables come first, in the order they first occur, the
conclusion first; then hypotheses, sorted by how they print. Ordering variables changes how `ac_nf` orders operands,
so this repeats until neither changes. If a variable's type mentions a hypothesis, the binders keep their order. -/
partial def canonical (type : Expr) (fuel : Nat := 5) : MetaM Expr := do
  let type ← normalize type
  let next ← forallTelescope type fun xs body => do
    let mut vars := #[]
    let mut hyps := #[]
    for x in xs do
      if ← isHypothesis x then hyps := hyps.push x else vars := vars.push x
    -- A variable whose type mentions a hypothesis can't come before it.
    for v in vars do
      if (← v.fvarId!.getType).hasAnyFVar (fun f => hyps.any (·.fvarId! == f)) then
        return type
    let hypTypes ← hyps.mapM inferType
    let order ← firstOccurrence vars (#[body] ++ hypTypes)
    let position (f : FVarId) : Option Nat := order.findIdx? (·.fvarId! == f)
    let printed ← hyps.mapM fun h => return (serializeWith [] position (← inferType h), h)
    let sorted := (printed.qsort (fun a b => a.1 < b.1)).map (·.2)
    -- A hypothesis whose type mentions another keeps the original order.
    let dependent ← hyps.anyM fun h => return (← inferType h).hasAnyFVar (fun f => hyps.any (·.fvarId! == f))
    mkForallFVars (order ++ (if dependent then hyps else sorted)) body
  let next ← eraseMData (← instantiateMVars next)
  if next == type || fuel == 0 then return next else canonical next (fuel - 1)

/-- The conclusion's sides swapped, for an equation or an equivalence, under the same binders. -/
def swapped (type : Expr) : MetaM (Option Expr) :=
  forallTelescope type fun xs body => do
    match body.getAppFn, body.getAppArgs with
    | .const ``Eq us, #[α, a, b] => return some (← mkForallFVars xs (mkApp3 (.const ``Eq us) α b a))
    | .const ``Iff [], #[a, b] => return some (← mkForallFVars xs (mkApp2 (.const ``Iff []) b a))
    | _, _ => return none

/-- What the store hashes for a statement: the normalizer's version and the canonical statement. -/
def keyText (params : List Name) (type : Expr) : MetaM String := do
  return s!"ir-lean.store.key/{version} {serialize params (← canonical type)}"

end LemmaStore.Normal
