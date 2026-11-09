import LemmaStore.Select
import Lean.Elab.Tactic.BVDecide

/-! # The lemma store's checker and lookup

`tools/store/store.py` runs these from a file it writes, which imports the store, its counterexamples and the modules
whose proofs count as uses, and prints one line of JSON. `store.py` decides from those facts whether a lemma is
admitted, a candidate, or refused, and why. `docs/lemma-store.md` has the bar.

What's computed here isn't what makes a lemma trusted: `tests/check_axioms.lean`, reading each module as data, and
`leanchecker` are, and `store.py` runs both. This runs the store's code, as any file importing it does. -/

open Lean Meta Elab

namespace StoreTool

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- What `store.py` asks for, in the file `LEMMA_STORE_REQUEST` names. -/
structure Request where
  /-- The lemmas to examine. -/
  lemmas : Array Name
  /-- The store they're judged against, for duplicates and subsumption: every stored lemma before them. -/
  catalog : Array Name
  /-- Modules whose own theorems are examined too, apart from counterexamples: a file of lemmas to add. -/
  modules : Array Name := #[]
  /-- Where each lemma's counterexamples and witness are: `<prefix>.<lemma>.drop_<hypothesis>` and `.sat`. -/
  counterPrefix : Name := `LemmaStore.Counter
  /-- The budget for each tactic tried on a lemma, in thousands of heartbeats, as `maxHeartbeats` counts. -/
  heartbeats : Nat := 20000
  /-- Whether to try closing each lemma with `simp`, `bv_normalize`, `grind` and `decide`. -/
  triviality : Bool := true
  /-- Whether to print each catalog lemma's key too, for judging new lemmas against the store. -/
  catalogKeys : Bool := false

/-- A request's field `k`, or `d` if it has none. -/
def field [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .ok v => fromJson? v |>.mapError (s!"{k}: " ++ ·)
  | .error _ => pure d

instance : FromJson Request where
  fromJson? j := do
    let d : Request := { lemmas := #[], catalog := #[] }
    return {
      lemmas := ← field j "lemmas" d.lemmas, catalog := ← field j "catalog" d.catalog,
      modules := ← field j "modules" d.modules, counterPrefix := ← field j "counterPrefix" d.counterPrefix,
      heartbeats := ← field j "heartbeats" d.heartbeats, triviality := ← field j "triviality" d.triviality,
      catalogKeys := ← field j "catalogKeys" d.catalogKeys }

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

def pp (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.set `format.width (1000 : Nat)) (ppExpr e))

/-! ### Width and constants -/

/-- The widths written as numbers in a statement, as the argument of `BitVec` or `IRLean.Val`. `store.py` allows 1,
which LLVM fixes for conditions, flags and comparisons. -/
def literalWidths (e : Expr) : Array Nat := Id.run do
  let mut out := #[]
  for sub in subterms e do
    if let some w := width? sub then
      if !out.contains w then out := out.push w
  return out
where
  width? (e : Expr) : Option Nat :=
    match e.getAppFn, e.getAppArgs with
    | .const ``BitVec _, #[w] | .const ``IRLean.Val _, #[w] => if w.hasLooseBVars || w.hasFVar then none else w.nat?
    | _, _ => none
  subterms (e : Expr) : Array Expr := Id.run do
    let mut acc := #[]
    let mut todo := #[e]
    while !todo.isEmpty do
      let x := todo.back!
      todo := todo.pop
      acc := acc.push x
      match x with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
      | .mdata _ y | .proj _ _ y => todo := todo.push y
      | _ => pure ()
    return acc

/-- Bit-vector constants other than `0` and `1` written as numbers, which a general lemma lifts into a variable with a
side condition. -/
def literalConstants (e : Expr) : Array String := Id.run do
  let mut out := #[]
  for sub in literalWidths.subterms e do
    let s? : Option String := match sub.getAppFn, sub.getAppArgs with
      | .const ``BitVec.ofNat _, #[w, n] => n.nat?.bind fun v => if v ≤ 1 then none else some s!"{v}#{w.nat?.getD 0}"
      | .const ``OfNat.ofNat _, #[t, n, _] =>
        if t.isAppOfArity ``BitVec 1 then n.nat?.bind fun v => if v ≤ 1 then none else some s!"{v}" else none
      | _, _ => none
    if let some s := s? then
      if !out.contains s then out := out.push s
  return out

/-! ### Hypotheses, counterexamples and the witness -/

/-- A hypothesis' counterexample is named after its binder, or its position if the binder has no name of its own. -/
def dropName (x : Expr) (pos : Nat) : MetaM String := do
  let n := (← x.fvarId!.getDecl).userName
  return if n.hasMacroScopes || n.isAnonymous then s!"drop_{pos}" else s!"drop_{n.eraseMacroScopes}"

/-- Whether the theorem `c` states `expected`: the same proposition up to reducible unfolding, or with the same key. -/
def states (c : Name) (expected : Expr) : MetaM (Option String) := do
  let some info := (← getEnv).find? c | return some "missing"
  unless info matches .thmInfo _ do return some "not_a_theorem"
  let actual ← instantiateTypeLevelParams info.toConstantVal (← mkFreshLevelMVarsFor info)
  if ← withoutModifyingState (withReducible (isDefEq expected actual)) then return none
  if (← LemmaStore.Normal.keyText [] expected) == (← LemmaStore.Normal.keyText [] actual) then return none
  return some "mismatch"

/-- `∃ xs, body`, the variables innermost last. -/
def mkExists (xs : Array Expr) (body : Expr) : MetaM Expr :=
  xs.foldrM (init := body) fun x b => do
    let lam ← match ← mkLambdaFVars #[x] b with
      | .lam n t e _ => pure (Expr.lam n t e .default)
      | e => pure e
    mkAppM ``Exists #[lam]

def mkAnds (ps : Array Expr) : Expr :=
  if ps.isEmpty then mkConst ``True else ps.pop.foldr mkAnd ps.back!

structure Hypothesis where
  binder : String
  statement : String
  counterexample : String
  /-- `ok`, `missing`, `mismatch`, `not_a_theorem`, or `typing` when the statement can't be formed without it. -/
  status : String
  expected : String

/-- Each hypothesis of `n`, whether a counterexample shows it's needed, and whether a witness shows they can all hold. -/
def hypotheses (n : Name) (type : Expr) (pre : Name) : MetaM (Array Hypothesis × Option (String × String × String)) :=
  forallTelescope type fun xs body => do
    let mut out := #[]
    let mut hyps := #[]
    let mut vars := #[]
    for x in xs, i in [0:xs.size] do
      unless ← isProp (← inferType x) do
        vars := vars.push x
        continue
      hyps := hyps.push x
      let drop ← dropName x i
      let cex := pre ++ n ++ drop.toName
      let rest := xs.eraseIdx! i
      -- Whether anything after it mentions it, so it can't be dropped.
      let laterTypes ← (xs.extract (i + 1) xs.size).mapM inferType
      let mentions := (laterTypes.push body).any (·.containsFVar x.fvarId!)
      let statement ← pp (← inferType x)
      if mentions then
        out := out.push { binder := drop, statement, counterexample := cex.toString, status := "typing", expected := "" }
        continue
      let expected := mkNot (← mkForallFVars rest body)
      let status := (← states cex expected).getD "ok"
      out := out.push { binder := drop, statement, counterexample := cex.toString, status, expected := ← pp expected }
    if hyps.isEmpty then return (out, none)
    let sat := mkAnds (← hyps.mapM inferType)
    -- A hypothesis about another hypothesis can't be put in a conjunction; its lemma needs a witness by hand.
    let expected ← mkExists vars sat
    let name := pre ++ n ++ `sat
    let status := (← states name expected).getD "ok"
    return (out, some (name.toString, status, ← pp expected))

/-! ### Cheap enough, and not trivial -/

/-- How long the kernel takes to check `n`'s declaration again, under a fresh name, in milliseconds. -/
def replayMs (n : Name) : MetaM (Option Float) := do
  let some (.thmInfo info) := (← getEnv).find? n | return none
  let decl := Declaration.thmDecl { info with name := `_storeReplay ++ n }
  let t0 ← IO.monoNanosNow
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ =>
    let t1 ← IO.monoNanosNow
    return some ((t1 - t0).toFloat / 1e6)
  | .error _ => return none

/-- Whether `tac` closes `type` within the budget. Any error, including running out of heartbeats, is no. -/
def closes (type : Expr) (tac : TSyntax `tactic) (budget : Nat) : MetaM Bool := do
  let s ← saveState
  -- Running out of heartbeats is a runtime exception, which a plain `try` doesn't catch.
  tryCatchRuntimeEx
    (do
      let goal ← mkFreshExprMVar type
      let rest ← withTheReader Core.Context (fun c => { c with maxHeartbeats := budget * 1000 }) <|
        withCurrHeartbeats <| Term.TermElabM.run' (Tactic.run goal.mvarId! (Tactic.evalTactic tac))
      let ok := rest.isEmpty && !(← instantiateMVars goal).hasSyntheticSorry
      s.restore
      return ok)
    (fun _ => do
      s.restore
      return false)

/-- Which of `simp`, `bv_normalize`, `grind` and `decide` close `n` alone, with `n` itself left out of `simp`'s and
`grind`'s lemmas. -/
def closedBy (n : Name) (type : Expr) (budget : Nat) : MetaM (Array String) := do
  let id := mkIdent n
  let isSimp := (← getSimpTheorems).isLemma (.decl n)
  let tactics : List (String × TSyntax `tactic) := [
    ("simp", ← if isSimp then `(tactic| simp [-$id]) else `(tactic| simp)),
    ("bv_normalize", ← `(tactic| bv_normalize)),
    ("grind", ← `(tactic| grind)),
    ("decide", ← `(tactic| decide))]
  let mut out := #[]
  for (label, tac) in tactics do
    if ← closes type tac budget then out := out.push label
  return out

/-- The stored lemmas other than `n` that prove it by being applied: its conclusion is theirs instantiated, and every
side condition left is one of `n`'s hypotheses or closed by `decide`. -/
def subsumedBy (n : Name) (type : Expr) (catalog : Array Name) : MetaM (Array Name) :=
  forallTelescope type fun _ body => do
    let others := catalog.filter (· != n)
    let ms ← LemmaStore.instances others body
    return ms.filter (fun m => m.unassigned == 0 && m.decided.all id) |>.map (·.name)

/-! ### Uses -/

/-- Whether `c` is part of a proof rather than a proof: generated by Lean, or private to its module. -/
def auxiliary (c : Name) : Bool := c.isInternal || isPrivateName c

/-- Every theorem that isn't Lean's own, a counterexample or auxiliary, with the constants its proof uses, through
auxiliary declarations of its own module. -/
def proofs (pre : Name) : MetaM (Array (Name × Name × NameSet)) := do
  let env ← getEnv
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if [`Init, `Std, `Lean, `Lake].contains m.getRoot then continue
    for c in env.header.moduleData[i]!.constNames do
      if auxiliary c || pre.isPrefixOf c then continue
      let some (.thmInfo info) := env.find? c | continue
      out := out.push (c, m, closure env m info.value)
  return out
where
  closure (env : Environment) (m : Name) (v : Expr) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo := v.getUsedConstants
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if auxiliary c && moduleOf env c == m then
        if let some info := env.find? c then
          if let some v := info.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
    return seen

/-! ### The facts about one lemma -/

def factsOf (req : Request) (uses : Array (Name × Name × NameSet)) (n : Name) : MetaM Json := do
  let env ← getEnv
  let some info := env.find? n | return Json.mkObj [("name", toJson n.toString), ("found", false)]
  let kind := match info with
    | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | _ => "other"
  let type := info.type
  let axioms := (← collectAxioms n).toList.map (·.toString)
  let swapped ← LemmaStore.Normal.swapped type
  -- As Mathlib's `simpNF` asks of a simp lemma's left side: the part a use site matches against its goal.
  let normal ← forallTelescope type fun _ body => do
    let b ← LemmaStore.Normal.eraseMData (← instantiateMVars body)
    let b := match b.getAppFn, b.getAppArgs with
      | .const ``Eq _, #[_, l, _] | .const ``Iff _, #[l, _] => l
      | _, _ => b
    let nb ← LemmaStore.Normal.normalize b
    if nb == b then return none else return some (← pp nb)
  let (hyps, sat) ← hypotheses n type req.counterPrefix
  let closed ← if req.triviality && kind == "theorem" then closedBy n type req.heartbeats else pure #[]
  let users := uses.filter (fun (c, _, used) => c != n && used.contains n)
  let swappedKey ← swapped.mapM (LemmaStore.Normal.keyText info.levelParams)
  return Json.mkObj [
    ("name", toJson n.toString), ("found", true), ("kind", toJson kind),
    ("module", toJson (moduleOf env n).toString), ("levels", toJson (info.levelParams.map (·.toString))),
    ("statement", toJson (← pp type)),
    ("key_text", toJson (← LemmaStore.Normal.keyText info.levelParams type)),
    ("swapped_key_text", match swappedKey with | some s => toJson s | none => Json.null),
    -- `none` when it's normal, or what `normalize` makes of the part matched against a goal.
    ("normal_form", match normal with | some s => toJson s | none => Json.null),
    ("axioms", toJson axioms),
    ("literal_widths", toJson (literalWidths type)),
    ("literal_constants", toJson (literalConstants type)),
    ("hypotheses", Json.arr (hyps.map fun h => Json.mkObj [("binder", toJson h.binder), ("statement", toJson h.statement),
      ("counterexample", toJson h.counterexample), ("status", toJson h.status), ("expected", toJson h.expected)])),
    ("witness", match sat with
      | some (nm, st, ex) => Json.mkObj [("name", toJson nm), ("status", toJson st), ("expected", toJson ex)]
      | none => Json.null),
    ("closed_by", toJson closed),
    ("subsumed_by", toJson ((← subsumedBy n type req.catalog).map (·.toString))),
    ("replay_ms", match ← replayMs n with | some t => toJson t | none => Json.null),
    ("used_by", Json.arr (users.map fun (c, m, _) =>
      Json.mkObj [("theorem", toJson c.toString), ("module", toJson m.toString)]))]

def readRequest : IO Request := do
  let some path ← IO.getEnv "LEMMA_STORE_REQUEST" | throw (IO.userError "LEMMA_STORE_REQUEST isn't set")
  match Json.parse (← IO.FS.readFile path) >>= fromJson? with
  | .ok r => return r
  | .error e => throw (IO.userError s!"bad request in {path}: {e}")

/-- Prints the facts about each lemma the request names, as one line of JSON after `STORE-JSON `. -/
def check : MetaM Unit := do
  let req ← readRequest
  let uses ← withCurrHeartbeats (proofs req.counterPrefix)
  let env ← getEnv
  let mut lemmas := req.lemmas
  for m in req.modules do
    let some i := env.getModuleIdx? m | throwError "no module {m}"
    for c in env.header.moduleData[i.toNat]!.constNames do
      if auxiliary c || req.counterPrefix.isPrefixOf c then continue
      if let some (.thmInfo _) := env.find? c then lemmas := lemmas.push c
  let mut out := #[]
  for n in lemmas do
    -- Each lemma gets the default budget of its own, and running out of it is reported, never taken as a verdict.
    let fact ← tryCatchRuntimeEx (withCurrHeartbeats (factsOf req uses n)) fun e => do
      return Json.mkObj [("name", toJson n.toString), ("found", true), ("limit", toJson (← e.toMessageData.toString))]
    out := out.push fact
  let mut keys := #[]
  if req.catalogKeys then
    for n in req.catalog do
      let some info := env.find? n | continue
      keys := keys.push (← withCurrHeartbeats do
        let swapped ← (← LemmaStore.Normal.swapped info.type).mapM (LemmaStore.Normal.keyText info.levelParams)
        return Json.mkObj [("name", toJson n.toString),
          ("key_text", toJson (← LemmaStore.Normal.keyText info.levelParams info.type)),
          ("swapped_key_text", match swapped with | some k => toJson k | none => Json.null)])
  IO.println s!"STORE-JSON {(Json.mkObj [("lemmas", Json.arr out), ("catalog", Json.arr keys)]).compress}"

/-! ### Lookup -/

/-- Looks up the proposition `q`'s value in the store, and prints what matches as one line of JSON. -/
def lookup (q : Name) : MetaM Unit := do
  let some (.defnInfo d) := (← getEnv).find? q | throwError "no query {q}"
  let stmt ← instantiateMVars d.value
  let key ← LemmaStore.Normal.keyText [] stmt
  let swapped ← LemmaStore.Normal.swapped stmt
  let swappedKey ← swapped.mapM (LemmaStore.Normal.keyText [])
  let mut exact := #[]
  for n in LemmaStore.catalog do
    let info ← getConstInfo n
    let k ← LemmaStore.Normal.keyText info.levelParams info.type
    if k == key then exact := exact.push (Json.mkObj [("name", toJson n.toString), ("reversed", false)])
    else if swappedKey == some k then exact := exact.push (Json.mkObj [("name", toJson n.toString), ("reversed", true)])
  let inst ← forallTelescope stmt fun _ body => do
    let ms ← LemmaStore.instances LemmaStore.catalog body
    ms.mapM fun m => do
      let sides ← m.sideConditions.mapM pp
      return Json.mkObj [("name", toJson m.name.toString), ("reversed", toJson m.reversed),
        ("side_conditions", Json.arr ((sides.zip m.decided).map fun (s, d) =>
          Json.mkObj [("statement", toJson s), ("closed_by", if d then toJson "decide" else Json.null)])),
        ("free_variables", toJson m.unassigned)]
  IO.println s!"STORE-JSON {(Json.mkObj [("key_text", toJson key), ("statement", toJson (← pp stmt)),
    ("exact", Json.arr exact), ("instances", Json.arr inst)]).compress}"

end StoreTool
