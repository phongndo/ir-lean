import Lean
import Peephole.Fold
import Peephole.Oracle
import Peephole.IC.Base

/-! # The Lean side of `tests/peephole.py`

`tests/peephole.py` compiles this into a directory of its own, and runs it from a driver it writes that imports the
families' modules. Nothing proved rests on it: it runs models, reads facts about theorems, and times them.

- `runCases`: each case's entry point on its operand, with `Oracle.none`, for `compare`. One JSON case a line in,
  one JSON answer a line out: the answer, the site that fired, and the registered folds the run reached. An InstCombine
  entry point takes a `Peephole.IC.Ctx` too, which the case gives: the instructions and arguments with one use in the
  function `opt` runs, and the phis, of which it has none.
- `prepare`: a fold's answer doesn't say which of its steps gave it, or which folds it ran through, so for each entry
  point this makes copies of it that say, below.
- `facts`: what `score` and `measure` ask: whether each site's theorem exists and what it rests on, which site
  theorems each fold's `sound` theorem uses, which stored lemmas each site's proof uses, and how long the kernel takes
  to check a site's proof with and without a stored lemma's proof put in its place.
- `timeModule`: a module's commands elaborated one at a time, the kernel's checks included, each timed. -/

open Lean Meta Elab

namespace PeepholeHarness

open Peephole

/-! ### Operands and answers, as JSON -/

def flagOf (j : Json) (k : String) : Bool :=
  match j.getObjValAs? Bool k with
  | .ok b => b
  | .error _ => false

def binOps : List (String × BinOp) :=
  [("add", .add), ("sub", .sub), ("mul", .mul), ("udiv", .udiv), ("sdiv", .sdiv), ("urem", .urem), ("srem", .srem),
    ("shl", .shl), ("lshr", .lshr), ("ashr", .ashr), ("and", .and), ("or", .or), ("xor", .xor)]

def preds : List (String × Pred) :=
  [("eq", .eq), ("ne", .ne), ("ugt", .ugt), ("uge", .uge), ("ult", .ult), ("ule", .ule), ("sgt", .sgt), ("sge", .sge),
    ("slt", .slt), ("sle", .sle)]

def binIntrs : List (String × BinIntr) :=
  [("umin", .umin), ("umax", .umax), ("smin", .smin), ("smax", .smax), ("uadd.sat", .uaddSat), ("usub.sat", .usubSat),
    ("sadd.sat", .saddSat), ("ssub.sat", .ssubSat)]

def unIntr (name : String) (flag : Bool) : Option UnIntr :=
  match name with
  | "ctpop" => some .ctpop
  | "bitreverse" => some .bitreverse
  | "bswap" => some .bswap
  | "ctlz" => some (.ctlz flag)
  | "cttz" => some (.cttz flag)
  | "abs" => some (.abs flag)
  | _ => none

def unName : UnIntr → String × Bool
  | .ctpop => ("ctpop", false)
  | .bitreverse => ("bitreverse", false)
  | .bswap => ("bswap", false)
  | .ctlz z => ("ctlz", z)
  | .cttz z => ("cttz", z)
  | .abs p => ("abs", p)

def lookupIn {α : Type} (table : List (String × α)) (what key : String) : Except String α :=
  match table.lookup key with
  | some a => pure a
  | none => throw s!"no {what} {key}"

def nameIn {α : Type} [BEq α] (table : List (String × α)) (a : α) : String :=
  ((table.find? (·.2 == a)).map (·.1)).getD "?"

/-- An operand, from `{"k": kind, "w": width, ...}` as `tests/peephole.py` writes it. -/
partial def term (w : Nat) (j : Json) : Except String (Term w) := do
  let k ← j.getObjValAs? String "k"
  let w' ← j.getObjValAs? Nat "w"
  unless w' == w do throw s!"an operand of width {w'} where {w} is needed: {j.compress}"
  let id := (j.getObjValAs? Nat "id").toOption.getD 0
  let part (key : String) : Except String Json := j.getObjVal? key
  let widthOf (x : Json) : Except String Nat := x.getObjValAs? Nat "w"
  match k with
  | "const" =>
    let c ← j.getObjValAs? String "c"
    let some n := c.toNat? | throw s!"bad constant {c}"
    return .const (BitVec.ofNat w n)
  | "poison" => return .poison
  | "undef" => return .undef
  | "var" => return .var id
  | "bin" =>
    let op ← lookupIn binOps "opcode" (← j.getObjValAs? String "op")
    let f : Flags :=
      { nuw := flagOf j "nuw", nsw := flagOf j "nsw", exact := flagOf j "exact", disjoint := flagOf j "disjoint" }
    return .bin id op f (← term w (← part "a")) (← term w (← part "b"))
  | "icmp" =>
    let p ← lookupIn preds "predicate" (← j.getObjValAs? String "p")
    let a ← part "a"
    let v ← widthOf a
    let t : Term 1 := .icmp id p (flagOf j "samesign") (← term v a) (← term v (← part "b"))
    if h : w = 1 then return (by subst h; exact t) else throw "an icmp is an i1"
  | "select" => return .select id (← term 1 (← part "c")) (← term w (← part "t")) (← term w (← part "e"))
  | "zext" =>
    let a ← part "a"
    return .zext id (flagOf j "nneg") (← term (← widthOf a) a)
  | "sext" =>
    let a ← part "a"
    return .sext id (← term (← widthOf a) a)
  | "trunc" =>
    let a ← part "a"
    return .trunc id (flagOf j "nuw") (flagOf j "nsw") (← term (← widthOf a) a)
  | "freeze" => return .freeze id (← term w (← part "a"))
  | "un" =>
    let f ← j.getObjValAs? String "f"
    let some u := unIntr f (flagOf j "flag") | throw s!"no intrinsic {f}"
    return .un id u (← term w (← part "a"))
  | "bi" =>
    let f ← lookupIn binIntrs "intrinsic" (← j.getObjValAs? String "f")
    return .bi id f (← term w (← part "a")) (← term w (← part "b"))
  | "fsh" => return .fsh id (flagOf j "left") (← term w (← part "a")) (← term w (← part "b")) (← term w (← part "c"))
  | _ => throw s!"no operand kind {k}"

def identJson : Peephole.Ident → Json
  | .const _ c => Json.mkObj [("const", toJson (toString c))]
  | .poison _ => "poison"
  | .undef _ => "undef"
  | .node id => Json.mkObj [("node", toJson id)]

/-- A replacement: an operand that exists by which `Value *` it is, or what a new instruction computes. -/
def replJson : {w : Nat} → Repl w → Json
  | w, .old t => Json.mkObj [("k", "old"), ("w", toJson w), ("t", identJson t.ident)]
  | w, .const c => Json.mkObj [("k", "const"), ("w", toJson w), ("c", toJson (toString c.toNat))]
  | w, .poison => Json.mkObj [("k", "poison"), ("w", toJson w)]
  | w, .bin op f a b =>
    Json.mkObj [("k", "bin"), ("w", toJson w), ("op", toJson (nameIn binOps op)), ("nuw", toJson f.nuw),
      ("nsw", toJson f.nsw), ("exact", toJson f.exact), ("disjoint", toJson f.disjoint), ("a", replJson a),
      ("b", replJson b)]
  | _, .icmp p s a b =>
    Json.mkObj [("k", "icmp"), ("w", toJson 1), ("p", toJson (nameIn preds p)), ("samesign", toJson s),
      ("a", replJson a), ("b", replJson b)]
  | w, .select c t e =>
    Json.mkObj [("k", "select"), ("w", toJson w), ("c", replJson c), ("t", replJson t), ("e", replJson e)]
  | w, .zext nneg a => Json.mkObj [("k", "zext"), ("w", toJson w), ("nneg", toJson nneg), ("a", replJson a)]
  | w, .sext a => Json.mkObj [("k", "sext"), ("w", toJson w), ("a", replJson a)]
  | w, .trunc nuw nsw a =>
    Json.mkObj [("k", "trunc"), ("w", toJson w), ("nuw", toJson nuw), ("nsw", toJson nsw), ("a", replJson a)]
  | w, .un f a =>
    Json.mkObj [("k", "un"), ("w", toJson w), ("f", toJson (unName f).1), ("flag", toJson (unName f).2),
      ("a", replJson a)]
  | w, .bi f a b =>
    Json.mkObj [("k", "bi"), ("w", toJson w), ("f", toJson (nameIn binIntrs f)), ("a", replJson a), ("b", replJson b)]
  | w, .fsh l a b c =>
    Json.mkObj [("k", "fsh"), ("w", toJson w), ("left", toJson l), ("a", replJson a), ("b", replJson b),
      ("c", replJson c)]

def resultJson {w : Nat} : Result w → Json
  | .value r => Json.mkObj [("value", replJson r)]
  | .null => Json.mkObj [("null", toJson true)]
  | .delegated c => Json.mkObj [("delegated", toJson c)]

/-! ### Oracles that answer yes

Where `opt` folds and the model with `Oracle.none` doesn't, the comparison asks whether an analysis could explain it:
whether the model fires with an oracle that knows everything it's asked. These aren't sound, and nothing is proved with
them. -/

def yesOracle (zeros : Bool) : Oracle where
  knownZero _ := if zeros then BitVec.allOnes _ else 0#_
  knownOne _ := if zeros then 0#_ else BitVec.allOnes _
  nonZero _ := true
  powerOfTwo _ _ := true
  signBits {w} _ := w
  notPoison _ := true
  nonEqual _ _ := true
  implies _ _ := some zeros

/-- Every value known to be non-negative: the sign bit known zero. -/
def nonNegOracle : Oracle where
  knownZero {w} _ := BitVec.intMin w
  knownOne _ := 0#_
  nonZero _ := true
  powerOfTwo _ _ := true
  signBits _ := 2
  notPoison _ := true
  nonEqual _ _ := true
  implies _ _ := none

def oracles : List (String × Oracle) :=
  [("every bit known zero", yesOracle true), ("every bit known one", yesOracle false), ("non-negative", nonNegOracle)]

/-! ### Which step fired, and which folds a run reached

A fold's answer says neither which of its steps gave it nor which other folds it ran through on the way. So for each
entry point the harness makes copies, each of it and of every definition between it and something it reaches:

- one in which `Peephole.run` is `runTagged`, which answers with the site of the step that fired;
- for each registered fold the entry point reaches, one in which that fold answers `ranTag` and its name, which a run
  that reaches it passes on as a delegation.

A definition reached only through a recursive or `partial` one can't be copied this way, and a fold whose caller drops
a delegation isn't seen: both leave less observed, never more. -/

def siteTag : String := "\x00site:"
def untaggedTag : String := "\x00untagged"
def ranTag : String := "\x00ran:"

/-- `run`, but a step that fires answers with its site, as a delegation no fold makes. -/
def runTagged {w : Nat} (steps : List (Step w)) : Result w :=
  match firedSite steps with
  | some s => .delegated (siteTag ++ s)
  | none => run steps

/-- What an entry point gives in place of its copy, when it couldn't be copied: no site. -/
def noSites : Oracle → {w : Nat} → Term w → Result w := fun _ _ _ => .delegated untaggedTag

/-- An entry point, as the driver runs it: with the `Ctx` an InstCombine fold reads, which InstSimplify's ignore. -/
abbrev EntryFn := IC.Ctx → Oracle → {w : Nat} → Term w → Result w

/-- Whether a constant of type `ty` takes a `Ctx` first, as an InstCombine entry point does. -/
def takesCtx (ty : Expr) : Bool :=
  match ty with
  | .forallE _ (.const n _) _ _ => n == ``Peephole.IC.Ctx
  | _ => false

/-- The constant `c`, of type `ty`, as an `EntryFn`: itself if it takes a `Ctx`, else ignoring one. -/
def asEntryFn (ty : Expr) (c : Expr) : Expr :=
  if takesCtx ty then c else .lam `_ctx (.const ``Peephole.IC.Ctx []) c .default

def taggedName (c : Name) : Name := `PeepholeHarness.Tagged ++ c

/-- The copy of `c` in which `fold` answers that it was reached. -/
def ranName (fold c : Name) : Name := `PeepholeHarness.Ran ++ fold ++ c

def inLibrary (env : Environment) (root c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!.getRoot == root
  | none => false

/-- The definitions of `Peephole` that `root` reaches and that reach `target`, callees first, `target` left out. -/
partial def toward (env : Environment) (root target : Name) : Array Name :=
  (go root |>.run ({}, #[])).2.2
where
  go (c : Name) : StateM (NameMap Bool × Array Name) Bool := do
    if c == target then return true
    if let some r := (← get).1.get? c then return r
    modify fun (m, a) => (m.insert c false, a)
    unless inLibrary env `Peephole c do return false
    let some (.defnInfo d) := env.find? c | return false
    let mut hit := false
    for u in d.value.getUsedConstants do
      if ← go u then hit := true
    if hit then modify fun (m, a) => (m.insert c true, a.push c)
    return hit

/-- Copies each definition, under `rename`, with `target` replaced by `by` and each of the others by its copy, and
compiles it. -/
def copyReplacing (names : Array Name) (rename : Name → Name) (target : Name) (by_ : List Level → Expr) :
    CoreM Unit := do
  let set := names.foldl (·.insert ·) ({} : NameSet)
  for c in names do
    if (← getEnv).contains (rename c) then continue
    let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} isn't a definition"
    let value := d.value.replace fun
      | .const n ls =>
        if n == target then some (by_ ls)
        else if set.contains n then some (.const (rename n) ls)
        else none
      | _ => none
    addAndCompile (.defnDecl { d with name := rename c, value, all := [rename c] })

/-- `fold` with its arguments, answering only that it was reached, if what it answers is a `Result`. -/
def marker (fold : Name) : MetaM (Option Expr) := do
  let some info := (← getEnv).find? fold | return none
  unless info matches .defnInfo _ do return none
  forallTelescope info.type fun xs body => do
    match (← whnf body).getAppFn, (← whnf body).getAppArgs with
    | .const ``Peephole.Result _, #[w] =>
      return some (← mkLambdaFVars xs (mkApp2 (.const ``Peephole.Result.delegated []) w
        (toExpr (ranTag ++ fold.toString))))
    | _, _ => return none

/-- What to watch for a registered fold, and what to put in its place: the fold itself, if it answers a `Result`,
or else `<fold>.steps`, the list of steps its callers run as theirs, as a single step that delegates. `run` passes that
on only where every step before it fell through, as the C++ reaches the fold. -/
def watched (fold : Name) : MetaM (Option (Name × Expr)) := do
  if let some m ← marker fold then return some (fold, m)
  let steps := fold ++ `steps
  let some (.defnInfo info) := (← getEnv).find? steps | return none
  forallTelescope info.type fun xs body => do
    let body ← whnf body
    let stepTy := body.appArg!
    match body.getAppFn, stepTy.getAppFn, stepTy.getAppArgs with
    | .const ``List _, .const ``Peephole.Step _, #[w] =>
      let one := mkApp2 (.const ``Peephole.Step.delegate []) w (toExpr (ranTag ++ fold.toString))
      return some (steps, ← mkLambdaFVars xs (← mkListLit stepTy [one]))
    | _, _, _ => return none

structure Entry where
  name : String
  fold : EntryFn
  tagged : EntryFn
  /-- For each registered fold the entry point reaches, a copy of it in which that fold answers that it was reached. -/
  ran : Array (String × EntryFn)

/-- For each entry point, its copies, and `PeepholeHarness.Driver.table`, the `Entry` of each, for the driver's `main`.
`folds` are the registered folds to watch for. -/
def prepare (entries folds : Array Name) : MetaM Unit :=
  withOptions (Elab.async.set · false) do
    let mut targets := #[]
    for f in folds do
      match ← watched f with
      | some (t, m) => targets := targets.push (f, t, m)
      | none =>
        -- Neither the fold nor `<fold>.steps` is a definition here that answers a `Result` or steps.
        IO.eprintln s!"HARNESS-UNWATCHABLE {f}"
    let mut table := #[]
    for e in entries do
      let some info := (← getEnv).find? e | throwError "no entry point {e}"
      try
        copyReplacing (toward (← getEnv) e ``Peephole.run) taggedName ``Peephole.run (.const ``runTagged ·)
        unless (← getEnv).contains (taggedName e) do throwError "it doesn't reach Peephole.run"
      catch ex =>
        IO.eprintln s!"HARNESS-UNTAGGED {e}: {← ex.toMessageData.toString}"
        let value := if takesCtx info.type then .lam `_ctx (.const ``Peephole.IC.Ctx []) (.const ``noSites [])
          .default else .const ``noSites []
        addAndCompile (.defnDecl {
          name := taggedName e, levelParams := [], type := info.type, value,
          hints := .opaque, safety := .safe, all := [taggedName e] })
      let mut ran := #[]
      for (f, target, m) in targets do
        let path := toward (← getEnv) e target
        if path.isEmpty then continue
        try
          copyReplacing path (ranName f) target fun _ => m
          ran := ran.push (mkApp4 (.const ``Prod.mk [0, 0]) (.const ``String []) (.const ``EntryFn [])
            (toExpr f.toString) (asEntryFn info.type (.const (ranName f e) [])))
        catch ex =>
          IO.eprintln s!"HARNESS-UNWATCHED {e} {f}: {← ex.toMessageData.toString}"
      let pair := mkApp2 (.const ``Prod [0, 0]) (.const ``String []) (.const ``EntryFn [])
      table := table.push (mkAppN (.const ``Entry.mk []) #[toExpr e.toString, asEntryFn info.type (.const e []),
        asEntryFn info.type (.const (taggedName e) []), ← mkArrayLit pair ran.toList])
    let name := `PeepholeHarness.Driver.table
    addAndCompile (.defnDecl {
      name, levelParams := [], type := mkApp (.const ``Array [Level.zero]) (.const ``Entry []),
      value := ← mkArrayLit (.const ``Entry []) table.toList, hints := .opaque, safety := .safe, all := [name] })

/-! ### Running cases -/

def siteOf (e : Entry) (c : IC.Ctx) (o : Oracle) {w : Nat} (t : Term w) : Json :=
  match e.tagged c o t with
  | .delegated s =>
    if s.startsWith siteTag then toJson (String.ofList (s.toList.drop siteTag.length))
    else if s == untaggedTag then "unknown" else Json.null
  | _ => Json.null

/-- The `Ctx` a case gives: `"one_use"`, the identities of the instructions and arguments with one use in the function
`opt` runs, and `"phi"`, those that are phis. A constant has neither. -/
def ctxOf (j : Json) : IC.Ctx :=
  let ids (k : String) : Array Nat := (j.getObjValAs? (Array Nat) k).toOption.getD #[]
  let one := ids "one_use"
  let phis := ids "phi"
  let has (xs : Array Nat) {w : Nat} (t : Term w) : Bool :=
    match t.ident with
    | .node id => xs.contains id
    | _ => false
  { oneUse := has one, phi := has phis }

/-- One case: the entry point's answer with `Oracle.none`, the site that fired, and if none did, the first oracle that
answers yes to everything and makes it fire. Then the folds a run with `Oracle.none` reached, of those `watch` says to
look for. -/
def runCase (entries : Array Entry) (watch : String → String → Bool) (line : String) :
    Except String (Json × String × Array String) := do
  let j ← Json.parse line
  let name ← j.getObjValAs? String "name"
  let entry ← j.getObjValAs? String "entry"
  let some e := entries.find? (·.name == entry) | throw s!"no entry point {entry}"
  let tj ← j.getObjVal? "term"
  let w ← tj.getObjValAs? Nat "w"
  let t ← term w tj
  let c := ctxOf j
  let r := e.fold c Oracle.none t
  let mut out := [("name", toJson name), ("result", resultJson r)]
  match r with
  | .value _ => out := out ++ [("site", siteOf e c Oracle.none t)]
  | _ =>
    for (label, o) in oracles do
      if let .value r' := e.fold c o t then
        out := out ++ [("analysis",
          Json.mkObj [("oracle", toJson label), ("value", replJson r'), ("site", siteOf e c o t)])]
        break
  -- Folds are looked for only in a case that's compared: `opt` left its operands alone, `"watch"`, and the model
  -- fired, or neither the model nor `opt` folded. A delegated case, or one where only `opt` folded, isn't.
  let optFolded := (j.getObjValAs? Bool "opt_folded").toOption.getD false
  let compared := match r with
    | .value _ => true
    | .null => !optFolded
    | .delegated _ => false
  let watching := (j.getObjValAs? Bool "watch").toOption.getD true && compared
  let mut reached := #[]
  for (f, copy) in e.ran do
    if !watching || !watch entry f then continue
    if let .delegated s := copy c Oracle.none t then
      if s == ranTag ++ f then reached := reached.push f
  return (Json.mkObj (out ++ [("ran", toJson reached)]), entry, reached)

/-- Each case, a line of JSON in and a line out. A fold is looked for from each entry point until one of its cases
reaches it. -/
def runCases (entries : Array Entry) (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run Driver.lean CASES.jsonl"; return 2
  let out ← IO.getStdout
  let mut seen : Std.HashSet (String × String) := {}
  for line in ← IO.FS.lines path do
    if line.isEmpty then continue
    match runCase entries (fun e f => !seen.contains (e, f)) line with
    | .ok (j, e, reached) =>
      out.putStrLn j.compress
      for f in reached do seen := seen.insert (e, f)
    | .error e => IO.eprintln s!"{e}: {line}"; return 1
  return 0

/-! ### Facts about theorems -/

/-- What `facts` is asked, from the file `PEEPHOLE_REQUEST` names. -/
structure Request where
  /-- Theorems that may prove a rewrite, `Peephole.<ID>`. -/
  sites : Array Name := #[]
  /-- Each fold's `sound` theorem. -/
  sounds : Array Name := #[]
  /-- The lemma store's lemmas. -/
  stored : Array Name := #[]
  /-- Pairs of a site theorem and a stored lemma its proof uses, to time with and without the lemma's proof inlined. -/
  pairs : Array (Name × Name) := #[]
  /-- How many times to check each, for the median. -/
  reps : Nat := 11

/-- A request's field `k`, or `d` if it has none. -/
def field {α : Type} [FromJson α] (j : Json) (k : String) (d : α) : Except String α :=
  match j.getObjVal? k with
  | .ok v => fromJson? v |>.mapError (s!"{k}: " ++ ·)
  | .error _ => pure d

instance : FromJson Request where
  fromJson? j := do
    let d : Request := {}
    let sites ← field j "sites" d.sites
    let sounds ← field j "sounds" d.sounds
    let stored ← field j "stored" d.stored
    let pairs ← field j "inline" d.pairs
    let reps ← field j "reps" d.reps
    return { sites, sounds, stored, pairs, reps }

def auxiliary (c : Name) : Bool := c.isInternal || isPrivateName c

/-- The constants `root`'s proof reaches, going through those `descend` allows. -/
def reach (env : Environment) (root : Name) (descend : Name → ConstantInfo → Bool) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some info := env.find? c | continue
    if c != root && !descend c info then continue
    if let some v := info.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen

def axiomsOf (c : Name) : MetaM (Array String) := do
  return (← collectAxioms c).map (·.toString)

/-- How long the kernel takes to check `decl`, in milliseconds, or none if it doesn't. -/
def kernelMs (decl : Declaration) : CoreM (Option Float) := do
  let t0 ← IO.monoNanosNow
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return some (((← IO.monoNanosNow) - t0).toFloat / 1e6)
  | .error _ => return none

def median (xs : Array Float) : Float :=
  if xs.isEmpty then 0 else (xs.qsort (· < ·))[xs.size / 2]!

/-- The kernel checking a site's proof as it is, and with a stored lemma's proof put where it's used. -/
def inlined (site lemma : Name) (reps : Nat) : MetaM Json := do
  let env ← getEnv
  let some (.thmInfo s) := env.find? site | return Json.mkObj [("site", toJson site.toString), ("error", "no site")]
  let some (.thmInfo l) := env.find? lemma | return Json.mkObj [("site", toJson site.toString), ("error", "no lemma")]
  let v := s.value.replace fun
    | .const n ls => if n == lemma then some (l.value.instantiateLevelParams l.levelParams ls) else none
    | _ => none
  let decl (tag : Name) (value : Expr) : Declaration := .thmDecl { s with name := tag ++ site, value }
  let mut store := #[]
  let mut inline := #[]
  for _ in [0:reps] do
    if let some t ← kernelMs (decl `_harnessStore s.value) then store := store.push t
    if let some t ← kernelMs (decl `_harnessInline v) then inline := inline.push t
  return Json.mkObj [("site", toJson site.toString), ("lemma", toJson lemma.toString), ("reps", toJson reps),
    ("store_ms", toJson (median store)), ("inlined_ms", toJson (median inline)),
    ("checked", toJson (store.size == reps && inline.size == reps && s.value.getUsedConstants.contains lemma))]

/-- Prints what the request asks, as one line of JSON after `HARNESS-JSON `. -/
def facts : MetaM Unit := do
  let some path ← IO.getEnv "PEEPHOLE_REQUEST" | throwError "PEEPHOLE_REQUEST isn't set"
  let req ← match Json.parse (← IO.FS.readFile path) >>= fromJson? with
    | .ok (r : Request) => pure r
    | .error e => throwError "bad request: {e}"
  let env ← getEnv
  let stored := req.stored.foldl (·.insert ·) ({} : NameSet)
  let inLib := inLibrary env `Peephole
  let mut sites := #[]
  for s in req.sites do
    let some info := env.find? s | continue
    -- The stored lemmas its proof uses: directly, or through theorems and auxiliary declarations of the `Peephole`
    -- library that aren't stored.
    let uses := reach env s fun c i =>
      inLib c && !stored.contains c && (i matches .thmInfo _ || auxiliary c)
    let direct : Array String := match info with
      | .thmInfo t => ((t.value.getUsedConstants.filter stored.contains).map (·.toString)).qsort (· < ·)
      | _ => #[]
    let mut kernel := #[]
    if let .thmInfo t := info then
      for _ in [0:req.reps] do
        if let some ms ← kernelMs (.thmDecl { t with name := `_harnessReplay ++ s }) then kernel := kernel.push ms
    sites := sites.push <| Json.mkObj [("name", toJson s.toString),
      ("kind", toJson (if info matches .thmInfo _ then "theorem" else "other")),
      ("module", toJson (env.getModuleIdxFor? s |>.map (env.header.moduleNames[·.toNat]!.toString))),
      ("axioms", toJson (← axiomsOf s)),
      ("uses", toJson ((uses.toArray.filter stored.contains).map (·.toString) |>.qsort (· < ·))),
      ("direct", toJson direct), ("kernel_ms", toJson (median kernel))]
  let siteSet := req.sites.foldl (·.insert ·) ({} : NameSet)
  let mut sounds := #[]
  for s in req.sounds do
    let some info := env.find? s | sounds := sounds.push (Json.mkObj [("name", toJson s.toString), ("found", false)])
    -- The site theorems it uses, through anything of the `Peephole` library.
    let reached := reach env s fun c _ => inLib c
    sounds := sounds.push <| Json.mkObj [("name", toJson s.toString), ("found", true),
      ("kind", toJson (if info matches .thmInfo _ then "theorem" else "other")),
      ("axioms", toJson (← axiomsOf s)),
      ("sites", toJson ((reached.toArray.filter siteSet.contains).map (·.toString) |>.qsort (· < ·)))]
  let mut inl := #[]
  for (site, lemma) in req.pairs do
    inl := inl.push (← inlined site lemma req.reps)
  IO.println s!"HARNESS-JSON {(Json.mkObj [("sites", Json.arr sites), ("sounds", Json.arr sounds),
    ("inline", Json.arr inl)]).compress}"

/-! ### Timing a module's commands -/

/-- Elaborates `path`, the source of `module`, one command at a time, as `lean` would but without elaborating in
parallel, so each command's time includes the kernel checking what it declares. Prints one line of JSON after
`HARNESS-JSON `: each command's line, time and the declarations it added. -/
unsafe def timeModule (path : System.FilePath) (module : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := (Elab.async.set {} false)
  let t0 ← IO.monoNanosNow
  let (env, messages) ← Elab.processHeader header opts messages inputCtx (mainModule := module)
  let importMs := ((← IO.monoNanosNow) - t0).toFloat / 1e6
  if messages.hasErrors then
    throw (IO.userError s!"importing {module}'s imports failed: {← messages.toList.mapM (·.toString)}")
  let mut st : Frontend.State :=
    { commandState := Command.mkState env messages opts, parserState, cmdPos := parserState.pos }
  let ctx : Frontend.Context := { inputCtx }
  let mut known := (← env.getLocalConstantInfos).size
  let mut rows := #[]
  let mut errors := #[]
  let mut done := false
  while !done do
    let line := inputCtx.fileMap.toPosition st.parserState.pos |>.line
    let t ← IO.monoNanosNow
    let (d, st') ← (Frontend.processCommand.run ctx).run st
    let ms := ((← IO.monoNanosNow) - t).toFloat / 1e6
    done := d
    st := st'
    -- Each command starts with no messages, so its errors are read here.
    for m in st.commandState.messages.toList do
      if m.severity == .error then errors := errors.push (← m.toString)
    let infos ← st.commandState.env.getLocalConstantInfos
    let added := (infos.extract known infos.size).map (·.name) |>.filter (!auxiliary ·)
    known := infos.size
    unless added.isEmpty do
      rows := rows.push <| Json.mkObj [("line", toJson line), ("ms", toJson ms),
        ("names", toJson (added.map (·.toString)))]
  IO.println s!"HARNESS-JSON {(Json.mkObj [("module", toJson module.toString), ("import_ms", toJson importMs),
    ("errors", toJson errors), ("commands", Json.arr rows)]).compress}"

unsafe def timeMainImpl (args : List String) : IO UInt32 := do
  let [path, module] := args | IO.eprintln "usage: lean --run Time.lean FILE MODULE"; return 2
  timeModule path module.toName
  return 0

/-- `timeModule` on the file and module named, as a program's `main`. -/
@[implemented_by timeMainImpl] opaque timeMain (args : List String) : IO UInt32

end PeepholeHarness
