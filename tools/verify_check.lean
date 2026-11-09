/-! What `tools/verify.py` asks Lean about a claim. It writes `import Lean`, `import IRLean`, the generated module
and an `open` above this text, and runs the file twice: once to check the claim, once to evaluate witnesses.

None of the proof's code runs here. A file that imports a module runs that module's code, its initializers and the
elaborators and extensions it adds, and that code could print an answer of its own. So the proof and support
modules are read as data, with `importModules (loadExts := false)`: their declarations, and which module each came
from. Pinned statements and witnesses are elaborated where only Lean, IRLean and the generated module are
imported, and a bv_decide axiom is rerun with the toolchain's checker on the data the proof recorded.

What to check comes from the JSON file that `IRLEAN_VERIFY_CONFIG` names, so nothing in a request is pasted into
Lean source. Each answer is one line starting with `IRLEAN_VERIFY` and the run's nonce. -/

open Lean Meta Elab Command

namespace IRLeanVerify

structure Config where
  nonce : String
  mode : String
  /-- The generated function the claim has to be about, such as `Real.popcount`. -/
  target : Name
  /-- The module ir-lean generated, such as `Real`. -/
  generated : Name
  /-- The support modules and the proof, read as data. -/
  modules : Array Name
  proofModule : Option Name
  theoremName : Option String
  statement : Option String
  /-- `theorem` or `statement`: which one witnesses are evaluated against. -/
  witnessSource : String
  /-- Each witness assigns Lean terms to binders, by name or as `#0`, `#1`, ... for the binders that aren't
  hypotheses. -/
  witnesses : Array (Array (String × String))

def optStr (j : Json) (key : String) : Except String (Option String) :=
  match j.getObjVal? key with
  | .ok .null => .ok none
  | .ok v => some <$> v.getStr?
  | .error _ => .ok none

def parseConfig (j : Json) : Except String Config := do
  let witnesses ← (← j.getObjValAs? (Array Json) "witnesses").mapM fun w => do
    (← w.getArr?).mapM fun pair => do
      let p ← pair.getArr?
      unless p.size = 2 do throw "a witness binding is a pair of strings"
      return (← p[0]!.getStr?, ← p[1]!.getStr?)
  return {
    nonce := ← j.getObjValAs? String "nonce"
    mode := ← j.getObjValAs? String "mode"
    target := (← j.getObjValAs? String "target").toName
    generated := (← j.getObjValAs? String "generated").toName
    modules := (← j.getObjValAs? (Array String) "modules").map String.toName
    proofModule := (← optStr j "proof_module").map String.toName
    theoremName := ← optStr j "theorem"
    statement := ← optStr j "statement"
    witnessSource := ← j.getObjValAs? String "witness_source"
    witnesses }

def config : IO Config := do
  let some path ← IO.getEnv "IRLEAN_VERIFY_CONFIG" | throw (IO.userError "IRLEAN_VERIFY_CONFIG isn't set")
  match Json.parse (← IO.FS.readFile path) >>= parseConfig with
  | .ok c => return c
  | .error e => throw (IO.userError s!"bad config: {e}")

def emit (nonce : String) (fields : List (String × Json)) : IO Unit := do
  IO.println s!"IRLEAN_VERIFY {nonce} {(Json.mkObj fields).compress}"
  (← IO.getStdout).flush

/-- Full names, so a statement printed here elaborates to the same thing wherever it's pasted. -/
def pp (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))

def parseTerm (text what : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term text s!"<{what}>" with
  | .ok s => return s
  | .error e => throwError "the {what} doesn't parse: {e}"

def elabStatement (text : String) : TermElabM Expr := Term.withoutErrToSorry do
  let e ← Term.elabType (← parseTerm text "statement")
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "the statement has holes Lean couldn't fill"
  if e.hasSorry then throwError "the statement uses sorry"
  unless ← isProp e do throwError "the statement isn't a proposition"
  return e

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleIn (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def moduleOf (n : Name) : MetaM (Option Name) := return moduleIn (← getEnv) n

/-- The proof's modules and everything they import, as data: no initializer, elaborator or extension of theirs
runs. -/
def proofEnv (cfg : Config) : IO Environment :=
  importModules (cfg.modules.map fun m => { module := m }) {} (loadExts := false)

/-- Runs `x` in `env`, which isn't the environment this file elaborates in. -/
def inEnv (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<verify>", fileMap := default }
  return (← (x.run' {} {}).toIO ctx { env }).1

/-- Whether `c` is the same declaration here as in the proof's environment: from the same module, and so the same
`.olean`. -/
def sameIn (here proof : Environment) (c : Name) : Bool :=
  here.contains c && moduleIn here c == moduleIn proof c

/-- Whether the conclusion says the target returns normally: `target ... = Outcome.ok _`, perhaps under `∃`. -/
partial def shapeOf (target : Name) (concl : Expr) : String :=
  let rec strip (e : Expr) (under : Bool) : Expr × Bool :=
    if e.isAppOfArity ``Exists 2 then
      match e.appArg! with
      | .lam _ _ b _ => strip b true
      | _ => (e, under)
    else (e, under)
  let (core, under) := strip concl false
  if core.isAppOfArity ``Eq 3 then
    let lhs := core.appFn!.appArg!
    let rhs := core.appArg!
    let ok := rhs.isAppOf ``IRLean.Outcome.ok ||
      (rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isAppOf ``Except.ok)
    if ok && lhs.getUsedConstants.contains target then
      if under then "exists_returns_ok" else "returns_ok"
    else "other"
  else "other"

/-- What a statement names from the generated module, and which of its binders are hypotheses. This is what it
means, so it's read in the statement's own environment. -/
def meaning (cfg : Config) (type : Expr) : MetaM (List (String × Json) × Array Bool) := do
  let env ← getEnv
  let used := type.getUsedConstants
  let generated := used.filter fun c => moduleIn env c == some cfg.generated
  let mentions := used.contains cfg.target && moduleIn env cfg.target == some cfg.generated
  let hypotheses ← forallTelescope type fun xs _ => xs.mapM fun x => do isProp (← x.fvarId!.getType)
  return ([("generated_constants", toJson (generated.map toString)), ("mentions_target", toJson mentions)],
    hypotheses)

/-- The statement as text, with its binders and conclusion. Printed where this file elaborates, it gets Lean's and
IRLean's notation and nothing of the proof's, whose constants print by name. -/
def display (cfg : Config) (type : Expr) (hypotheses : Array Bool) : MetaM (List (String × Json)) := do
  forallTelescope type fun xs body => do
    let mut binders : Array Json := #[]
    for h : i in [0:xs.size] do
      let d ← xs[i].fvarId!.getDecl
      let kind := match d.binderInfo with
        | .default => "explicit" | .implicit => "implicit"
        | .strictImplicit => "strict_implicit" | .instImplicit => "instance"
      binders := binders.push <| Json.mkObj [
        ("name", toJson d.userName.eraseMacroScopes.toString),
        ("type", toJson (← pp d.type)),
        ("hypothesis", toJson (hypotheses[i]?.getD false)),
        ("binder", toJson kind)]
    return [
      ("statement", toJson (← pp type)),
      ("binders", Json.arr binders),
      ("conclusion", toJson (← pp body)),
      ("shape", toJson (shapeOf cfg.target body))]

def describe (cfg : Config) (type : Expr) : MetaM (List (String × Json)) := do
  let (m, hypotheses) ← meaning cfg type
  return (← display cfg type hypotheses) ++ m

/-- The theorem's name as given, or the one declaration in the proof module it's the end of. -/
def resolveTheorem (cfg : Config) (text : String) : MetaM (Except String Name) := do
  let env ← getEnv
  let n := text.toName
  let some proof := cfg.proofModule | return .error "no proof module"
  let some idx := env.getModuleIdx? proof | return .error s!"the proof module {proof} isn't imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  if names.contains n then return .ok n
  let candidates := names.filter fun c => c.toString.endsWith ("." ++ text)
  match candidates.toList with
  | [m] => return .ok m
  | [] =>
    if env.contains n then
      return .error s!"{n} isn't declared in the proof module {proof}, but in {(← moduleOf n).getD `unknown}"
    return .error s!"there's no {n} in the proof module {proof}"
  | ms => return .error s!"{text} could be any of {ms}"

/-- Whether `n` is named like an axiom `bv_decide` adds, as `tests/check_axioms.lean` reads them. -/
def bvDecideName : Name → Bool
  | .str (.str (.str _ "_native") "bv_decide") ax => ax.startsWith "ax_"
  | _ => false

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- What a bv_decide formula may be built from: constructors, types and literals. Building one runs no code. -/
def dataConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo _) | some (.inductInfo _) => true
  | _ => [``OfNat.ofNat, ``instOfNatNat, ``BitVec.ofNat].contains c

/-- The Bool an axiom bv_decide adds says is `true`, `verifyBVExpr formula certificate`, with the two replaced by
their values. Rerunning it runs the toolchain's checker on data, and nothing the proof wrote. -/
def bvDecideBool (env : Environment) (n : Name) : Except String Expr := do
  let unlike := s!"not what bv_decide would add: {n}"
  unless bvDecideName n do throw s!"not an allowed axiom: {n}"
  let some (.axiomInfo info) := env.find? n | throw unlike
  let t := info.type
  unless t.isAppOfArity ``Eq 3 && t.appArg! == mkConst ``Bool.true do throw unlike
  let b := t.appFn!.appArg!
  unless b.isAppOfArity `Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 do throw unlike
  let args ← b.getAppArgs.mapM fun arg => do
    let .const c [] := arg | throw unlike
    let some (.defnInfo d) := env.find? c | throw unlike
    if let some k := d.value.getUsedConstants.find? (!dataConst env ·) then
      throw s!"{unlike}: {c} uses {k}, so rerunning it would run more than bv_decide's checker"
    pure d.value
  return mkAppN b.getAppFn args

/-- `tests/check_axioms.lean`'s policy, on every declaration in the proof's modules: the standard three axioms, and
bv_decide's. Returns the Bools to rerun for bv_decide's. -/
def axiomPolicy (cfg : Config) : MetaM (Except String (Array (Name × Expr))) := do
  let env ← getEnv
  let mut rerun : Array (Name × Expr) := #[]
  for m in cfg.modules do
    let some idx := env.getModuleIdx? m | return .error s!"no module {m}"
    for d in env.header.moduleData[idx.toNat]!.constNames do
      for a in ← collectAxioms d do
        if standardAxioms.contains a || rerun.any (·.1 == a) then continue
        match bvDecideBool env a with
        | .ok b => rerun := rerun.push (a, b)
        | .error e => return .error s!"{m}: {e}"
  return .ok rerun

/-- Reruns bv_decide's checker here, where only the toolchain's code can run. -/
unsafe def rerunBVDecide (proof : Environment) (rerun : Array (Name × Expr)) : TermElabM (Except String Nat) := do
  let here ← getEnv
  for (a, b) in rerun do
    if let some c := b.getUsedConstants.find? (!sameIn here proof ·) then
      return .error s!"not what bv_decide would add: {a} uses {c} from {(moduleIn proof c).getD `unknown}"
    unless ← evalExpr Bool (mkConst ``Bool) b do
      return .error s!"not what bv_decide would add: {a}, whose certificate doesn't check"
  return .ok rerun.size

/-- What the proof's environment says about the theorem. Also its type, which binders are hypotheses, and whether
it's a theorem of a proposition. -/
def checkTheorem (cfg : Config) (text : String) :
    MetaM (List (String × Json) × Option (Expr × Array Bool × Bool)) := do
  match ← resolveTheorem cfg text with
  | .error e => return ([("found", false), ("error", toJson e)], none)
  | .ok n =>
    let info ← getConstInfo n
    let isProp' ← isProp info.type
    let axioms ← collectAxioms n
    let (m, hypotheses) ← meaning cfg info.type
    let fields := [
      ("found", toJson true), ("name", toJson n.toString),
      ("module", toJson ((← moduleOf n).map toString)), ("kind", toJson (kindOf info)),
      ("is_prop", toJson isProp'), ("axioms", toJson (axioms.map toString))] ++ m
    return (fields, some (info.type, hypotheses, kindOf info == "theorem" && isProp'))

unsafe def runCheck (cfg : Config) : CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  unless env.contains cfg.target && (← moduleOf cfg.target) == some cfg.generated do
    emit cfg.nonce [("kind", "check"), ("ok", false),
      ("error", toJson s!"{cfg.target} isn't in the generated module {cfg.generated}")]
    return
  let mut theoremJson := Json.null
  let mut policyJson := Json.null
  let mut theoremType : Option (Expr × Environment) := none
  if let some t := cfg.theoremName then
    let proof ← proofEnv cfg
    let (fields, found) ← inEnv proof (checkTheorem cfg t)
    let mut shown := []
    if let some (ty, hypotheses, isTheorem) := found then
      shown ← try display cfg ty hypotheses catch _ => inEnv proof (display cfg ty hypotheses)
      if isTheorem then theoremType := some (ty, proof)
    theoremJson := Json.mkObj (fields ++ shown)
    let policy ← match ← inEnv proof (axiomPolicy cfg) with
      | .error e => pure (.error e)
      | .ok rerun => try rerunBVDecide proof rerun
          catch ex => pure (.error s!"not what bv_decide would add: {← ex.toMessageData.toString}")
    policyJson := match policy with
      | .ok n => Json.mkObj [("ok", true), ("bv_decide", n)]
      | .error e => Json.mkObj [("ok", false), ("error", toJson e)]
  let mut statementJson := Json.null
  if let some text := cfg.statement then
    statementJson ← try
      let e ← elabStatement text
      let compare ← match theoremType with
        | none => pure Json.null
        | some (ty, proof) =>
          -- A constant of the proof's own, even one named like one here, is never what the statement names.
          if !ty.getUsedConstants.all (sameIn env proof) then pure (toJson "mismatch")
          else if e.eqv ty then pure (toJson "syntactic")
          else if ← (try withReducible (isDefEq e ty) catch _ => pure false) then pure (toJson "reducible_defeq")
          else pure (toJson "mismatch")
      pure (Json.mkObj ([("elaborated", toJson true), ("match", compare)] ++ (← describe cfg e)))
    catch ex =>
      pure (Json.mkObj [("elaborated", toJson false), ("error", toJson (← ex.toMessageData.toString))])
  emit cfg.nonce [("kind", "check"), ("ok", true), ("theorem", theoremJson), ("statement", statementJson),
    ("axiom_policy", policyJson)]

#eval show CommandElabM Unit from do
  let cfg ← config
  if cfg.mode == "check" then unsafe runCheck cfg

end IRLeanVerify

/- Witnesses are decided by running compiled code, and `Outcome` needs this to be decidable. Deriving it builds
the proof that it decides equality, and it comes after the check so it can't change how a statement elaborates
there. -/
deriving instance DecidableEq for Except

namespace IRLeanVerify

/-- The statement with each binder that isn't a hypothesis replaced by its witness. Hypotheses stay as
implications, so deciding the result decides whether the witness meets them and the conclusion holds. -/
partial def instantiate (e : Expr) (w : Array (String × String)) (used : Array String) (position : Nat) :
    TermElabM (Expr × Array String) := do
  match e with
  | .forallE n ty body bi =>
    if ← isProp ty then
      if body.hasLooseBVar 0 then
        throwError "the conclusion depends on the proof of hypothesis {n}, which can't be decided"
      let (b, used) ← instantiate (body.lowerLooseBVars 1 1) w used position
      return (.forallE n ty b bi, used)
    let name := n.eraseMacroScopes.toString
    let key := s!"#{position}"
    let value ← match w.find? (fun (k, _) => k == name || k == key) with
      | some (k, text) => do
        let v ← Term.withoutErrToSorry do
          let v ← Term.elabTermEnsuringType (← parseTerm text s!"witness for {name}") ty
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars v
        if v.hasMVar || v.hasSorry then throwError "the witness for {name} isn't a complete term"
        pure (v, used.push k)
      | none =>
        if bi.isInstImplicit then pure (← synthInstance ty, used)
        else throwError "no witness for binder {name} ({key})"
    instantiate (body.instantiate1 value.1) w value.2 (position + 1)
  | _ => return (e, used)

unsafe def evalBool (e : Expr) : TermElabM Bool := evalExpr Bool (mkConst ``Bool) e

unsafe def runWitnesses (cfg : Config) : CommandElabM Unit := liftTermElabM do
  let source ← match cfg.witnessSource, cfg.theoremName, cfg.statement with
    | "statement", _, some text => elabStatement text
    | "theorem", some text, _ => do
      let proof ← proofEnv cfg
      let ty ← inEnv proof do
        match ← resolveTheorem cfg text with
        | .ok n => pure (← getConstInfo n).type
        | .error e => throwError e
      let here ← getEnv
      if let some c := ty.getUsedConstants.find? (!sameIn here proof ·) then
        throwError "the theorem uses {c} from {(moduleIn proof c).getD `unknown}, and evaluating it would run \
          the proof's own code"
      pure ty
    | s, _, _ => throwError "nothing to evaluate witnesses against ({s})"
  emit cfg.nonce [("kind", "witness_start"), ("count", toJson cfg.witnesses.size),
    ("source", toJson cfg.witnessSource)]
  for h : i in [0:cfg.witnesses.size] do
    let w := cfg.witnesses[i]
    let fields ← try
      let (p, used) ← instantiate source w #[] 0
      for (k, _) in w do
        unless used.contains k do throwError "the witness names {k}, which isn't a binder of the statement"
      if p.hasLooseBVars || p.hasFVar || p.hasMVar then throwError "the instance isn't closed"
      let inst ← try synthInstance (mkApp (mkConst ``Decidable) p)
        catch _ => throwError "Lean can't decide the statement at this witness: no Decidable instance"
      let decision := mkApp2 (mkConst ``Decidable.decide) p inst
      for c in decision.getUsedConstants do
        if (← collectAxioms c).contains ``sorryAx then throwError "deciding it would use sorry, through {c}"
      let holds ← evalBool decision
      pure [("result", toJson (if holds then "holds" else "fails")), ("instance", toJson (← pp p))]
    catch ex =>
      pure [("result", toJson "unsupported"), ("error", toJson (← ex.toMessageData.toString))]
    emit cfg.nonce ([("kind", toJson "witness"), ("index", toJson i)] ++ fields)

#eval show CommandElabM Unit from do
  let cfg ← config
  if cfg.mode == "witness" then
    try unsafe runWitnesses cfg
    catch ex => emit cfg.nonce [("kind", "witness_error"), ("error", toJson (← ex.toMessageData.toString))]

end IRLeanVerify
