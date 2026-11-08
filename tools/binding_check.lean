/-! What `tools/binding.py` asks Lean about one certificate: is the theorem it names exactly the claim its kind says,
about the two functions ir-lean regenerated from the IR, and nothing else?

`tools/binding.py` writes `import IRLean` and the two generated modules above this text, and nothing else, so the
claim is elaborated where only Lean, `IRLean` and what the emitter wrote can give it meaning. The claim is built here
from the kind and the two names. Nothing the certificate says goes into it.

The certificate module is then read as data, with `importModules (loadExts := false)`, so none of its code runs here:
its declarations, and which module each came from. Its theorem has to be declared in it, have no universe parameters,
mention only constants that are the same declarations here, and have a type that is the expected claim, as the same
`Expr`. Definitional equality isn't enough: an instance or a definition of the certificate's own could make a weaker
claim unfold to the right one.

What to check comes from the JSON file `IRLEAN_BINDING_CONFIG` names. The answer is one line, starting with
`IRLEAN_BINDING` and the run's nonce. Axioms and the kernel replay are checked separately, by `tests/check_axioms.lean`
and `leanchecker`. -/

open Lean Meta Elab Command

namespace IRLeanBinding

structure Config where
  nonce : String
  kind : String
  src : Name
  tgt : Name
  srcModule : Name
  tgtModule : Name
  certModule : Name
  theoremName : Name

def parseConfig (j : Json) : Except String Config := do
  return {
    nonce := ← j.getObjValAs? String "nonce"
    kind := ← j.getObjValAs? String "kind"
    src := (← j.getObjValAs? String "src").toName
    tgt := (← j.getObjValAs? String "tgt").toName
    srcModule := (← j.getObjValAs? String "src_module").toName
    tgtModule := (← j.getObjValAs? String "tgt_module").toName
    certModule := (← j.getObjValAs? String "cert_module").toName
    theoremName := (← j.getObjValAs? String "theorem").toName }

def config : IO Config := do
  let some path ← IO.getEnv "IRLEAN_BINDING_CONFIG" | throw (IO.userError "IRLEAN_BINDING_CONFIG isn't set")
  match Json.parse (← IO.FS.readFile path) >>= parseConfig with
  | .ok c => return c
  | .error e => throw (IO.userError s!"bad config: {e}")

def emit (nonce : String) (fields : List (String × Json)) : IO Unit := do
  IO.println s!"IRLEAN_BINDING {nonce} {(Json.mkObj fields).compress}"
  (← IO.getStdout).flush

def refuse (nonce reason detail : String) (extra : List (String × Json) := []) : IO Unit :=
  emit nonce ([("ok", toJson false), ("reason", toJson reason), ("detail", toJson detail)] ++ extra)

def moduleIn (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether `c` is the same declaration in both environments: from the same module, and so the same `.olean`. -/
def sameIn (here there : Environment) (c : Name) : Bool :=
  here.contains c && moduleIn here c == moduleIn there c

/-- Full names, and with `explicit` every implicit argument and instance, so a swapped instance shows. -/
def pp (e : Expr) (explicit := false) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.explicit explicit) (ppExpr e))

/-- The modules a certificate may import, besides the toolchain's: `IRLean` and the two generated modules. -/
def allowedModule (cfg : Config) (m : Name) : Bool :=
  [`Init, `Std, `Lean, `IRLean].contains m.getRoot || [cfg.srcModule, cfg.tgtModule, cfg.certModule].contains m

/-- `∀ args, ∀ s : IRLean.ModelStop, f args ≠ some (.error (.model s))`: `f` never stops the model. A model stop is
where IRLean doesn't know what LLVM does, such as freezing poison, so two functions that both stop there are equal in
the model and can still differ in LLVM. `.error` when `f` doesn't return an `IRLean.Outcome`. -/
def neverStops (f : Name) : MetaM (Except String Expr) := do
  let ty := (← getConstInfo f).type
  forallTelescope ty fun xs body => do
    unless body.isAppOfArity ``IRLean.Outcome 1 do
      return .error s!"{f} doesn't return an IRLean.Outcome"
    let ρ := body.appArg!
    let stop := mkConst ``IRLean.Stop
    withLocalDeclD `s (mkConst ``IRLean.ModelStop) fun s => do
      let err := mkApp3 (mkConst ``Except.error [0, 0]) stop ρ (mkApp (mkConst ``IRLean.Stop.model) s)
      let some' := mkApp2 (mkConst ``Option.some [0]) (mkApp2 (mkConst ``Except [0, 0]) stop ρ) err
      return .ok (← mkForallFVars (xs.push s) (← mkAppM ``Ne #[mkAppN (mkConst f) xs, some']))

/-- The claim, built here. `.error (reason, detail)` when there's none to build. -/
def expected (cfg : Config) : MetaM (Except (String × String) Expr) := do
  let env ← getEnv
  for (f, m) in [(cfg.src, cfg.srcModule), (cfg.tgt, cfg.tgtModule)] do
    unless moduleIn env f == some m do
      return .error ("function_not_generated", s!"{f} isn't declared in {m}, as ir-lean generated it")
    let some (.defnInfo d) := env.find? f |
      return .error ("function_not_generated", s!"{f} isn't a definition")
    unless d.levelParams.isEmpty do
      return .error ("function_not_generated", s!"{f} has universe parameters, which ir-lean never writes")
  let s ← getConstInfo cfg.src
  let t ← getConstInfo cfg.tgt
  unless s.type == t.type do
    return .error ("signature_mismatch", s!"{cfg.src} and {cfg.tgt} have different types, so no claim relates them")
  match cfg.kind with
  | "ir_instance_equivalence" =>
    -- Equal in the model is evidence only where the model knows what LLVM does: so the source never stops it.
    match ← neverStops cfg.src with
    | .error e => return .error ("signature_mismatch", e)
    | .ok never => return .ok (← mkAppM ``And #[← mkEq (mkConst cfg.src) (mkConst cfg.tgt), never])
  | "ir_instance_refinement" =>
    unless env.contains `IRLean.Refines do
      return .error ("claim_kind_unavailable", "this IRLean has no IRLean.Refines")
    try
      return .ok (← instantiateMVars (← mkAppM `IRLean.Refines #[mkConst cfg.src, mkConst cfg.tgt]))
    catch ex =>
      return .error ("claim_kind_unavailable", s!"IRLean.Refines doesn't apply: {← ex.toMessageData.toString}")
  | k => return .error ("claim_kind_unverifiable", s!"{k} isn't a claim this checker can build")

unsafe def check : MetaM Unit := do
  let cfg ← config
  let here ← getEnv
  let want ← match ← expected cfg with
    | .ok e => pure e
    | .error (r, d) => refuse cfg.nonce r d; return
  let wantText ← pp want
  let proof ← importModules #[{ module := cfg.certModule }] {} (loadExts := false)
  let some _ := proof.getModuleIdx? cfg.certModule |
    refuse cfg.nonce "theorem_not_found" s!"no module {cfg.certModule}"; return
  if let some m := proof.header.moduleNames.find? (!allowedModule cfg ·) then
    refuse cfg.nonce "certificate_imports_disallowed"
      s!"the certificate imports {m}, and may only import Lean, IRLean and the two generated modules"
    return
  let some info := proof.find? cfg.theoremName |
    refuse cfg.nonce "theorem_not_found" s!"there's no {cfg.theoremName}"; return
  unless moduleIn proof cfg.theoremName == some cfg.certModule do
    refuse cfg.nonce "theorem_not_found"
      s!"{cfg.theoremName} is declared in {(moduleIn proof cfg.theoremName).getD `unknown}, not {cfg.certModule}"
    return
  let .thmInfo thm := info |
    refuse cfg.nonce "not_a_theorem" s!"{cfg.theoremName} isn't a theorem"; return
  unless thm.levelParams.isEmpty do
    refuse cfg.nonce "claim_type_mismatch" s!"{cfg.theoremName} has universe parameters"; return
  if let some c := thm.type.getUsedConstants.find? (!sameIn here proof ·) then
    refuse cfg.nonce "foreign_constant"
      s!"the theorem's type uses {c} from {(moduleIn proof c).getD `unknown}, which isn't Lean's, IRLean's or the \
        generated modules'"
      [("expected", toJson wantText)]
    return
  -- Every constant is the same declaration here, so the type can be printed and compared here.
  unless thm.type == want do
    let defeq ← try withReducible (isDefEq thm.type want) catch _ => pure false
    refuse cfg.nonce "claim_type_mismatch" s!"{cfg.theoremName} doesn't state the expected claim"
      [("expected", toJson (← pp want true)), ("got", toJson (← pp thm.type true)),
        ("reducible_defeq", toJson defeq)]
    return
  emit cfg.nonce [("ok", toJson true), ("statement", toJson wantText), ("theorem", toJson cfg.theoremName.toString)]

end IRLeanBinding

run_meta do
  try unsafe IRLeanBinding.check
  catch ex =>
    let nonce := (← IO.getEnv "IRLEAN_BINDING_NONCE").getD ""
    IRLeanBinding.refuse nonce "checker_error" (← ex.toMessageData.toString)
