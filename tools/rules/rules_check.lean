/-! What `tools/rules/rules.py` asks Lean, in two modes, about modules it reads as data, so none of their code runs here.

**`rules`**: is each rule proved? For each name, `Rules.Stmt.<name>` has to be a definition of a `Prop` in
`Rules.Statements`, the generated module, and `Rules.<name>` a theorem, in a module of the `Rules` library, whose type
is that constant itself, with no universe parameters, resting on the standard three axioms and nothing else: nothing
from `bv_decide`, and no `sorry`.

**`cert`**: is a certificate's theorem exactly the claim that one generated function refines another?
`tools/rules/rules.py` writes `import IRLean` and the generated module above this text, and nothing else, so the
claim is elaborated where only Lean, `IRLean` and what the emitter wrote can give it meaning. It's built here from the
two names. The certificate's theorem has to be declared in the certificate's module, have no universe parameters,
mention only constants that are the same declarations here, and have a type that is the expected claim, as the same
`Expr`, as `tools/binding_check.lean` asks. A certificate may import the `Rules` library and what it imports, which
`tools/binding.py`'s certificates may not. The answer names the axioms the theorem rests on and the rules its proof
uses, read from the proof terms.

What to check comes from the JSON file `IRLEAN_RULES_CONFIG` names. Each answer is one line, starting with
`IRLEAN_RULES` and the run's nonce. The kernel replay is `leanchecker`'s, separately. -/

open Lean Meta

namespace IRLeanRules

def emit (nonce : String) (fields : List (String × Json)) : IO Unit := do
  IO.println s!"IRLEAN_RULES {nonce} {(Json.mkObj fields).compress}"
  (← IO.getStdout).flush

def moduleIn (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether `c` is the same declaration in both environments: from the same module, and so the same `.olean`. -/
def sameIn (here there : Environment) (c : Name) : Bool :=
  here.contains c && moduleIn here c == moduleIn there c

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every constant `roots` reach through types and values, and the axioms among them, as `tests/check_axioms.lean`
reads them. -/
def reachable (env : Environment) (roots : Array Name) : NameSet × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut axioms := #[]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | some (.axiomInfo v) =>
      axioms := axioms.push c
      todo := todo ++ v.type.getUsedConstants
    | some (.inductInfo v) => todo := todo ++ v.type.getUsedConstants ++ v.ctors.toArray
    | some info =>
      todo := todo ++ info.type.getUsedConstants
      if let some v := info.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
    | none => pure ()
  return (seen, axioms)

def pp (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))

/-- A rule's theorem: its name is `Rules.<rule>`, in a module of the library, and not one of the library's own
lemmas. -/
def ruleOf (env : Environment) (c : Name) : Option String :=
  match c with
  | .str (.str .anonymous "Rules") rule =>
    if env.contains (`Rules.Stmt ++ Name.mkSimple rule) then some rule else none
  | _ => none

unsafe def checkRules (nonce : String) (j : Json) : MetaM Unit := do
  let names ← IO.ofExcept (j.getObjValAs? (Array String) "rules")
  let env ← importModules #[{ module := `Rules }] {} (loadExts := false)
  for name in names do
    let stmt := `Rules.Stmt ++ Name.mkSimple name
    let thm := `Rules ++ Name.mkSimple name
    let refuse (reason detail : String) : MetaM Unit :=
      emit nonce [("rule", toJson name), ("ok", toJson false), ("reason", toJson reason), ("detail", toJson detail)]
    let some (.defnInfo d) := env.find? stmt
      | refuse "statement_missing" s!"{stmt} isn't a definition"; continue
    unless moduleIn env stmt == some `Rules.Statements do
      refuse "statement_not_generated" s!"{stmt} isn't declared in Rules.Statements"; continue
    unless d.type == .sort .zero && d.levelParams.isEmpty do
      refuse "statement_missing" s!"{stmt} isn't a Prop"; continue
    let some info := env.find? thm
      | refuse "not_proved" s!"there's no {thm}"; continue
    let .thmInfo t := info
      | refuse "not_proved" s!"{thm} isn't a theorem"; continue
    unless ((moduleIn env thm).map (·.getRoot)) == some `Rules do
      refuse "not_proved" s!"{thm} isn't declared in the Rules library"; continue
    unless t.levelParams.isEmpty && t.type == mkConst stmt do
      refuse "statement_mismatch" s!"{thm} doesn't state {stmt}"; continue
    let (_, axioms) := reachable env #[thm]
    if let some a := axioms.find? (!standardAxioms.contains ·) then
      refuse "disallowed_axiom" s!"{thm} rests on {a}"; continue
    emit nonce [("rule", toJson name), ("ok", toJson true),
      ("axioms", toJson (axioms.map (·.toString)).qsort.toList)]

unsafe def checkCert (nonce : String) (j : Json) : MetaM Unit := do
  let get (k : String) : MetaM String := IO.ofExcept (j.getObjValAs? String k)
  let src := (← get "src").toName
  let tgt := (← get "tgt").toName
  let genModule := (← get "generated_module").toName
  let certModule := (← get "certificate_module").toName
  let theoremName := (← get "theorem").toName
  let runDir ← get "run_dir"
  let libDirs ← IO.ofExcept (j.getObjValAs? (Array String) "library_dirs")
  let refuse (reason detail : String) (extra : List (String × Json) := []) : MetaM Unit :=
    emit nonce ([("ok", toJson false), ("reason", toJson reason), ("detail", toJson detail)] ++ extra)
  let here ← getEnv
  for f in [src, tgt] do
    unless moduleIn here f == some genModule do
      refuse "function_not_generated" s!"{f} isn't declared in {genModule}, as ir-lean generated it"; return
    let some (.defnInfo d) := here.find? f
      | refuse "function_not_generated" s!"{f} isn't a definition"; return
    unless d.levelParams.isEmpty do
      refuse "function_not_generated" s!"{f} has universe parameters, which ir-lean never writes"; return
  unless (← inferType (mkConst src)) == (← inferType (mkConst tgt)) do
    refuse "signature_mismatch" s!"{src} and {tgt} have different types, so no claim relates them"; return
  let want ← try
      instantiateMVars (← mkAppM `IRLean.Refines #[mkConst src, mkConst tgt])
    catch ex =>
      refuse "claim_unavailable" s!"IRLean.Refines doesn't apply: {← ex.toMessageData.toString}"; return
  let proof ← importModules #[{ module := certModule }] {} (loadExts := false)
  let allowed (m : Name) : Bool :=
    [`Init, `Std, `Lean, `IRLean, `Rules, `Peephole].contains m.getRoot || m == genModule || m == certModule
  if let some m := proof.header.moduleNames.find? (!allowed ·) then
    refuse "certificate_imports_disallowed"
      s!"the certificate imports {m}, and may only import Lean, IRLean, Rules, what Rules imports and the generated module"
    return
  -- Each module has to be the file it should be: Lean's from the toolchain, the libraries' from the repo's build,
  -- and the rest from the run. A module of the same name earlier on the search path would be read instead.
  let toolchainDir := (← IO.FS.realPath (← getLibDir (← findSysroot))).toString
  for m in proof.header.moduleNames do
    let path := (← IO.FS.realPath (← findOLean m)).toString
    let dirs :=
      if [`Init, `Std, `Lean].contains m.getRoot then #[toolchainDir]
      else if m == genModule || m == certModule then #[runDir]
      else libDirs
    unless dirs.any fun dir => path.startsWith (dir ++ "/") do
      refuse "module_shadowed" s!"{m} is read from {path}, not from {dirs}"; return
  let some info := proof.find? theoremName
    | refuse "theorem_not_found" s!"there's no {theoremName}"; return
  unless moduleIn proof theoremName == some certModule do
    refuse "theorem_not_found" s!"{theoremName} isn't declared in {certModule}"; return
  let .thmInfo thm := info
    | refuse "not_a_theorem" s!"{theoremName} isn't a theorem"; return
  unless thm.levelParams.isEmpty do
    refuse "claim_type_mismatch" s!"{theoremName} has universe parameters"; return
  if let some c := thm.type.getUsedConstants.find? (!sameIn here proof ·) then
    refuse "foreign_constant" s!"the theorem's type uses {c}, which isn't Lean's, IRLean's or the generated module's"
    return
  unless thm.type == want do
    refuse "claim_type_mismatch" s!"{theoremName} doesn't state the expected claim"
      [("expected", toJson (← pp want)), ("got", toJson (← pp thm.type))]
    return
  let (seen, axioms) := reachable proof #[theoremName]
  let rules := seen.toArray.filterMap (ruleOf proof ·) |>.qsort (· < ·)
  emit nonce [("ok", toJson true), ("statement", toJson (← pp want)),
    ("axioms", toJson (axioms.map (·.toString)).qsort.toList), ("rules", toJson rules.toList)]

unsafe def check : MetaM Unit := do
  let some path ← IO.getEnv "IRLEAN_RULES_CONFIG" | throwError "IRLEAN_RULES_CONFIG isn't set"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let nonce ← IO.ofExcept (j.getObjValAs? String "nonce")
  try
    match ← IO.ofExcept (j.getObjValAs? String "mode") with
    | "rules" => checkRules nonce j
    | "cert" => checkCert nonce j
    | m => throwError "no mode {m}"
  catch ex =>
    emit nonce [("ok", toJson false), ("reason", toJson "checker_error"),
      ("detail", toJson (← ex.toMessageData.toString))]

end IRLeanRules

run_meta unsafe IRLeanRules.check
