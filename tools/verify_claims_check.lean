import Lean
import Std.Tactic.BVDecide.Reflect

/-! What `tools/verify_claims.py` asks Lean about the theorems a claim's evidence names. It shares no code with
`tools/verify_check.lean`, `tools/binding_check.lean` or `tests/check_axioms.lean`, the scorer's checkers.

The modules the evidence names are read as data, with `importModules (loadExts := false)`, so none of their code runs
here, and nothing they print can pass for an answer: each answer is one line starting with `VERIFY_CLAIMS` and a nonce
this process reads from a file the evidence never sees. For each theorem:

- it's declared in the module the evidence names, as a theorem, with no universe parameters;
- every module is read from where it should be: Lean's from the toolchain, `IRLean`'s from its library, and the rest
  from the run's own directory;
- every constant its statement uses comes from Lean, `IRLean`, a module `ir-lean` generated, or a module the evidence
  lists as the model, so the statement means what those files say, and never what the proof defines;
- it names each generated function it's about, declared in that function's generated module;
- every axiom it rests on is one of the standard three, or one `bv_decide` adds, rerun here with only the toolchain's
  code. `sorryAx` is reported as `sorry`.

It answers with the statement printed with full names, and a serialization of the statement's `Expr` that two
different statements never share, which `tools/verify_claims.py` hashes and compares with the evidence. -/

open Lean Meta

-- Printing a large statement can take more than Lean's default heartbeats. Nothing here elaborates what the evidence
-- wrote, and tools/verify_claims.py gives this process a time limit of its own.
set_option maxHeartbeats 0

namespace VerifyClaims

structure Theorem where
  module : Name
  name : Name
  about : Array Name

structure Config where
  nonce : String
  modules : Array Name
  generated : Array Name
  model : Array Name
  theorems : Array Theorem
  runDir : String
  irleanDir : String
  /-- The toolchain's own library, where Lean's modules have to come from. -/
  toolchainDir : String

def parseTheorem (j : Json) : Except String Theorem := do
  return {
    module := (← j.getObjValAs? String "module").toName
    name := (← j.getObjValAs? String "name").toName
    about := (← j.getObjValAs? (Array String) "about").map String.toName }

def parseConfig (j : Json) : Except String Config := do
  let names (k : String) : Except String (Array Name) := do
    return (← j.getObjValAs? (Array String) k).map String.toName
  return {
    nonce := ← j.getObjValAs? String "nonce"
    modules := ← names "modules"
    generated := ← names "generated"
    model := ← names "model"
    theorems := ← (← j.getObjValAs? (Array Json) "theorems").mapM parseTheorem
    runDir := ← j.getObjValAs? String "run_dir"
    irleanDir := ← j.getObjValAs? String "irlean_dir"
    toolchainDir := ← j.getObjValAs? String "toolchain_dir" }

def answer (nonce : String) (fields : List (String × Json)) : IO Unit := do
  IO.println s!"VERIFY_CLAIMS {nonce} {(Json.mkObj fields).compress}"
  (← IO.getStdout).flush

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-! ## A serialization of `Expr` that two different statements never share

Every node is tagged, and every name and string is written with its length first, so the text reads back one way.
Binder names and metadata don't change what a statement says, and are left out. -/

def str (s : String) : String := s!"{s.length}:{s}"

def name : Name → String
  | .anonymous => "_"
  | .str p s => s!"(s {name p} {str s})"
  | .num p n => s!"(n {name p} {n})"

def level : Level → String
  | .zero => "0"
  | .succ l => s!"(+ {level l})"
  | .max a b => s!"(max {level a} {level b})"
  | .imax a b => s!"(imax {level a} {level b})"
  | .param n => s!"(p {name n})"
  | .mvar m => s!"(?l {name m.name})"

def binder : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

def expr : Expr → String
  | .bvar i => s!"(b {i})"
  | .fvar f => s!"(f {name f.name})"
  | .mvar m => s!"(? {name m.name})"
  | .sort l => s!"(S {level l})"
  | .const c ls => s!"(c {name c} [{" ".intercalate (ls.map level)}])"
  | .app f a => s!"(a {expr f} {expr a})"
  | .lam _ t b bi => s!"(l {binder bi} {expr t} {expr b})"
  | .forallE _ t b bi => s!"(P {binder bi} {expr t} {expr b})"
  | .letE _ t v b nd => s!"(L {nd} {expr t} {expr v} {expr b})"
  | .lit (.natVal n) => s!"(N {n})"
  | .lit (.strVal s) => s!"(T {str s})"
  | .mdata _ e => expr e
  | .proj s i e => s!"(j {name s} {i} {expr e})"

/-! ## Axioms -/

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every axiom `c` rests on, following each constant's type and value, an inductive's constructors and a
constructor's or recursor's inductive. -/
def axiomsOf (env : Environment) (c : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[c]
  let mut found := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | continue
    todo := todo ++ info.type.getUsedConstants
    match info with
    | .axiomInfo _ => found := found.push n
    | .defnInfo v => todo := todo ++ v.value.getUsedConstants
    | .thmInfo v => todo := todo ++ v.value.getUsedConstants
    | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
    | .inductInfo v => todo := todo ++ v.ctors.toArray ++ v.all.toArray
    | .ctorInfo v => todo := todo.push v.induct
    | .recInfo v => todo := todo ++ v.all.toArray
    | .quotInfo _ => pure ()
  return found

/-- Whether `n` is named as `bv_decide` names the axioms it adds: `..._native.bv_decide.ax_...`. -/
def bvDecideNamed : Name → Bool
  | .str (.str (.str _ "_native") "bv_decide") s => s.startsWith "ax_"
  | _ => false

/-- What a `bv_decide` formula or certificate may be made of: constructors and their types, and literals. Building
one runs nothing. -/
def inert (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo _) | some (.inductInfo _) => true
  | _ => c == ``OfNat.ofNat || c == ``instOfNatNat || c == ``BitVec.ofNat

/-- `none` if `a` is an axiom `bv_decide` would add, `verifyBVExpr formula certificate = true` with both made of
constructors and literals, and the toolchain's `verifyBVExpr` gives `true` on them here. -/
unsafe def bvDecideFails (here data : Environment) (a : Name) : MetaM (Option String) := do
  unless bvDecideNamed a do return some s!"{a} isn't an axiom this verifier allows"
  let some (.axiomInfo info) := data.find? a | return some s!"{a} isn't an axiom"
  let t := info.type
  unless t.isAppOfArity ``Eq 3 && t.appArg! == mkConst ``Bool.true do
    return some s!"{a} isn't `_ = true`, as bv_decide's axioms are"
  let lhs := t.appFn!.appArg!
  unless lhs.isAppOfArity ``Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 do
    return some s!"{a} isn't about verifyBVExpr, as bv_decide's axioms are"
  let mut args := #[]
  for arg in lhs.getAppArgs do
    let .const c [] := arg | return some s!"{a} applies verifyBVExpr to something other than a constant"
    let some (.defnInfo d) := data.find? c | return some s!"{a} applies verifyBVExpr to {c}, not a definition"
    if let some k := d.value.getUsedConstants.find? (!inert data ·) then
      return some s!"{a} uses {c}, which is built with {k}, so rerunning it would run more than bv_decide's checker"
    args := args.push d.value
  let built := mkAppN lhs.getAppFn args
  -- Every constant has to be the toolchain's own declaration here too, so what runs is the toolchain's code.
  for k in built.getUsedConstants do
    unless here.contains k && moduleOf here k == moduleOf data k do
      return some s!"{a} uses {k}, which isn't the toolchain's declaration"
  let ok ← evalExpr Bool (mkConst ``Bool) built
  return if ok then none else some s!"{a}'s certificate doesn't check"

/-! ## One theorem -/

def pp (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))

/-- Where a module has to be read from: the toolchain's, `IRLean`'s library, or the run's directory. -/
def homeOf (cfg : Config) (toolchain : String) (m : Name) : String :=
  if [`Init, `Std, `Lean, `Lake].contains m.getRoot then toolchain
  else if m.getRoot == `IRLean then cfg.irleanDir
  else cfg.runDir

/-- Whether a statement may use a constant from module `m`: Lean's, `IRLean`'s, a generated module's or the
model's, and never a proof's or a support module's. -/
def statementModule (cfg : Config) (m : Name) : Bool :=
  [`Init, `Std, `Lean, `IRLean].contains m.getRoot || cfg.generated.contains m || cfg.model.contains m

unsafe def checkTheorem (cfg : Config) (here data : Environment) (t : Theorem) : MetaM (List (String × Json)) := do
  let refuse (reason detail : String) : List (String × Json) :=
    [("ok", toJson false), ("reason", toJson reason), ("detail", toJson detail)]
  let some info := data.find? t.name | return refuse "theorem_not_found" s!"there's no {t.name}"
  unless moduleOf data t.name == some t.module do
    return refuse "theorem_not_found"
      s!"{t.name} is declared in {(moduleOf data t.name).getD `unknown}, not in {t.module}"
  let .thmInfo thm := info | return refuse "not_a_theorem" s!"{t.name} isn't a theorem"
  unless thm.levelParams.isEmpty do return refuse "not_a_theorem" s!"{t.name} has universe parameters"
  for c in thm.type.getUsedConstants do
    let m := (moduleOf data c).getD `unknown
    unless statementModule cfg m do
      return refuse "foreign_constant"
        s!"the statement uses {c}, from {m}, which isn't Lean's, IRLean's, a generated module's or the model's"
  for g in t.about do
    let m := (moduleOf data g).getD `unknown
    unless cfg.generated.contains m && m.isPrefixOf g do
      return refuse "not_about_target" s!"{g} isn't declared in the module ir-lean generated for it, but in {m}"
    unless (data.find? g).any (·.isDefinition) do
      return refuse "not_about_target" s!"{g} isn't a definition ir-lean generated"
    unless thm.type.getUsedConstants.contains g do
      return refuse "not_about_target" s!"{t.name}'s statement doesn't name {g}"
  let axs := axiomsOf data t.name
  if axs.contains ``sorryAx then return refuse "sorry" s!"{t.name} rests on sorryAx"
  for a in axs do
    if standard.contains a then continue
    if let some why ← bvDecideFails here data a then return refuse "disallowed_axiom" why
  let fromModel := thm.type.getUsedConstants.filter fun c => cfg.model.contains ((moduleOf data c).getD `unknown)
  return [("ok", toJson true), ("statement", toJson (← pp thm.type)), ("canonical", toJson (expr thm.type)),
    ("axioms", toJson ((axs.map (·.toString)).qsort (· < ·))),
    ("names", toJson (fromModel.map fun c => s!"{c} ({(moduleOf data c).getD `unknown})"))]

unsafe def check : MetaM Unit := do
  let some path ← IO.getEnv "VERIFY_CLAIMS_CONFIG" | throwError "VERIFY_CLAIMS_CONFIG isn't set"
  let cfg ← match Json.parse (← IO.FS.readFile path) >>= parseConfig with
    | .ok c => pure c
    | .error e => throwError "bad config: {e}"
  let here ← getEnv
  let data ← importModules (cfg.modules.map fun m => { module := m }) {} (loadExts := false)
  let toolchain := (← IO.FS.realPath cfg.toolchainDir).toString
  for m in data.header.moduleNames do
    let at_ := (← IO.FS.realPath (← findOLean m)).toString
    let home := homeOf cfg toolchain m
    unless at_.startsWith (home ++ "/") do
      answer cfg.nonce [("module", toJson m.toString), ("ok", toJson false), ("reason", toJson "module_shadowed"),
        ("detail", toJson s!"{m} is read from {at_}, not from {home}")]
      return
  for t in cfg.theorems do
    let fields ← checkTheorem cfg here data t
    answer cfg.nonce ([("theorem", toJson t.name.toString)] ++ fields)
  answer cfg.nonce [("done", toJson true)]

end VerifyClaims

run_meta unsafe VerifyClaims.check
