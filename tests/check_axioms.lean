import Lean.Meta.Eval
import Std.Tactic.BVDecide.Reflect

/-! Checks a compiled proof module without running any of its code, for `tests/proofs.sh` and `tests/llvm.py`.

Importing a module runs its code: its initializers, and the elaborators and extensions it adds. It also trusts what
the module recorded about itself, such as the axioms of each of its declarations. So the module and everything it
imports are read as data, with `importModules (loadExts := false)`, and every fact here comes from the declarations
themselves, as `tools/verify_check.lean` does.

It reads what to check from the environment:
- `IRLEAN_CHECK_MODULE`, the proof module.
- `IRLEAN_CHECK_GENERATED`, the namespaces ir-lean generated, separated by spaces, if theorems are given. A namespace's
  modules are the one of its name and, for a split translation, those under it.
- `IRLEAN_CHECK_THEOREMS`, lines of a theorem and the generated function it has to be about, such as
  `Llvm.clzsi2_correct CrtClzsi2.clzsi2`. A theorem can be given by its last components.

Every module that isn't Lean's own, from the toolchain's directory, that is the proof, its support modules, the
generated module and `IRLean`, may rest on the standard three axioms and on what `bv_decide` adds, and nothing else. A
`bv_decide` axiom says that `verifyBVExpr formula certificate` is `true`. Its formula and certificate have to be built
from constructors and literals, and the Bool is rerun here, where only the toolchain's code can run. None of those
modules may have `implemented_by` or `extern`, which make compiled code disagree with what the kernel checked. -/
open Lean Meta

namespace CheckAxioms

def moduleIn (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether `c` is the same declaration in both environments: from the same module, and so the same `.olean`. -/
def sameIn (here there : Environment) (c : Name) : Bool :=
  here.contains c && moduleIn here c == moduleIn there c

/-- Whether a module is Lean's own, which the toolchain is trusted for: its `.olean` is the toolchain's, and not one
named like it somewhere else on the search path. -/
def toolchain (lib : System.FilePath) (m : Name) : IO Bool := do
  return [`Init, `Std, `Lean, `Lake].contains m.getRoot &&
    (← IO.FS.realPath (← findOLean m)).toString.startsWith ((← IO.FS.realPath lib).toString ++ "/")

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every axiom `roots` rest on, from the declarations themselves, as `collectAxioms` reads them. -/
def reachableAxioms (env : Environment) (roots : Array Name) : Array Name := Id.run do
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
  return axioms

/-- Whether `n` is named like an axiom `bv_decide` adds. -/
def bvDecideName : Name → Bool
  | .str (.str (.str _ "_native") "bv_decide") ax => ax.startsWith "ax_"
  | _ => false

/-- What a bv_decide formula may be built from: constructors, types and literals. Building one runs no code. -/
def dataConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo _) | some (.inductInfo _) => true
  | _ => [``OfNat.ofNat, ``instOfNatNat, ``BitVec.ofNat].contains c

/-- The Bool an axiom bv_decide adds says is `true`, `verifyBVExpr formula certificate`, with the two replaced by
their values. -/
def bvDecideBool (env : Environment) (n : Name) : Except String Expr := do
  let unlike := s!"not what bv_decide would add: {n}"
  unless bvDecideName n do throw s!"not an allowed axiom: {n}"
  let some (.axiomInfo info) := env.find? n | throw unlike
  let t := info.type
  unless t.isAppOfArity ``Eq 3 && t.appArg! == mkConst ``Bool.true do throw unlike
  let b := t.appFn!.appArg!
  unless b.isAppOfArity ``Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 do throw unlike
  let args ← b.getAppArgs.mapM fun arg => do
    let .const c [] := arg | throw unlike
    let some (.defnInfo d) := env.find? c | throw unlike
    if let some k := d.value.getUsedConstants.find? (!dataConst env ·) then
      throw s!"{unlike}: {c} uses {k}, so rerunning it would run more than bv_decide's checker"
    pure d.value
  return mkAppN b.getAppFn args

/-- A theorem in the proof module, by its full name or its last components. -/
def resolve (env : Environment) (proof : Name) (text : String) : Except String Name := do
  let some idx := env.getModuleIdx? proof | throw s!"no module {proof}"
  let names := env.header.moduleData[idx.toNat]!.constNames
  if names.contains text.toName then return text.toName
  match (names.filter fun c => c.toString.endsWith ("." ++ text)).toList with
  | [n] => return n
  | [] => throw s!"there's no {text} in {proof}"
  | ns => throw s!"{text} could be any of {ns}"

/-- Whether `c` comes from a module ir-lean generated, in the namespace `ns`. -/
def generatedIn (env : Environment) (ns c : Name) : Bool := (moduleIn env c).any (ns.isPrefixOf ·)

/-- That `text` is a theorem about `target`, which comes from the generated modules, as do the other constants in its
statement that are named like they do. -/
def checkTheorem (env : Environment) (proof : Name) (namespaces : List Name) (target : Name) (text : String) :
    Except String Unit := do
  let n ← resolve env proof text
  let some (.thmInfo info) := env.find? n | throw s!"{n} isn't a theorem"
  let some ns := namespaces.find? (·.isPrefixOf target) | throw s!"{target} isn't in a namespace ir-lean generated"
  unless generatedIn env ns target do
    throw s!"{target} isn't in what ir-lean generated for {ns}, so it may have left it out"
  unless info.type.getUsedConstants.contains target do
    throw s!"{n} doesn't mention {target}"
  for c in info.type.getUsedConstants do
    if let some ns := namespaces.find? (·.isPrefixOf c) then
      unless generatedIn env ns c do
        throw s!"{n} mentions {c}, which is named like what ir-lean generated but comes from {moduleIn env c}"

def env? (name : String) : IO (Option String) := do
  return (← IO.getEnv name).filter (!·.isEmpty)

unsafe def check : MetaM String := do
  let some module ← env? "IRLEAN_CHECK_MODULE" | throwError "IRLEAN_CHECK_MODULE isn't set"
  let module := module.toName
  let proof ← importModules #[{ module }] {} (loadExts := false)
  let lib ← getLibDir (← findSysroot)
  let checked ← (List.range proof.header.moduleNames.size).filterMapM fun i => do
    let m := proof.header.moduleNames[i]!
    return if ← toolchain lib m then none else some (m, proof.header.moduleData[i]!)
  -- Compiled code that isn't the declaration the kernel checked.
  for (m, data) in checked do
    for (ext, entries) in data.entries do
      if entries.size > 0 && [`Lean.Compiler.implementedByAttr, `Lean.externAttr].contains ext then
        throwError "{m} uses {if ext == `Lean.externAttr then "extern" else "implemented_by"}, so its compiled \
          code isn't what the kernel checked"
  let roots := checked.foldl (fun acc (_, data) => acc ++ data.constNames) #[]
  let here ← getEnv
  for a in reachableAxioms proof roots do
    if standardAxioms.contains a then continue
    match bvDecideBool proof a with
    | .error e => throwError e
    | .ok b =>
      if let some c := b.getUsedConstants.find? (!sameIn here proof ·) then
        throwError "not what bv_decide would add: {a} uses {c} from {(moduleIn proof c).getD `unknown}"
      unless ← evalExpr Bool (mkConst ``Bool) b do
        throwError "not what bv_decide would add: {a}, whose certificate doesn't check"
  -- What the proof module's own declarations rest on, which is what's reported.
  let some idx := proof.getModuleIdx? module | throwError "no module {module}"
  let count := (reachableAxioms proof proof.header.moduleData[idx.toNat]!.constNames).filter
    (!standardAxioms.contains ·) |>.size
  if let some lines ← env? "IRLEAN_CHECK_THEOREMS" then
    let some generated ← env? "IRLEAN_CHECK_GENERATED" | throwError "IRLEAN_CHECK_GENERATED isn't set"
    let namespaces := (generated.splitOn " ").filter (!·.isEmpty) |>.map String.toName
    for line in lines.splitOn "\n" do
      match line.splitOn " " |>.filter (!·.isEmpty) with
      | [] => pure ()
      | [theorem', target] =>
        if let .error e := checkTheorem proof module namespaces target.toName theorem' then throwError e
      | _ => throwError "a line of IRLEAN_CHECK_THEOREMS is a theorem and a target: {line}"
  return s!"at most the standard three, and {count} from bv_decide"

end CheckAxioms

run_meta do IO.println (← unsafe CheckAxioms.check)
