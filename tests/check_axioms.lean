import Lean
import MODULE
open Lean Meta

def bvDecideResult? (env : Environment) : Name → Option Expr
  | n@(.str (.str (.str _ "_native") "bv_decide") ax) =>
    if ax.startsWith "ax_" then
      match env.find? n with
      | some (.axiomInfo info) =>
        if info.type.isAppOfArity ``Eq 3 && info.type.appArg! == mkConst ``Bool.true then
          some info.type.appFn!.appArg!
        else none
      | _ => none
    else none
  | _ => none

run_meta do
  let env ← getEnv
  let some index := env.getModuleIdx? `MODULE | throwError "no module MODULE"
  let mut axioms : NameSet := {}
  for declaration in env.header.moduleData[index.toNat]!.constNames do
    for axiom' in ← collectAxioms declaration do
      axioms := axioms.insert axiom'
  let mut count : Nat := 0
  for axiom' in axioms do
    if [``propext, ``Classical.choice, ``Quot.sound].contains axiom' then continue
    let some result := bvDecideResult? env axiom' | throwError "not an allowed axiom: {axiom'}"
    match ← nativeEqTrue `bv_decide result with
    | .success _ => count := count + 1
    | .notTrue => throwError "not what bv_decide would add: {axiom'}"
  IO.println s!"at most the standard three, and {count} from bv_decide"
