import Lean.Data.Json
import SimplifyAddModel

/-! Runs the `simplifyAddInst` model on cases from `tests/cpp_correspondence.py`, for comparing with `opt`.

`lean --run Driver.lean CASES` reads one JSON case a line and prints one JSON answer a line, with the recursion
budget InstSimplify starts with, `RecursionLimit`, 3. An operand is `{"const": "-1"}`, `"poison"`, `"undef"`,
`{"other": id}`, `{"sub": [id, nuw, nsw, a, b]}`, `{"xor": [id, a, b]}` or `{"add": [id, nuw, nsw, a, b]}`. An
answer is `{"value": ident}`, `"null"` or `{"delegated": callee}`, where an ident is `{"node": id}`,
`{"const": "c"}` with `c` signed, `"poison"` or `"undef"`. This is test code: nothing proved rests on it. -/

open Lean CppCorrespondence.SimplifyAdd

partial def parseOperand (w : Nat) (j : Json) : Except String (Operand w) := do
  match j with
  | .str "poison" => return .poison
  | .str "undef" => return .undef
  | _ =>
  if let .ok c := j.getObjValAs? String "const" then
    let some i := c.toInt? | throw s!"bad constant {c}"
    return .const (BitVec.ofInt w i)
  if let .ok id := j.getObjValAs? Nat "other" then return .other id
  if let .ok (args : Array Json) := j.getObjValAs? (Array Json) "sub" then
    let #[id, nuw, nsw, a, b] := args | throw "sub takes 5"
    return .sub (← id.getNat?) (← nuw.getBool?) (← nsw.getBool?) (← parseOperand w a) (← parseOperand w b)
  if let .ok (args : Array Json) := j.getObjValAs? (Array Json) "add" then
    let #[id, nuw, nsw, a, b] := args | throw "add takes 5"
    return .add (← id.getNat?) (← nuw.getBool?) (← nsw.getBool?) (← parseOperand w a) (← parseOperand w b)
  if let .ok (args : Array Json) := j.getObjValAs? (Array Json) "xor" then
    let #[id, a, b] := args | throw "xor takes 3"
    return .xor (← id.getNat?) (← parseOperand w a) (← parseOperand w b)
  throw s!"bad operand {j.compress}"

def identJson {w : Nat} : Ident w → Json
  | .const c => Json.mkObj [("const", toString c.toInt)]
  | .poison => "poison"
  | .undef => "undef"
  | .node id => Json.mkObj [("node", id)]

def calleeName : Callee → String
  | .constantFold => "constantFold"
  | .simplifyXorInst => "simplifyXorInst"
  | .simplifyAssociativeBinOp => "simplifyAssociativeBinOp"

def resultJson {w : Nat} : Result w → Json
  | .value v => Json.mkObj [("value", identJson v.ident)]
  | .null => "null"
  | .delegated c => Json.mkObj [("delegated", calleeName c)]

def runCase (line : String) : Except String Json := do
  let j ← Json.parse line
  let name ← j.getObjValAs? String "name"
  let w ← j.getObjValAs? Nat "w"
  let op0 ← parseOperand w (← j.getObjVal? "op0")
  let op1 ← parseOperand w (← j.getObjVal? "op1")
  let r := simplifyAddInst op0 op1 (← j.getObjValAs? Bool "nsw") (← j.getObjValAs? Bool "nuw") 3
  return Json.mkObj [("name", name), ("result", resultJson r)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run Driver.lean CASES"; return 2
  for line in (← IO.FS.lines path) do
    if line.isEmpty then continue
    match runCase line with
    | .ok j => IO.println j.compress
    | .error e => IO.eprintln s!"{e}: {line}"; return 1
  return 0
