import LLVMLean.Int
import LLVMLean.Mem

/-! Vectors of integers. Each lane is a `Val`, so one lane can be poison without the others, and an
operation on a vector is the scalar operation on each lane. -/

namespace LLVMLean

abbrev Vec (n w : Nat) := Vector (Val w) n

instance {τ : Type} : HasPoison (Vector (Option τ) n) := ⟨Vector.replicate n none⟩

namespace Vec

@[llvm, inline] def map (f : Val w → Val v) (a : Vec n w) : Vec n v := Vector.map f a

@[llvm, inline] def map2 (f : Val w → Val u → Val v) (a : Vec n w) (b : Vec n u) : Vec n v :=
  Vector.ofFn fun i => f a[i] b[i]

/-- A lane, or poison if there's no such lane. -/
@[llvm, inline] def lane (a : Vec n w) (i : Nat) : Val w :=
  if h : i < n then a[i] else none

/-- `select` with a condition for each lane. -/
@[llvm, inline] def select (c : Vec n 1) (t e : Vec n w) : Vec n w :=
  Vector.ofFn fun i => LLVMLean.select c[i] t[i] e[i]

@[llvm, inline] def extract (a : Vec n w) (i : Val k) : Val w :=
  match i with
  | none => none
  | some j => lane a j.toNat

/-- An index past the end gives poison in every lane. -/
@[llvm, inline] def insert (a : Vec n w) (x : Val w) (i : Val k) : Vec n w :=
  match i with
  | none => HasPoison.poison
  | some j => if h : j.toNat < n then a.set j.toNat x h else HasPoison.poison

/-- `shufflevector`. Each mask entry picks a lane, counting on through `b`, and `none` is poison. -/
@[llvm, inline] def shuffle (k : Nat) (a b : Vec n w) (mask : Array (Option Nat)) : Vec k w :=
  Vector.ofFn fun i =>
    match mask[i.val]? with
    | some (some j) => if j < n then lane a j else lane b (j - n)
    | _ => none

/-- `llvm.vector.reduce.*`: combines the lanes, starting from the first. -/
@[llvm, inline] def reduce (f : Val w → Val w → Val w) (a : Vec n w) : Val w :=
  match a.toList with
  | [] => none
  | x :: rest => rest.foldl f x

end Vec

namespace Mem

/-- `load` of a vector, whose lanes are a whole number of bytes each. -/
@[llvm, inline] def loadVec (n w : Nat) (m : Mem) (p : PtrVal) (align : Nat) : Outcome (Vec n w) :=
  match m.access p (n * (w / 8)) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    match m.check q a false with
    | some e => some (.error e)
    | none =>
      let lanes := (List.range n).map fun i =>
        collect (m.read q a (q.offset.toNat + i * (w / 8)) (w / 8))
      match lanes.findSome? fun l => match l with | .error e => some e | .ok _ => none with
      | some e => Outcome.stop e
      | none =>
        Outcome.ok <| Vector.ofFn fun i =>
          match lanes[i.val]? with
          | some (.ok (some x)) => some (BitVec.ofNat w x)
          | _ => none

/-- `store` of a vector. A poison lane makes that lane's bytes poison. -/
@[llvm, inline] def storeVec (m : Mem) (p : PtrVal) (v : Vec n w) (align : Nat) : Outcome Mem :=
  match m.access p (n * (w / 8)) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    match m.check q a true with
    | some e => some (.error e)
    | none =>
      Outcome.ok <| m.write q a (n * (w / 8)) fun i =>
        match Vec.lane v (i / (w / 8)) with
        | none => .poison
        | some x => intByte x (i % (w / 8))

end Mem

end LLVMLean
