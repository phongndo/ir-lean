import IRLean.Int
import IRLean.Mem

/-! Vectors of integers. Each lane is a `Val`, so one lane can be poison without the others, and an
operation on a vector is the scalar operation on each lane. -/

namespace IRLean

abbrev Vec (n w : Nat) := Vector (Val w) n

instance {τ : Type} : HasPoison (Vector (Option τ) n) := ⟨Vector.replicate n none⟩

namespace Vec

@[llvm] def map (f : Val w → Val v) (a : Vec n w) : Vec n v := Vector.map f a

@[llvm] def map2 (f : Val w → Val u → Val v) (a : Vec n w) (b : Vec n u) : Vec n v :=
  Vector.ofFn fun i => f a[i] b[i]

/-- A lane, or poison if there's no such lane. -/
@[llvm] def lane (a : Vec n w) (i : Nat) : Val w :=
  if h : i < n then a[i] else none

/-- Joins consecutive lanes, placing the first lane in the low bits. Poison affects only the
destination lane containing it. `count * w ≤ v` is checked by the emitter's bitcast shape rule. -/
@[llvm] def joinLanes (v : Nat) (a : Vec n w) (start : Nat) : Nat → Val v
  | 0 => some 0#v
  | count + 1 =>
    Val.map₂ (fun lo hi => lo ||| (hi <<< (count * w)))
      (joinLanes v a start count) (Val.map₁ (fun x => x.setWidth v) (lane a (start + count)))

/-- Little-endian integer `bitcast`. The emitter requires equal total size and lane widths where
one divides the other. Splitting copies a lane's poison to all its pieces; joining poisons only
the destination lane containing a poison piece. A scalar is represented as a one-lane vector. -/
@[llvm] def bitcast (m v : Nat) (a : Vec n w) : Vec m v :=
  Vector.ofFn fun i =>
    if w ≤ v then joinLanes v a (i.val * (v / w)) (v / w)
    else Val.map₁ (fun x => (x >>> ((i.val % (w / v)) * v)).setWidth v)
      (lane a (i.val / (w / v)))

/-- `select` with a condition for each lane. -/
@[llvm] def select (c : Vec n 1) (t e : Vec n w) : Vec n w :=
  Vector.ofFn fun i => IRLean.select c[i] t[i] e[i]

@[llvm] def extract (a : Vec n w) (i : Val k) : Val w :=
  match i with
  | none => none
  | some j => lane a j.toNat

/-- An index past the end gives poison in every lane. -/
@[llvm] def insert (a : Vec n w) (x : Val w) (i : Val k) : Vec n w :=
  match i with
  | none => HasPoison.poison
  | some j => if h : j.toNat < n then a.set j.toNat x h else HasPoison.poison

/-- `shufflevector`. Each mask entry picks a lane, counting on through `b`, and `none` is poison. -/
@[llvm] def shuffle (k : Nat) (a b : Vec n w) (mask : Array (Option Nat)) : Vec k w :=
  Vector.ofFn fun i =>
    match mask[i.val]? with
    | some (some j) => if j < n then lane a j else lane b (j - n)
    | _ => none

/-- `llvm.vector.reduce.*`: combines the lanes, starting from the first. -/
@[llvm] def reduce (f : Val w → Val w → Val w) (a : Vec n w) : Val w :=
  match a.toList with
  | [] => none
  | x :: rest => rest.foldl f x

end Vec

namespace Mem

/-- `load` of a vector, whose lanes are a whole number of bytes each. -/
@[llvm] def loadVec (n w : Nat) (m : Mem) (p : PtrVal) (align : Nat) : Outcome (Vec n w) :=
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
@[llvm] def storeVec (m : Mem) (p : PtrVal) (v : Vec n w) (align : Nat) : Outcome Mem :=
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

end IRLean
