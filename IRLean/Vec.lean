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

/-! `bitcast` between vectors of integers. LangRef 23.1.3, "'`bitcast .. to`' Instruction", Semantics: "The
conversion is done as if the `value` had been stored to memory and read back as type `ty2`", and "`bitcast <2 x i8>
<value> to i16` puts element zero of the vector in the least significant bits of the i16 for little-endian". So lanes
are laid end to end, the first lowest, and the emitter refuses a big-endian module. For poison, its Poison Values
examples store a poison `i32` and read it back as `i16` and as `i64`, and both are poison, so a lane of the result is
poison exactly when a lane it shares bits with is. `tests/x86check.py` checks both against Alive2 and LLVM's constant
folder, poison included. -/

/-- `bitcast` to `k` times as many lanes, each `1 / k` as wide: lane `i` is the bits of lane `i / k` from
`v * (i % k)` up. It's poison if that lane is. -/
@[llvm] def split (m v k : Nat) (a : Vec n w) : Vec m v :=
  Vector.ofFn fun i =>
    match a.lane (i / k) with
    | some x => some (x.extractLsb' (v * (i.val % k)) v)
    | none => none

/-- `bitcast` to `1 / k` as many lanes, each `k` times as wide: lane `i` joins lanes `k * i` to
`k * i + k - 1`, the first lowest. It's poison if any of them is. -/
@[llvm] def join (m v k : Nat) (a : Vec n w) : Vec m v :=
  Vector.ofFn fun i =>
    (List.range k).foldr
      (fun j acc =>
        match a.lane (k * i + j), acc with
        | some x, some y => some ((y <<< w) ||| x.setWidth v)
        | _, _ => none)
      (some 0#v)

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
