import IRLean.Vec

/-! Integer operations and value promises on vectors and structs, lane by lane, for the forms `IRLean.Vec` doesn't
have: intrinsics with three operands, intrinsics with two results, division, and `noundef` on values that aren't one
integer or pointer.

LangRef 23.1.3 says of `udiv`, `sdiv`, `urem` and `srem`: "For vectors, if any element of the divisor is zero, the
operation has undefined behavior." Of `noundef`: "If the value representation contains any undefined or poison bits,
the behavior is undefined", so one poison lane, or field, is enough. Of `range`: "For vector-typed parameters, the
range is applied element-wise." The overflow intrinsics return "a structure --- the first element of which is the
sum, and the second element of which is a bit specifying if the unsigned summation resulted in a carry", and LangRef
doesn't spell out their vector forms; lane by lane, a vector of results and a vector of bits, is how LLVM's constant
folder and Alive2 both read them. `tests/vecopcheck.py` checks each form here against both, poison lanes and
undefined behavior included.
-/

namespace IRLean

namespace Vec

@[llvm] def map3 (f : Val w → Val w → Val w → Val v) (a b c : Vec n w) : Vec n v :=
  Vector.ofFn fun i => f a[i] b[i] c[i]

/-- An operation with two results, such as `llvm.uadd.with.overflow`, lane by lane: a vector of each. -/
@[llvm] def map2Pair (f : Val w → Val w → Val u × Val v) (a b : Vec n w) : Vec n u × Vec n v :=
  (Vector.ofFn fun i => (f a[i] b[i]).1, Vector.ofFn fun i => (f a[i] b[i]).2)

/-- An operation that can be undefined, such as `udiv`, lane by lane. The whole is undefined if any lane is, with the
first such lane's reason. -/
@[llvm] def mapOutcome2 (f : Val w → Val w → Outcome (Val v)) (a b : Vec n w) : Outcome (Vec n v) :=
  match (List.finRange n).findSome? fun i =>
      match f a[i] b[i] with
      | some (.ok _) => none
      | r => some r with
  | some (some (.error e)) => some (.error e)
  | some _ => none
  | none => Outcome.ok (Vector.ofFn fun i => match f a[i] b[i] with | some (.ok x) => x | _ => none)

end Vec

/-- Values that can hold poison somewhere: an integer or a pointer, and vectors and structs of them. -/
class Defined (α : Type) where
  /-- Whether no part of the value is poison. -/
  defined : α → Bool

instance : Defined (Option τ) := ⟨Option.isSome⟩
instance : Defined Unit := ⟨fun _ => true⟩
instance [Defined α] : Defined (Vector α n) := ⟨fun v => v.toList.all Defined.defined⟩
instance [Defined α] [Defined β] : Defined (α × β) := ⟨fun p => Defined.defined p.1 && Defined.defined p.2⟩

/-- `noundef` on a vector or a struct: a poison lane or field anywhere is undefined behavior. One integer or
pointer has `IRLean.noundef`. -/
@[llvm, inline] def noundefAll [Defined τ] (x : τ) (k : Outcome α) : Outcome α :=
  if Defined.defined x then k else Outcome.ub .noundefPoison

end IRLean
