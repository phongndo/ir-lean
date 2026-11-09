import IRLean.Lanes

/-! x86's pure bit functions: VPTERNLOG, PSHUFB, and the shifts by an immediate, by a count in a vector, and by a
count in each lane, following the pseudo-code in Intel's Software Developer's Manual.

LangRef 23.1.3 doesn't define target intrinsics, nor what poison does to them. Here a result lane is poison when a
lane it's computed from is, as for `IRLean.X86`'s dot products, and as Alive2 reads each of these: a lane of
`llvm.x86.avx512.pternlog` is poison when that lane of any operand is, whatever the truth table uses, a byte of
PSHUFB when the byte it picks is, even where it's zeroed, and a shift by a count that's poison is poison in every
lane. Where the SDM's pseudo-code reads less than that, this is the more poisonous reading. `tests/vecopcheck.py`
checks each against Alive2, both ways, and LLVM's constant folder with x86's own folds, poison included. -/

namespace IRLean.X86

/-- VPTERNLOG's truth table on bits: bit `j` of the result is bit `4 x[j] + 2 y[j] + z[j]` of `imm`. -/
def ternlogBits (imm : Nat) (x y z : BitVec w) : BitVec w :=
  let pick (k : Nat) (v : BitVec w) := if k &&& 1 == 1 then v else ~~~v
  (List.range 8).foldl
    (fun acc k => if imm.testBit k then acc ||| (pick (k >>> 2) x &&& pick (k >>> 1) y &&& pick k z) else acc)
    0

/-- `llvm.x86.avx512.pternlog.{d,q}`: the truth table `imm` applied to each bit of three vectors. -/
@[llvm] def pternlog (imm : Nat) (a b c : Vec n w) : Vec n w :=
  Vec.map3
    (fun x y z =>
      match x, y, z with
      | some x, some y, some z => some (ternlogBits imm x y z)
      | _, _, _ => none)
    a b c

/-- `llvm.x86.*.pshuf.b`, PSHUFB: byte `i` is 0 if bit 7 of `b[i]` is set, and otherwise the byte of `a` that
`b[i]`'s low four bits pick, in the same 16-byte block as `i`. It's poison if `b[i]` is, or the byte it picks is,
even where bit 7 makes it 0, as Alive2 reads it. The SDM's pseudo-code doesn't read that byte when bit 7 is set,
so this is the more poisonous of the two readings, as for `pternlog`; docs/trust.md lists the choice. -/
@[llvm] def pshufb (a b : Vec n 8) : Vec n 8 :=
  Vector.ofFn fun i =>
    match b.lane i with
    | none => none
    | some s =>
      match a.lane (i.val / 16 * 16 + s.toNat % 16) with
      | none => none
      | some x => if s.getMsbD 0 then some 0 else some x

/-- How each kind of shift treats a count, as the SDM's pseudo-code does: a logical shift by the width or more gives
0, and an arithmetic one shifts in the sign, as if by the width less one. -/
inductive Shift where
  | shl
  | lshr
  | ashr
  deriving Repr, DecidableEq

@[llvm] def Shift.apply : Shift → BitVec w → Nat → BitVec w
  | .shl, x, c => if c < w then x <<< c else 0
  | .lshr, x, c => if c < w then x >>> c else 0
  | .ashr, x, c => x.sshiftRight (min c (w - 1))

/-- `psllv`, `psrlv`, `psrav`: each lane by the count in the same lane of `b`, as an unsigned number. -/
@[llvm] def shiftLanes (s : Shift) (a b : Vec n w) : Vec n w :=
  Vec.map2
    (fun x c =>
      match x, c with
      | some x, some c => some (s.apply x c.toNat)
      | _, _ => none)
    a b

/-- `pslli`, `psrli`, `psrai`: every lane by one count, an unsigned 32-bit number. -/
@[llvm] def shiftImm (s : Shift) (a : Vec n w) (c : Val 32) : Vec n w :=
  match c with
  | none => HasPoison.poison
  | some c => Vec.map (fun x => x.map (s.apply · c.toNat)) a

/-- `psll`, `psrl`, `psra`: every lane by one count, the low 64 bits of `c`, read as an unsigned number from its
first lanes, lowest first. -/
@[llvm] def shiftVec (s : Shift) (a : Vec n w) (c : Vec m u) : Vec n w :=
  let k := 64 / u
  match (List.range k).foldr
      (fun j acc =>
        match c.lane j, acc with
        | some x, some y => some ((y <<< u) ||| x.toNat)
        | _, _ => none)
      (some 0) with
  | none => HasPoison.poison
  | some count => Vec.map (fun x => x.map (s.apply · count)) a

end IRLean.X86
