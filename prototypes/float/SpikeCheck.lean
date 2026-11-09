import FloatSpike

/-! Checks `FloatSpike` against two independent references, run with `lean --run`:

- Lean's own `Float.Model`, the logical model of floats in the toolchain's `Init`, on every pair of values of
  small formats. It has one NaN, positive and quiet with a zero payload, which is what `FloatSpike` gives when the
  NaN choice is 0.
- The processor, through Lean's `Float` and `Float32`, on random and edge-case pairs, comparing bits where the result
  isn't a NaN and requiring a NaN where it is.

Exits 1 on the first few disagreements it prints. -/

open FloatSpike Float.Model

def spec (e m : Nat) (he : 2 ≤ e := by decide) (hm : 0 < m := by decide) : Format :=
  { exponentBits := e, mantissaBitsWithoutImplicit := m, he, hm }

/-- The model's predicate for `fcmp`, from `Float.Model`'s ordering. -/
def specCmp (pred : Nat) (o : Option Ordering) : Bool :=
  match o with
  | none => pred &&& 8 != 0
  | some .eq => pred &&& 1 != 0
  | some .gt => pred &&& 2 != 0
  | some .lt => pred &&& 4 != 0

def checkFormat (e m : Nat) (f : Format) (he : f.numBits = 1 + e + m) : IO Nat := do
  let n := 1 + e + m
  let mut bad := 0
  for i in List.range (2 ^ n) do
    for j in List.range (2 ^ n) do
      let a := BitVec.ofNat n i
      let b := BitVec.ofNat n j
      let ua := UnpackedFloat.unpack f (he ▸ a)
      let ub := UnpackedFloat.unpack f (he ▸ b)
      let ops : List (String × BitVec n × BitVec f.numBits) :=
        [("fadd", fadd (e := e) (m := m) 0 a b, UnpackedFloat.pack f (UnpackedFloat.add f ua ub)),
         ("fsub", fsub (e := e) (m := m) 0 a b, UnpackedFloat.pack f (UnpackedFloat.sub f ua ub)),
         ("fmul", fmul (e := e) (m := m) 0 a b, UnpackedFloat.pack f (UnpackedFloat.mul f ua ub)),
         ("fdiv", fdiv (e := e) (m := m) 0 a b, UnpackedFloat.pack f (UnpackedFloat.div f ua ub))]
      for (name, got, want) in ops do
        if got.toNat != want.toNat then
          bad := bad + 1
          if bad ≤ 10 then
            IO.println s!"E{e}M{m} {name} {a.toNat} {b.toNat}: model {got.toNat}, Float.Model {want.toNat}"
      for pred in List.range 16 do
        let got := fcmp (e := e) (m := m) (BitVec.ofNat 4 pred) a b
        let want := specCmp pred (UnpackedFloat.compare ua ub)
        if got != want then
          bad := bad + 1
          if bad ≤ 10 then
            IO.println s!"E{e}M{m} fcmp {pred} {a.toNat} {b.toNat}: model {got}, Float.Model {want}"
  IO.println s!"E{e}M{m}: every pair, {bad} disagreements"
  return bad

/-- Bits that say the most: zeros, the smallest and largest subnormals and normals, one, infinities and NaNs. -/
def edges (e m : Nat) : List Nat :=
  let n := 1 + e + m
  let pos := [0, 1, 2, 2 ^ m - 1, 2 ^ m, 2 ^ m + 1, (2 ^ (e - 1) - 1) * 2 ^ m, (2 ^ (e - 1) - 1) * 2 ^ m + 1,
    (2 ^ e - 2) * 2 ^ m + (2 ^ m - 1), (2 ^ e - 1) * 2 ^ m, (2 ^ e - 1) * 2 ^ m + 1,
    (2 ^ e - 1) * 2 ^ m + 2 ^ (m - 1)]
  pos ++ pos.map (· + 2 ^ (n - 1))

def isNaNBits (e m : Nat) (x : Nat) : Bool :=
  (x >>> m) % 2 ^ e == 2 ^ e - 1 && x % 2 ^ m != 0

/-- Against the processor. `hw` is the processor's operation on bits. -/
def checkHardware (e m : Nat) (name : String) (op : BitVec (1 + e + m) → BitVec (1 + e + m) → BitVec (1 + e + m))
    (hw : Nat → Nat → Nat) (count : Nat) (seed : Nat) : IO Nat := do
  let n := 1 + e + m
  let mut gen := mkStdGen seed
  let mut bad := 0
  let es := edges e m
  for k in List.range count do
    let (r1, g1) := randNat gen 0 (2 ^ n - 1)
    let (r2, g2) := randNat g1 0 (2 ^ n - 1)
    let (c, g3) := randNat g2 0 3
    gen := g3
    let a := if c == 0 then es[k % es.length]! else r1
    let b := if c == 1 then es[(k / es.length) % es.length]! else r2
    let got := (op (BitVec.ofNat n a) (BitVec.ofNat n b)).toNat
    let want := hw a b
    let ok := if isNaNBits e m want then isNaNBits e m got else got == want
    if !ok then
      bad := bad + 1
      if bad ≤ 10 then IO.println s!"E{e}M{m} {name} {a} {b}: model {got}, processor {want}"
  IO.println s!"E{e}M{m} {name}: {count} pairs against the processor, {bad} disagreements"
  return bad

def f64 (op : Float → Float → Float) (a b : Nat) : Nat :=
  (op (Float.ofBits (UInt64.ofNat a)) (Float.ofBits (UInt64.ofNat b))).toBits.toNat

def f32 (op : Float32 → Float32 → Float32) (a b : Nat) : Nat :=
  (op (Float32.ofBits (UInt32.ofNat a)) (Float32.ofBits (UInt32.ofNat b))).toBits.toNat

def main (args : List String) : IO UInt32 := do
  let count := (args.head? >>= String.toNat?).getD 20000
  let mut bad := 0
  bad := bad + (← checkFormat 2 3 (spec 2 3) rfl)
  bad := bad + (← checkFormat 3 2 (spec 3 2) rfl)
  bad := bad + (← checkFormat 4 3 (spec 4 3) rfl)
  bad := bad + (← checkFormat 5 2 (spec 5 2) rfl)
  bad := bad + (← checkFormat 3 4 (spec 3 4) rfl)
  for (name, op, h64, h32) in [
      ("fadd", @fadd 11 52 0, f64 (· + ·), f32 (· + ·)),
      ("fsub", @fsub 11 52 0, f64 (· - ·), f32 (· - ·)),
      ("fmul", @fmul 11 52 0, f64 (· * ·), f32 (· * ·)),
      ("fdiv", @fdiv 11 52 0, f64 (· / ·), f32 (· / ·))] do
    bad := bad + (← checkHardware 11 52 name op h64 count 1)
    let op32 : BitVec (1 + 8 + 23) → BitVec (1 + 8 + 23) → BitVec (1 + 8 + 23) :=
      match name with
      | "fadd" => fadd 0 | "fsub" => fsub 0 | "fmul" => fmul 0 | _ => fdiv 0
    bad := bad + (← checkHardware 8 23 name op32 h32 count 2)
  return if bad == 0 then 0 else 1
