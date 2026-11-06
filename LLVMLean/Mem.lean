import LLVMLean.Int

/-! Memory. A pointer is an allocation and an offset into it, so an access can only reach the
allocation its pointer came from. Memory is passed explicitly, so functions that don't touch it
keep their simple types. `tests/differential.py` compares this with native code. -/

namespace LLVMLean

/-- A pointer. Allocation 0 never exists, and is where null points. -/
structure Ptr where
  block : Nat
  offset : BitVec 64
  deriving DecidableEq, Repr, Inhabited

namespace Ptr
def null : Ptr := ⟨0, 0#64⟩
end Ptr

/-- An LLVM pointer value. `none` is poison. -/
abbrev PtrVal := Option Ptr

/-- One byte of memory. -/
inductive Byte where
  | uninit
  | poison
  | val (b : BitVec 8)
  /-- Byte `index` of a stored pointer. -/
  | ptr (p : Ptr) (index : Nat)
  deriving Inhabited

structure Alloc where
  size : Nat
  /-- Writing is undefined. This covers a stack object outside its lifetime, which reads as poison:
  its bytes are uninitialized, and nothing can write to them. -/
  readonly : Bool
  bytes : Nat → Byte
  /-- Whether `malloc` returned it, so `free` may take it. -/
  heap : Bool := false
  deriving Inhabited

/-- The state of memory. `base` gives each allocation's address, and is what makes `ptrtoint` and
comparing pointers meaningful. A theorem that holds for every `base` holds for every layout. -/
structure Mem where
  allocs : Nat → Option Alloc
  next : Nat
  base : Nat → BitVec 64
  /-- The current function's `alloca`s, which go away when it returns. -/
  frame : List Nat
  /-- Whether the `malloc` that would make allocation `i` fails. A theorem that holds for every
  `failAlloc` holds whichever calls fail. -/
  failAlloc : Nat → Bool := fun _ => false

instance : Inhabited Mem := ⟨{ allocs := fun _ => none, next := 1, base := fun _ => 0#64, frame := [] }⟩

namespace Mem

/-- Memory with nothing allocated. -/
def empty (base : Nat → BitVec 64) : Mem :=
  { allocs := fun _ => none, next := 1, base := base, frame := [] }

/-- A layout for running code: allocations are aligned and far apart. -/
def spacedOut (block : Nat) : BitVec 64 := BitVec.ofNat 64 (block * 0x100000000)

@[llvm, inline] def setAlloc (m : Mem) (block : Nat) (a : Option Alloc) : Mem :=
  { m with allocs := fun b => if b == block then a else m.allocs b }

/-- A global's initial contents. Values above 255 stand for uninitialized bytes, and bytes past the
end of `init` are zero. -/
def globalBytes (init : Array Nat) (i : Nat) : Byte :=
  match init[i]? with
  | none => Byte.val 0#8
  | some n => if n > 255 then Byte.uninit else Byte.val (BitVec.ofNat 8 n)

/-- Adds a global at allocation `block`. -/
def addGlobal (m : Mem) (block size : Nat) (readonly : Bool) (init : Array Nat) : Mem :=
  { m with
    allocs := fun b =>
      if b == block then
        some { size := size, readonly := readonly, bytes := globalBytes init }
      else m.allocs b
    next := max m.next (block + 1) }

/-- Puts a pointer into a global's initial contents. -/
def addReloc (m : Mem) (block offset : Nat) (target : Ptr) : Mem :=
  match m.allocs block with
  | none => m
  | some a =>
    m.setAlloc block (some { a with
      bytes := fun i => if offset ≤ i ∧ i < offset + 8 then .ptr target (i - offset) else a.bytes i })

/-- Keeps allocations below `next` for functions, whose addresses are allocations that hold nothing
and so can't be read or written. -/
def reserve (m : Mem) (next : Nat) : Mem :=
  { m with next := max m.next next }

/-- A pointer's address. Null is always 0. -/
@[llvm, inline] def addr (m : Mem) (p : Ptr) : BitVec 64 :=
  if p.block == 0 then p.offset else m.base p.block + p.offset

/-- A pointer as an integer: for `ptrtoint` and for comparing pointers. -/
@[llvm, inline] def toVal (m : Mem) : PtrVal → Val 64
  | some p => some (m.addr p)
  | none => none

/-- The allocation an access of `n` bytes at `p` falls in, or the reason it isn't valid. -/
@[llvm, inline] def access (m : Mem) (p : PtrVal) (n align : Nat) : Except UB (Ptr × Alloc) :=
  match p with
  | none => .error .poisonPointer
  | some q =>
    match m.allocs q.block with
    | none => .error .badAccess
    | some a =>
      if q.offset.toNat + n > a.size then .error .badAccess
      else if align != 1 && (m.addr q).toNat % align != 0 then .error .misaligned
      else .ok (q, a)

/-- The bytes of a little-endian integer, or none if any is poison or uninitialized. LLVM calls an
uninitialized read `undef`, and poison is stricter: nothing that depends on it comes out clean, and
branching on it is undefined. So a result that isn't poison here doesn't depend on those bytes.
zlib does this on purpose: `slide_hash` reads uninitialized entries of `prev` and never uses them. -/
def collect : List Byte → Except ModelStop (Option Nat)
  | [] => .ok (some 0)
  | .ptr .. :: _ => .error .pointerBytes
  | .poison :: rest | .uninit :: rest =>
    match collect rest with
    | .error e => .error e
    | .ok _ => .ok none
  | .val b :: rest =>
    match collect rest with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some k) => .ok (some (b.toNat + 256 * k))

@[llvm, inline] def read (a : Alloc) (offset n : Nat) : List Byte :=
  (List.range n).map fun i => a.bytes (offset + i)

/-- `load` of a `w`-bit integer, where `w` is a whole number of bytes. -/
@[llvm, inline] def loadInt (w : Nat) (m : Mem) (p : PtrVal) (align : Nat) : Outcome (Val w) :=
  match m.access p (w / 8) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    match collect (read a q.offset.toNat (w / 8)) with
    | .error e => Outcome.stop e
    | .ok none => Outcome.ok none
    | .ok (some n) => Outcome.ok (some (BitVec.ofNat w n))

/-- Reads back a pointer stored whole, or null from zeroed memory. -/
def assemblePtr (bytes : List Byte) : Except ModelStop PtrVal :=
  match bytes with
  | [] => .error .pointerBytes
  | .ptr p _ :: _ =>
    let whole := bytes.zipIdx.all fun (b, i) =>
      match b with
      | .ptr q j => q == p && j == i
      | _ => false
    if whole then .ok (some p) else .error .pointerBytes
  | _ =>
    match collect bytes with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some 0) => .ok (some Ptr.null)
    | .ok (some _) => .error .pointerBytes

@[llvm, inline] def loadPtr (m : Mem) (p : PtrVal) (align : Nat) : Outcome PtrVal :=
  match m.access p 8 align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    match assemblePtr (read a q.offset.toNat 8) with
    | .error e => Outcome.stop e
    | .ok v => Outcome.ok v

/-- Overwrites `n` bytes starting at `offset`. `f` gets each byte's position in the write. -/
@[llvm, inline] def write (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) : Mem :=
  let o := q.offset.toNat
  m.setAlloc q.block (some { a with
    bytes := fun i => if o ≤ i ∧ i < o + n then f (i - o) else a.bytes i })

/-- Byte `i` of a little-endian integer. -/
@[llvm, inline] def intByte (x : BitVec w) (i : Nat) : Byte :=
  .val (BitVec.ofNat 8 (x.toNat >>> (8 * i)))

/-- `store` of a `w`-bit integer. A poison value makes every byte poison. -/
@[llvm, inline] def storeInt (m : Mem) (p : PtrVal) (v : Val w) (align : Nat) : Outcome Mem :=
  match m.access p (w / 8) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    Outcome.ok <| m.write q a (w / 8) fun i =>
      match v with
      | none => .poison
      | some x => intByte x i

@[llvm, inline] def storePtr (m : Mem) (p : PtrVal) (v : PtrVal) (align : Nat) : Outcome Mem :=
  match m.access p 8 align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    Outcome.ok <| m.write q a 8 fun i =>
      match v with
      | none => .poison
      | some x => .ptr x i

/-- Whether adding `d`, read as a signed number, to the unsigned address `a` goes below zero or past
the top of the address space. -/
@[llvm, inline] def addressWraps (a d : BitVec 64) : Bool :=
  if d.msb then BitVec.ult a (-d) else a.uaddOverflow d

/-- One step of `getelementptr`, given its offset in bytes. The rules are LangRef's:

- `nuw` and `nusw`: adding the offset to the address doesn't wrap, reading the offset as unsigned and
  as signed. `inbounds` implies `nusw`.
- `inbounds`: unless the offset is zero, the base and the result are both inside the allocation or just
  past its end. LLVM also allows this in an allocation that's gone. The model has forgotten its size,
  so that's poison here, which is stricter, and any access through it is undefined either way.

The emitter refuses an `inbounds` whose non-zero index gives a zero offset, so here a zero offset means
the index was zero. -/
@[llvm, inline] def gep (m : Mem) (p : PtrVal) (off : Val 64) (inbounds nusw nuw : Bool := false) : PtrVal :=
  match p, off with
  | some q, some d =>
    let moved : Ptr := { q with offset := q.offset + d }
    if nuw && (m.addr q).uaddOverflow d then none
    else if (inbounds || nusw) && addressWraps (m.addr q) d then none
    else if inbounds && d != 0#64 then
      match m.allocs q.block with
      | some a => if q.offset.toNat ≤ a.size ∧ moved.offset.toNat ≤ a.size then some moved else none
      | none => none
    else some moved
  | _, _ => none

/-- `getelementptr` with several non-zero indices: each offset is a step, checked where it lands, and
the offsets' running total can't wrap either. `go` carries the total. -/
@[llvm] def gepSteps (m : Mem) (p : PtrVal) (offsets : List (Val 64)) (inbounds nusw nuw : Bool := false) :
    PtrVal :=
  go p (some 0#64) offsets
where
  @[llvm] go (p : PtrVal) (total : Val 64) : List (Val 64) → PtrVal
    | [] => p
    | off :: rest =>
      match Val.add total off (nsw := inbounds || nusw) (nuw := nuw) with
      | none => none
      | total' => go (gep m p off inbounds nusw nuw) total' rest

/-- The `nonnull` attribute. -/
@[llvm, inline] def nonnull (m : Mem) (p : PtrVal) : PtrVal :=
  match p with
  | some q => if m.addr q == 0#64 then none else some q
  | none => none

/-- The `align` attribute. -/
@[llvm, inline] def aligned (m : Mem) (align : Nat) (p : PtrVal) : PtrVal :=
  match p with
  | some q => if (m.addr q).toNat % align == 0 then some q else none
  | none => none

/-- The `dereferenceable` attribute: `n` bytes at `p` must be valid to access. -/
@[llvm, inline] def dereferenceable (m : Mem) (p : PtrVal) (n : Nat) (k : Outcome α) : Outcome α :=
  match m.access p n 1 with
  | .error e => Outcome.ub e
  | .ok _ => k

/-- `llvm.assume` with a `nonnull` bundle: a null pointer is undefined. LLVM doesn't say what poison does
here, since the attribute it's equivalent to gives poison and an assume's failure is undefined. -/
@[llvm, inline] def assumeNonnull (m : Mem) (p : PtrVal) (k : Outcome α) : Outcome α :=
  match p with
  | none => Outcome.stop .assumeOnPoison
  | some q => if m.addr q == 0#64 then Outcome.ub .assumeFailed else k

/-- `alloca`: fresh, uninitialized memory in the current function's frame. `dead` is for one that
has `llvm.lifetime.start`, which can't be written until that runs. -/
@[llvm, inline] def alloca (m : Mem) (size : Val 64) (dead : Bool := false) : Outcome (PtrVal × Mem) :=
  match size with
  | none => Outcome.ub .poisonPointer
  | some n =>
    let block := m.next
    Outcome.ok (some ⟨block, 0#64⟩,
      { m with
        allocs := fun b =>
          if b == block then
            some { size := n.toNat, readonly := dead, bytes := fun _ => .uninit }
          else m.allocs b
        next := block + 1
        frame := block :: m.frame })

/-- Runs a function body that uses `alloca`, then frees what it allocated. -/
@[llvm, inline] def withFrame (m : Mem) (body : Mem → Outcome (α × Mem)) : Outcome (α × Mem) :=
  andThen (body { m with frame := [] }) fun (r, m') =>
    Outcome.ok (r, { m' with
      allocs := fun b => if m'.frame.contains b then none else m'.allocs b
      frame := m.frame })

/-- `llvm.lifetime.start` and `.end`: a stack object comes alive or dies, with uninitialized contents
either way. Poison does nothing. -/
@[llvm, inline] def lifetime (m : Mem) (p : PtrVal) (alive : Bool) : Outcome Mem :=
  match p with
  | none => Outcome.ok m
  | some q =>
    match m.allocs q.block with
    | none => Outcome.ok m
    | some a =>
      Outcome.ok (m.setAlloc q.block (some { a with readonly := !alive, bytes := fun _ => .uninit }))

/-- `llvm.memset`. Setting zero bytes does nothing, whatever the pointer is. -/
@[llvm, inline] def memset (m : Mem) (p : PtrVal) (v : Val 8) (n : Val 64) : Outcome Mem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok m else
    match m.access p k.toNat 1 with
    | .error e => Outcome.ub e
    | .ok (q, a) =>
      if a.readonly then Outcome.ub .writeToConstant else
      Outcome.ok <| m.write q a k.toNat fun _ =>
        match v with
        | none => .poison
        | some x => .val x

/-- `llvm.memcpy`. The two ranges must be identical or not overlap. -/
@[llvm, inline] def memcpy (m : Mem) (dst src : PtrVal) (n : Val 64) : Outcome Mem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok m else
    match m.access dst k.toNat 1, m.access src k.toNat 1 with
    | .error e, _ => Outcome.ub e
    | _, .error e => Outcome.ub e
    | .ok (d, da), .ok (s, sa) =>
      if da.readonly then Outcome.ub .writeToConstant else
      let dOff := d.offset.toNat
      let sOff := s.offset.toNat
      if d.block == s.block && dOff != sOff && dOff < sOff + k.toNat && sOff < dOff + k.toNat then
        Outcome.ub .overlappingCopy
      else
        Outcome.ok <| m.write d da k.toNat fun i => sa.bytes (sOff + i)

/-- C's `malloc`, which can fail. -/
def malloc (size : Val 64) (m : Mem) : Outcome (PtrVal × Mem) :=
  match size with
  | none => Outcome.ub .noundefPoison
  | some n =>
    let block := m.next
    if m.failAlloc block then Outcome.ok (some Ptr.null, { m with next := block + 1 }) else
    Outcome.ok (some ⟨block, 0#64⟩,
      { m with
        allocs := fun b =>
          if b == block then
            some { size := n.toNat, readonly := false, bytes := fun _ => .uninit, heap := true }
          else m.allocs b
        next := block + 1 })

/-- C's `free`, which does nothing to null. -/
def free (p : PtrVal) (m : Mem) : Outcome (Unit × Mem) :=
  match p with
  | none => Outcome.ub .noundefPoison
  | some q =>
    if q == Ptr.null then Outcome.ok ((), m) else
    match m.allocs q.block with
    | some a =>
      if a.heap && q.offset == 0#64 then Outcome.ok ((), m.setAlloc q.block none)
      else Outcome.ub .badFree
    | none => Outcome.ub .badFree

/-- How many bytes from offset `o` come before a zero byte, looking at `fuel` bytes at most. -/
def strlenFrom (a : Alloc) : (fuel o : Nat) → Except Stop Nat
  | 0, _ => .error (.undefined .badAccess)
  | fuel + 1, o =>
    match a.bytes o with
    | .val b =>
      if b == 0#8 then .ok 0 else
      match strlenFrom a fuel (o + 1) with
      | .ok n => .ok (n + 1)
      | .error e => .error e
    | .uninit => .error (.model .readUninit)
    | .poison => .error (.undefined .noundefPoison)
    | .ptr .. => .error (.model .pointerBytes)

/-- C's `strlen`: running off the end of the allocation is undefined. -/
def strlen (p : PtrVal) (m : Mem) : Outcome (Val 64 × Mem) :=
  match p with
  | none => Outcome.ub .noundefPoison
  | some q =>
    match m.allocs q.block with
    | none => Outcome.ub .badAccess
    | some a =>
      match strlenFrom a (a.size - q.offset.toNat) q.offset.toNat with
      | .ok n => Outcome.ok (some (BitVec.ofNat 64 n), m)
      | .error e => some (.error e)

end Mem

section Monotone
open Lean.Order

variable {γ : Sort _} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem Mem.monotone_withFrame (m : Mem) (k : γ → Mem → Outcome (α × Mem))
    (hk : monotone k) : monotone fun g => Mem.withFrame m (k g) := by
  intro g g' h
  have h1 := hk g g' h { m with frame := [] }
  simp only [Mem.withFrame, andThen]
  revert h1
  generalize k g _ = a
  generalize k g' _ = b
  intro h1
  cases h1 with
  | bot => exact FlatOrder.rel.bot
  | refl => exact FlatOrder.rel.refl

@[partial_fixpoint_monotone]
theorem Mem.monotone_dereferenceable (m : Mem) (p : PtrVal) (n : Nat) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => Mem.dereferenceable m p n (k g) := by
  intro g g' h
  simp only [Mem.dereferenceable]
  split
  · exact FlatOrder.rel.refl
  · exact hk g g' h

@[partial_fixpoint_monotone]
theorem Mem.monotone_assumeNonnull (m : Mem) (p : PtrVal) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => Mem.assumeNonnull m p (k g) := by
  intro g g' h
  simp only [Mem.assumeNonnull]
  split
  · exact FlatOrder.rel.refl
  · split
    · exact FlatOrder.rel.refl
    · exact hk g g' h

end Monotone

end LLVMLean
