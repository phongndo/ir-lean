import IRLean.Mem

/-! # LLVM's IR in memory, as its matchers read it

BIND-04 for reading IR, gate B1 of `docs/binding-approach.md`: what bytes in IRLean's memory mean as LLVM's own
objects, so a theorem about a compiled matcher, which reads those bytes, is a theorem about the IR they hold. It covers
`Value`, `Use`, `ConstantInt` with its `APInt`, and `Type`, at `llvmorg-23.1.3` on x86-64, as far as the compiled
`PatternMatch` matchers read them:

- a `Value`'s ID, the byte at offset 0, and its `Type *`, at offset 8;
- a `BinaryOperator`'s two operands, the `Value *` of each `Use`, which come before the object, at offsets -64 and -32;
- a `ConstantInt`'s value, up to 64 bits, the word of its `APInt` at offset 24, and its width at offset 32;
- a `Type`'s ID, the low byte of the word at offset 8, and an `IntegerType`'s width, the rest of that word.

`Graph` is the IR the matchers can see, and `View M G` says memory `M` holds it. `View.keep` says a change to memory
that leaves the bytes `G` reads alone leaves `G` held. Each constructor a small pass calls, `ConstantInt::get`,
`PoisonValue::get` and `BinaryOperator::Create`, is stated as what it does to memory, and proved to keep the view and
add what it made: `View.constantIntGet`, `View.poisonGet` and `View.binOpCreate`. The `View.load_*` lemmas say what
each read the compiled code makes gives.

What this trusts, and where it's checked:

- **The layout.** The offsets and IDs in `Layout` are read from the pinned headers. `tests/llvm_heap.sh` prints them
  from this file and builds `tests/llvm_heap/layout_probe.cpp` with them, against the pinned `libLLVM`, which checks
  each on objects that library builds. A wrong one would make every theorem using the view say nothing about real
  heaps, rather than something false.
- **What each constructor does.** `ConstantIntGet`, `PoisonGet` and `BinOpCreate` are specifications, not
  translations of `Constants.cpp` and `Instructions.cpp`. The probe checks each on the pinned `libLLVM`, finitely:
  the bytes of the object made, that the same constant comes back for the same value, and that the bytes the view
  reads of every object already there are unchanged.
- **`APInt`'s clean words.** `APInt` keeps the bits above its width 0, and the compiled matchers rely on it:
  `m_ZeroInt` compares the whole word with 0. A release build doesn't keep it when a caller breaks
  `ConstantInt::get`'s precondition: `ConstantInt::get(i1, 7)` holds the word 7, #74's probe found. So the view
  describes only clean words, `View.constantIntGet` needs the precondition as a hypothesis, `hX`, and
  `dirty_not_constInt` shows a dirty word is no `ConstantInt` the view can describe. A theorem about a heap with one
  says nothing about it.

Not covered: use lists, which `m_OneUse` reads and only `BinaryOperator::Create` writes here, `BasicBlock`,
`Instruction`'s other fields and flags, vectors and their constants, constant expressions, values over 64 bits, and
writing IR, which is gate B4. -/

set_option linter.unusedSimpArgs false

namespace IRLean.LLVMHeap

open IRLean

/-! ## The layout -/

/-! Offsets and IDs at `llvmorg-23.1.3` on x86-64, from `llvm/IR/Value.h`, `Use.h`, `Constants.h`, `ADT/APInt.h`,
`Type.h` and `Instruction.def`. `tests/llvm_heap/layout_probe.cpp` checks each on the pinned `libLLVM`. -/

namespace Layout
/-- `Value::SubclassID`, a byte. -/
abbrev valueID : Nat := 0
/-- `Value::VTy`, the value's `Type *`. -/
abbrev valueType : Nat := 8
/-- `Value::UseList`, the first `Use` of the value. Nothing in the view reads it. -/
abbrev valueUseList : Nat := 16
abbrev valueSize : Nat := 24
/-- `Use::Val`, the `Value *` used. -/
abbrev useVal : Nat := 0
/-- `Use::Prev`, which `Use::addToList` writes in the `Use` it puts this one before. -/
abbrev usePrev : Nat := 16
abbrev useSize : Nat := 32
/-- `ConstantInt::Val.U`: the value's word, up to 64 bits. -/
abbrev constWord : Nat := 24
/-- `ConstantInt::Val.BitWidth`. -/
abbrev constWidth : Nat := 32
abbrev constSize : Nat := 40
abbrev binOpSize : Nat := 72
/-- The word of a `Type` holding its `ID` in the low byte, and `SubclassData` above, an `IntegerType`'s width. -/
abbrev typeWord : Nat := 8
abbrev typeSize : Nat := 24
abbrev constantIntVal : Nat := 5
abbrev poisonValueVal : Nat := 1
abbrev instructionVal : Nat := 30
abbrev integerTyID : Nat := 12
abbrev fixedVectorTyID : Nat := 18
abbrev scalableVectorTyID : Nat := 19

/-- Every fact above, by name, for `tests/llvm_heap.sh` to give the probe. -/
def all : List (String × Nat) :=
  [("VALUE_ID", valueID), ("VALUE_TYPE", valueType), ("VALUE_USE_LIST", valueUseList), ("VALUE_SIZE", valueSize),
   ("USE_VAL", useVal), ("USE_PREV", usePrev), ("USE_SIZE", useSize), ("CONST_WORD", constWord),
   ("CONST_WIDTH", constWidth), ("CONST_SIZE", constSize), ("BINOP_SIZE", binOpSize), ("TYPE_WORD", typeWord),
   ("TYPE_SIZE", typeSize), ("CONSTANT_INT_VAL", constantIntVal), ("POISON_VALUE_VAL", poisonValueVal),
   ("INSTRUCTION_VAL", instructionVal), ("INTEGER_TY_ID", integerTyID), ("FIXED_VECTOR_TY_ID", fixedVectorTyID),
   ("SCALABLE_VECTOR_TY_ID", scalableVectorTyID)]
end Layout

/-- Writes the layout's numbers out, so `omega` can use them. -/
macro "llvm_layout" : tactic => `(tactic| try simp only [Layout.valueID, Layout.valueType, Layout.valueUseList,
  Layout.valueSize, Layout.useVal, Layout.usePrev, Layout.useSize, Layout.constWord, Layout.constWidth,
  Layout.constSize, Layout.binOpSize, Layout.typeWord, Layout.typeSize, Layout.constantIntVal,
  Layout.poisonValueVal, Layout.instructionVal, Layout.integerTyID, Layout.fixedVectorTyID,
  Layout.scalableVectorTyID] at *)

/-- The binary operators of `Instruction.def`. -/
inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem | shl | lshr | ashr | and | or | xor
  deriving DecidableEq, Repr

/-- Each one's `Instruction::BinaryOps` number. A binary operator's value ID is `Value::InstructionVal` plus it. -/
def BinOp.opcode : BinOp → Nat
  | .add => 14 | .sub => 16 | .mul => 18 | .udiv => 20 | .sdiv => 21 | .urem => 23 | .srem => 24
  | .shl => 26 | .lshr => 27 | .ashr => 28 | .and => 29 | .or => 30 | .xor => 31

theorem BinOp.opcode_range (op : BinOp) : 14 ≤ op.opcode ∧ op.opcode < 32 := by cases op <;> decide

/-- Every operator by name, for `tests/llvm_heap.sh` to give the probe its opcode. -/
def BinOp.all : List (String × BinOp) :=
  [("ADD", .add), ("SUB", .sub), ("MUL", .mul), ("UDIV", .udiv), ("SDIV", .sdiv), ("UREM", .urem), ("SREM", .srem),
   ("SHL", .shl), ("LSHR", .lshr), ("ASHR", .ashr), ("AND", .and), ("OR", .or), ("XOR", .xor)]

/-! ## What the matchers see -/

/-- Where an object is: an allocation, and the offset of the object in it. A `Value *` points there. -/
abbrev Loc := Nat × Nat

/-- The pointer to an object, with no tags. -/
abbrev ptrOf (l : Loc) : Ptr := ⟨l.1, BitVec.ofNat 64 l.2, []⟩

/-- A type, as far as the matchers read it. -/
inductive Ty where
  /-- `IntegerType`, of width `w`. -/
  | int (w : Nat)
  /-- `FixedVectorType`, or `ScalableVectorType` if `scalable`. -/
  | vector (scalable : Bool)
  /-- Any other type, with its type ID. -/
  | other (id : Nat)

/-- A value, as far as the matchers read it. -/
inductive Obj where
  /-- A `ConstantInt` of `w` bits, at most 64, holding `v`. -/
  | constInt (w : Nat) (v : BitVec w)
  /-- A `PoisonValue`. -/
  | poison
  /-- A `BinaryOperator`, whose operands are the values at `a` and `b`. -/
  | binOp (op : BinOp) (a b : Loc)
  /-- Any other value, with its value ID: an argument, `undef`, another instruction. -/
  | other (id : Nat)

/-- The value ID, `Value::SubclassID`. -/
def Obj.id : Obj → Nat
  | .constInt .. => Layout.constantIntVal
  | .poison => Layout.poisonValueVal
  | .binOp op .. => Layout.instructionVal + op.opcode
  | .other id => id

/-- Where an object at offset `o` starts: a `BinaryOperator`'s two `Use`s come before it. -/
def Obj.lo (o : Nat) : Obj → Nat
  | .binOp .. => o - 2 * Layout.useSize
  | _ => o

/-- Where it ends. -/
def Obj.hi (o : Nat) : Obj → Nat
  | .constInt .. => o + Layout.constSize
  | .binOp .. => o + Layout.binOpSize
  | _ => o + Layout.valueSize

/-- The bytes the view reads of an object at offset `o`: its ID and type, and a `ConstantInt`'s word and width, or a
`BinaryOperator`'s operands. -/
def Obj.reads (o : Nat) : Obj → Nat → Prop
  | .constInt .., i => i = o ∨ (o + 8 ≤ i ∧ i < o + 16) ∨ (o + 24 ≤ i ∧ i < o + 36)
  | .binOp .., i => i = o ∨ (o + 8 ≤ i ∧ i < o + 16) ∨ (o - 64 ≤ i ∧ i < o - 56) ∨ (o - 32 ≤ i ∧ i < o - 24)
  | _, i => i = o ∨ (o + 8 ≤ i ∧ i < o + 16)

/-- The bytes the view reads of a type at offset `o`: the word with its ID and width. -/
def Ty.reads (o i : Nat) : Prop := o + 8 ≤ i ∧ i < o + 12

/-- The IR the matchers can see: each value's object and where its type is, and each type. -/
structure Graph where
  objs : Loc → Option (Obj × Loc)
  tys : Loc → Option Ty

/-- Byte `i` of allocation `b` is one the view reads. -/
def Graph.Reads (G : Graph) (b i : Nat) : Prop :=
  (∃ l e, G.objs l = some e ∧ l.1 = b ∧ e.1.reads l.2 i) ∨ (∃ t ty, G.tys t = some ty ∧ t.1 = b ∧ Ty.reads t.2 i)

/-- An entry of the graph at `l` spans bytes `lo` to `hi` of its allocation. -/
def Graph.Spans (G : Graph) (l : Loc) (lo hi : Nat) : Prop :=
  (∃ e, G.objs l = some e ∧ lo = e.1.lo l.2 ∧ hi = e.1.hi l.2) ∨
    (∃ ty, G.tys l = some ty ∧ lo = l.2 ∧ hi = l.2 + Layout.typeSize)

/-- The graph with the value at `r` added, or replaced. -/
def Graph.addObj (G : Graph) (r : Loc) (e : Obj × Loc) : Graph :=
  { G with objs := fun l => if l = r then some e else G.objs l }

@[simp] theorem Graph.addObj_self (G : Graph) (r : Loc) (e : Obj × Loc) : (G.addObj r e).objs r = some e := by
  simp [Graph.addObj]

@[simp] theorem Graph.addObj_ne (G : Graph) {l r : Loc} (e : Obj × Loc) (h : l ≠ r) :
    (G.addObj r e).objs l = G.objs l := by
  simp [Graph.addObj, h]

@[simp] theorem Graph.addObj_tys (G : Graph) (r : Loc) (e : Obj × Loc) : (G.addObj r e).tys = G.tys := rfl

/-! ## What memory holds -/

/-- Allocation `b` is `a`, where every access the compiled code makes into it is valid: not null, aligned to 8 from
its start, and not crossing the top of the address space. -/
structure Placed (M : Mem) (b : Nat) (a : Alloc) : Prop where
  alloc : M.allocs b = some a
  ne : b ≠ 0
  base_pos : 0 < (M.base b).toNat
  base_align : (M.base b).toNat % 8 = 0
  fits : (M.base b).toNat + a.size < 2 ^ 64
  size : a.size < 2 ^ 63

/-- Bytes `o` to `o + 8` hold the pointer `p`, stored whole. -/
def PtrAt (a : Alloc) (o : Nat) (p : Ptr) : Prop := ∀ i, i < 8 → a.bytes (o + i) = .ptr p i

/-- Bytes `o` to `o + n` hold `x`, little-endian. -/
def IntAt (a : Alloc) (o : Nat) (x : BitVec w) (n : Nat) : Prop := ∀ i, i < n → a.bytes (o + i) = Mem.intByte x i

/-- An `IntegerType`'s word: its width above the type ID. -/
def intTypeWord (w : Nat) : BitVec 32 := BitVec.ofNat 32 (w * 256 + Layout.integerTyID)

/-- What the bytes of a type at `o` say. -/
def Ty.bytes (a : Alloc) (o : Nat) : Ty → Prop
  | .int w => 0 < w ∧ w < 2 ^ 24 ∧ IntAt a (o + Layout.typeWord) (intTypeWord w) 4
  | .vector s =>
    a.bytes (o + Layout.typeWord) =
      .val (BitVec.ofNat 8 (if s then Layout.scalableVectorTyID else Layout.fixedVectorTyID))
  | .other id =>
    id < 256 ∧ id ≠ Layout.integerTyID ∧ id ≠ Layout.fixedVectorTyID ∧ id ≠ Layout.scalableVectorTyID ∧
      a.bytes (o + Layout.typeWord) = .val (BitVec.ofNat 8 id)

/-- What the bytes of an object at `o` say, beyond its ID and type. -/
def Obj.bytes (a : Alloc) (o : Nat) : Obj → Prop
  | .constInt w v =>
    0 < w ∧ w ≤ 64 ∧ IntAt a (o + Layout.constWord) (v.setWidth 64) 8 ∧
      IntAt a (o + Layout.constWidth) (BitVec.ofNat 32 w) 4
  | .poison => True
  | .binOp _ x y =>
    2 * Layout.useSize ≤ o ∧ PtrAt a (o - 2 * Layout.useSize) (ptrOf x) ∧ PtrAt a (o - Layout.useSize) (ptrOf y)
  | .other id =>
    id < 256 ∧ id ≠ Layout.constantIntVal ∧ id ≠ Layout.poisonValueVal ∧
      ¬ (Layout.instructionVal + 14 ≤ id ∧ id < Layout.instructionVal + 32)

/-- Memory holds the type `ty` at `t`. -/
def HoldsTy (M : Mem) (t : Loc) (ty : Ty) : Prop :=
  ∃ a, Placed M t.1 a ∧ t.2 % 8 = 0 ∧ t.2 + Layout.typeSize ≤ a.size ∧ ty.bytes a t.2

/-- Memory holds the value `e.1`, of the type at `e.2`, at `l`. -/
def Holds (M : Mem) (l : Loc) (e : Obj × Loc) : Prop :=
  ∃ a, Placed M l.1 a ∧ l.2 % 8 = 0 ∧ e.1.hi l.2 ≤ a.size ∧
    a.bytes (l.2 + Layout.valueID) = .val (BitVec.ofNat 8 e.1.id) ∧
    PtrAt a (l.2 + Layout.valueType) (ptrOf e.2) ∧ e.1.bytes a l.2

/-- **Memory `M` holds the IR `G`, as the matchers read it.** Every value and type is where `G` says, laid out as
above. Each value's type is in `G`, a `ConstantInt`'s is an `IntegerType` of its width, and a binary operator's
operands are in `G`, of its type. No two entries overlap, and no two values share an address, so `m_Specific`, which
compares pointers, compares locations. Nothing running limits what may be read. -/
structure View (M : Mem) (G : Graph) : Prop where
  objs : ∀ l e, G.objs l = some e → Holds M l e
  tys : ∀ t ty, G.tys t = some ty → HoldsTy M t ty
  typed : ∀ l e, G.objs l = some e → G.tys e.2 ≠ none
  ints : ∀ l w v t, G.objs l = some (.constInt w v, t) → G.tys t = some (.int w)
  operands : ∀ l op x y t, G.objs l = some (.binOp op x y, t) →
    (∃ o, G.objs x = some (o, t)) ∧ (∃ o, G.objs y = some (o, t))
  one : ∀ l, G.objs l = none ∨ G.tys l = none
  apart : ∀ l lo hi l' lo' hi', G.Spans l lo hi → G.Spans l' lo' hi' → l ≠ l' → l.1 = l'.1 → hi ≤ lo' ∨ hi' ≤ lo
  distinct : ∀ l e l' e', G.objs l = some e → G.objs l' = some e' →
    M.addr (ptrOf l) = M.addr (ptrOf l') → l = l'
  calls : M.calls = []

/-! ## Changes that keep the view -/

/-- `M'` is `M` with every byte `S` names as it was, in an allocation still there at the same size, the same
addresses, and the same calls running. An allocation `S` names no byte of, such as a map's old buckets, can be freed,
and new allocations can be anything. -/
structure Keeps (M M' : Mem) (S : Nat → Nat → Prop) : Prop where
  allocs : ∀ b a, M.allocs b = some a → (∃ i, i < a.size ∧ S b i) →
    ∃ a', M'.allocs b = some a' ∧ a'.size = a.size ∧ ∀ i, S b i → a'.bytes i = a.bytes i
  base : M'.base = M.base
  calls : M'.calls = M.calls

theorem Placed.keep {M M' : Mem} {S : Nat → Nat → Prop} {b : Nat} {a : Alloc} (P : Placed M b a)
    (K : Keeps M M' S) (hS : ∃ i, i < a.size ∧ S b i) :
    ∃ a', Placed M' b a' ∧ a'.size = a.size ∧ ∀ i, S b i → a'.bytes i = a.bytes i := by
  obtain ⟨a', h, hs, hb⟩ := K.allocs b a P.alloc hS
  refine ⟨a', ⟨h, P.ne, ?_, ?_, ?_, ?_⟩, hs, hb⟩
  · rw [K.base]; exact P.base_pos
  · rw [K.base]; exact P.base_align
  · rw [K.base, hs]; exact P.fits
  · rw [hs]; exact P.size

theorem Obj.reads_hi {o i : Nat} {e : Obj} (h : e.reads o i) : e.lo o ≤ i ∧ i < e.hi o := by
  cases e <;> simp only [Obj.reads, Obj.lo, Obj.hi] at h ⊢ <;> llvm_layout <;> omega

theorem Obj.hi_ge (o : Nat) (e : Obj) : o + Layout.valueSize ≤ e.hi o := by
  cases e <;> simp only [Obj.hi] <;> llvm_layout <;> omega

theorem Obj.lo_le (o : Nat) (e : Obj) : e.lo o ≤ o := by
  cases e <;> simp only [Obj.lo] <;> omega

theorem Obj.bytes_keep {a a' : Alloc} {o : Nat} {e : Obj} (h : e.bytes a o)
    (hb : ∀ i, e.reads o i → a'.bytes i = a.bytes i) : e.bytes a' o := by
  cases e with
  | constInt w v =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    refine ⟨h0, h1, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hb _ (by simp only [Obj.reads]; llvm_layout; omega)]; exact h2 i hi
    · rw [hb _ (by simp only [Obj.reads]; llvm_layout; omega)]; exact h3 i hi
  | poison => trivial
  | binOp op x y =>
    obtain ⟨h0, h1, h2⟩ := h
    refine ⟨h0, fun i hi => ?_, fun i hi => ?_⟩
    · rw [hb _ (by simp only [Obj.reads]; llvm_layout; omega)]; exact h1 i hi
    · rw [hb _ (by simp only [Obj.reads]; llvm_layout; omega)]; exact h2 i hi
  | other id => exact h

theorem Holds.keep {M M' : Mem} {S : Nat → Nat → Prop} {l : Loc} {e : Obj × Loc} (H : Holds M l e)
    (K : Keeps M M' S) (hS : ∀ i, e.1.reads l.2 i → S l.1 i) : Holds M' l e := by
  obtain ⟨a, P, hal, hhi, hid, hty, hby⟩ := H
  have := Obj.hi_ge l.2 e.1
  obtain ⟨a', P', hs, hb⟩ :=
    P.keep K ⟨l.2, by llvm_layout; omega, hS _ (by cases e.1 <;> simp [Obj.reads])⟩
  have hb' : ∀ i, e.1.reads l.2 i → a'.bytes i = a.bytes i := fun i hi => hb i (hS i hi)
  refine ⟨a', P', hal, hs ▸ hhi, ?_, fun i hi => ?_, Obj.bytes_keep hby hb'⟩
  · rw [hb' _ (by cases e.1 <;> simp [Obj.reads])]; exact hid
  · rw [hb' _ (by cases e.1 <;> simp only [Obj.reads, Layout.valueType] <;> omega)]; exact hty i hi

theorem HoldsTy.keep {M M' : Mem} {S : Nat → Nat → Prop} {t : Loc} {ty : Ty} (H : HoldsTy M t ty)
    (K : Keeps M M' S) (hS : ∀ i, Ty.reads t.2 i → S t.1 i) : HoldsTy M' t ty := by
  obtain ⟨a, P, hal, hsz, hby⟩ := H
  obtain ⟨a', P', hs, hb⟩ := P.keep K ⟨t.2 + 8, by llvm_layout; omega, hS _ (by simp [Ty.reads])⟩
  refine ⟨a', P', hal, hs ▸ hsz, ?_⟩
  have hb' : ∀ i, Ty.reads t.2 i → a'.bytes i = a.bytes i := fun i hi => hb i (hS i hi)
  cases ty with
  | int w =>
    obtain ⟨h0, h1, h2⟩ := hby
    exact ⟨h0, h1, fun i hi => by rw [hb' _ (by simp only [Ty.reads]; llvm_layout; omega)]; exact h2 i hi⟩
  | vector s => simp only [Ty.bytes] at hby ⊢; rw [hb' _ (by simp only [Ty.reads]; llvm_layout; omega)]; exact hby
  | other id =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := hby
    exact ⟨h0, h1, h2, h3, by rw [hb' _ (by simp only [Ty.reads]; llvm_layout; omega)]; exact h4⟩

/-- **The frame.** A change to memory that keeps every byte the view reads, and changes no allocation's size or
address, keeps the view. -/
theorem View.keep {M M' : Mem} {G : Graph} {S : Nat → Nat → Prop} (V : View M G) (K : Keeps M M' S)
    (hS : ∀ b i, G.Reads b i → S b i) : View M' G where
  objs l e h := (V.objs l e h).keep K fun i hi => hS _ _ (.inl ⟨l, e, h, rfl, hi⟩)
  tys t ty h := (V.tys t ty h).keep K fun i hi => hS _ _ (.inr ⟨t, ty, h, rfl, hi⟩)
  typed := V.typed
  ints := V.ints
  operands := V.operands
  one := V.one
  apart := V.apart
  distinct l e l' e' h h' ha := V.distinct l e l' e' h h' (by simpa [Mem.addr, K.base] using ha)
  calls := K.calls.trans V.calls

/-! ## Adding a value -/

/-- A view of `G`, with a value `e` at `r` that memory holds, in an allocation no entry of `G` is in, at an address
no value of `G` has, is a view of `G` with it. -/
theorem View.add {M : Mem} {G : Graph} {r : Loc} {e : Obj × Loc} (V : View M G) (holds : Holds M r e)
    (typed : G.tys e.2 ≠ none) (ints : ∀ w v, e.1 = .constInt w v → G.tys e.2 = some (.int w))
    (operands : ∀ op x y, e.1 = .binOp op x y → (∃ o, G.objs x = some (o, e.2)) ∧ (∃ o, G.objs y = some (o, e.2)))
    (alone : ∀ l lo hi, G.Spans l lo hi → l.1 ≠ r.1)
    (addr : ∀ l e', G.objs l = some e' → M.addr (ptrOf r) ≠ M.addr (ptrOf l)) : View M (G.addObj r e) := by
  have hnone : G.objs r = none := by
    cases hr : G.objs r with
    | none => rfl
    | some e => exact absurd rfl (alone r _ _ (.inl ⟨e, hr, rfl, rfl⟩))
  have hrty : G.tys r = none := by
    cases htr : G.tys r with
    | none => rfl
    | some ty => exact absurd rfl (alone r _ _ (.inr ⟨ty, htr, rfl, rfl⟩))
  have old : ∀ l e', l ≠ r → (G.addObj r e).objs l = some e' → G.objs l = some e' :=
    fun l e' hl he => by simpa [hl] using he
  have new : ∀ e', (G.addObj r e).objs r = some e' → e' = e := fun e' he => by simpa using he.symm
  have hspans : ∀ l lo hi, (G.addObj r e).Spans l lo hi → l = r ∨ G.Spans l lo hi := by
    intro l lo hi hs
    by_cases hl : l = r
    · exact .inl hl
    · refine .inr ?_
      rcases hs with ⟨e', he, h1, h2⟩ | h
      · exact .inl ⟨e', old l e' hl he, h1, h2⟩
      · exact .inr h
  refine ⟨fun l e' he => ?_, V.tys, fun l e' he => ?_, fun l w v t' he => ?_, fun l op x y t' he => ?_,
    fun l => ?_, ?_, ?_, V.calls⟩
  · by_cases hl : l = r
    · subst hl; rw [new e' he]; exact holds
    · exact V.objs l e' (old l e' hl he)
  · by_cases hl : l = r
    · subst hl; rw [new e' he]; simpa using typed
    · exact V.typed l e' (old l e' hl he)
  · by_cases hl : l = r
    · subst hl
      have := new _ he
      subst this
      exact ints w v rfl
    · exact V.ints l w v t' (old l _ hl he)
  · have up : ∀ z, (∃ o, G.objs z = some (o, t')) → ∃ o, (G.addObj r e).objs z = some (o, t') := by
      rintro z ⟨o, hz⟩
      have : z ≠ r := by rintro rfl; simp [hnone] at hz
      exact ⟨o, by simpa [this] using hz⟩
    by_cases hl : l = r
    · subst hl
      have := new _ he
      subst this
      obtain ⟨h1, h2⟩ := operands op x y rfl
      exact ⟨up x h1, up y h2⟩
    · obtain ⟨h1, h2⟩ := V.operands l op x y t' (old l _ hl he)
      exact ⟨up x h1, up y h2⟩
  · by_cases hl : l = r
    · subst hl; exact .inr (by simpa using hrty)
    · simpa [hl] using V.one l
  · intro l lo hi l' lo' hi' hs hs' hne hb
    rcases hspans l lo hi hs with hl | hg <;> rcases hspans l' lo' hi' hs' with hl' | hg'
    · exact absurd (hl.trans hl'.symm) hne
    · exact absurd (hl ▸ hb).symm (alone l' lo' hi' hg')
    · exact absurd (hl' ▸ hb) (alone l lo hi hg)
    · exact V.apart l lo hi l' lo' hi' hg hg' hne hb
  · intro l e₁ l' e₂ he he' ha
    by_cases hl : l = r <;> by_cases hl' : l' = r
    · rw [hl, hl']
    · subst hl
      exact absurd ha (addr l' e₂ (old l' e₂ hl' he'))
    · subst hl'
      exact absurd ha.symm (addr l e₁ (old l e₁ hl he))
    · exact V.distinct l e₁ l' e₂ (old l e₁ hl he) (old l' e₂ hl' he') ha

/-- Every entry of a view is in an allocation memory has. -/
theorem View.allocated {M : Mem} {G : Graph} (V : View M G) {l : Loc} {lo hi : Nat} (h : G.Spans l lo hi) :
    M.allocs l.1 ≠ none := by
  rcases h with ⟨e, he, -, -⟩ | ⟨ty, ht, -, -⟩
  · obtain ⟨a, P, -⟩ := V.objs l e he; simp [P.alloc]
  · obtain ⟨a, P, -⟩ := V.tys l ty ht; simp [P.alloc]

/-! ## The constructors a small pass calls -/

/-- What `ConstantInt::get(Ty, X)` does, for the `IntegerType` at `t` of width `w`: it returns `r`, a `ConstantInt`
of that type whose word is `X` as given, either the context's own for that word or a new one in an allocation of its
own. It writes no byte outside `ctx`, the context's storage, such as the map it keeps its constants in, and new
allocations, and frees only allocations wholly in `ctx`, such as the map's old buckets when it grows. `ctx` is bytes,
not allocations: `LLVMContextImpl` holds the map and the common integer types, which the view reads, in one. It gives the same object for the same type and word. `tests/llvm_heap/layout_probe.cpp` checks each
part on the pinned `libLLVM`. -/
structure ConstantIntGet (G : Graph) (M M' : Mem) (ctx : Nat → Nat → Prop) (t : Loc) (w : Nat) (X : BitVec 64)
    (r : Loc) : Prop where
  keeps : Keeps M M' fun b i => ¬ ctx b i
  made : ∃ a, Placed M' r.1 a ∧ r.2 % 8 = 0 ∧ r.2 + Layout.constSize ≤ a.size ∧
    a.bytes (r.2 + Layout.valueID) = .val (BitVec.ofNat 8 Layout.constantIntVal) ∧
    PtrAt a (r.2 + Layout.valueType) (ptrOf t) ∧ IntAt a (r.2 + Layout.constWord) X 8 ∧
    IntAt a (r.2 + Layout.constWidth) (BitVec.ofNat 32 w) 4
  /-- The view either has this constant at `r` already, or nothing in `r`'s allocation. -/
  found_or_alone : (∃ v : BitVec w, G.objs r = some (.constInt w v, t) ∧ v.setWidth 64 = X) ∨
    ∀ l lo hi, G.Spans l lo hi → l.1 ≠ r.1
  /-- A new one has an address no value in the view has. -/
  addr : G.objs r = none → ∀ l e, G.objs l = some e → M'.addr (ptrOf r) ≠ M'.addr (ptrOf l)

theorem setWidth_setWidth_64 {w : Nat} (hw : w ≤ 64) (v : BitVec w) : (v.setWidth 64).setWidth w = v := by
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem setWidth_64_of_lt {w : Nat} {X : BitVec 64} (hX : X.toNat < 2 ^ w) : (X.setWidth w).setWidth 64 = X := by
  apply BitVec.eq_of_toNat_eq
  have := X.isLt
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt this]

/-- **`ConstantInt::get` keeps the view, and adds the constant it returns**, given its precondition: the value fits
in the width, `hX`. That's #74's finding about `APInt`, as a hypothesis: the pinned release build doesn't check it,
and a word with bits set above the width is no `ConstantInt` the view describes (`dirty_not_constInt`). -/
theorem View.constantIntGet {M M' : Mem} {G : Graph} {ctx : Nat → Nat → Prop} {t r : Loc} {w : Nat} {X : BitVec 64}
    (V : View M G) (h : ConstantIntGet G M M' ctx t w X r) (hctx : ∀ b i, G.Reads b i → ¬ ctx b i)
    (ht : G.tys t = some (.int w)) (hw : 0 < w) (hw64 : w ≤ 64) (hX : X.toNat < 2 ^ w) :
    View M' (G.addObj r (.constInt w (X.setWidth w), t)) := by
  have V' := V.keep h.keeps hctx
  rcases h.found_or_alone with ⟨v, hr, hvX⟩ | alone
  · -- The context had it, and so did the view.
    have hv' : v = X.setWidth w := by rw [← hvX, setWidth_setWidth_64 hw64]
    have : G.addObj r (.constInt w (X.setWidth w), t) = G := by
      cases G with
      | mk objs tys =>
        simp only [Graph.addObj, Graph.mk.injEq, and_true]
        funext l
        by_cases hl : l = r
        · subst hl; simp_all
        · simp [hl]
    rw [this]; exact V'
  · have hnone : G.objs r = none := by
      cases hr : G.objs r with
      | none => rfl
      | some e => exact absurd rfl (alone r _ _ (.inl ⟨e, hr, rfl, rfl⟩))
    obtain ⟨a, P, hal, hsz, hid, hty, hword, hwidth⟩ := h.made
    refine V'.add ⟨a, P, hal, by simpa [Obj.hi] using hsz, by simpa [Obj.id] using hid, hty,
      hw, hw64, by rw [setWidth_64_of_lt hX]; exact hword, hwidth⟩ (by simp [ht])
      (fun w' v he => by cases he; exact ht) (fun _ _ _ he => by cases he) alone (h.addr hnone)

/-- What `PoisonValue::get(Ty)` does, for the type at `t`: it returns `r`, the context's `PoisonValue` of that type,
either one it had or a new one in an allocation of its own, writing no byte outside `ctx` and new allocations. -/
structure PoisonGet (G : Graph) (M M' : Mem) (ctx : Nat → Nat → Prop) (t r : Loc) : Prop where
  keeps : Keeps M M' fun b i => ¬ ctx b i
  made : ∃ a, Placed M' r.1 a ∧ r.2 % 8 = 0 ∧ r.2 + Layout.valueSize ≤ a.size ∧
    a.bytes (r.2 + Layout.valueID) = .val (BitVec.ofNat 8 Layout.poisonValueVal) ∧
    PtrAt a (r.2 + Layout.valueType) (ptrOf t)
  found_or_alone : G.objs r = some (.poison, t) ∨ ∀ l lo hi, G.Spans l lo hi → l.1 ≠ r.1
  addr : G.objs r = none → ∀ l e, G.objs l = some e → M'.addr (ptrOf r) ≠ M'.addr (ptrOf l)

/-- **`PoisonValue::get` keeps the view, and adds the poison it returns.** -/
theorem View.poisonGet {M M' : Mem} {G : Graph} {ctx : Nat → Nat → Prop} {t r : Loc} (V : View M G)
    (h : PoisonGet G M M' ctx t r) (hctx : ∀ b i, G.Reads b i → ¬ ctx b i) (ht : G.tys t ≠ none) :
    View M' (G.addObj r (.poison, t)) := by
  have V' := V.keep h.keeps hctx
  rcases h.found_or_alone with hr | alone
  · have : G.addObj r (.poison, t) = G := by
      cases G with
      | mk objs tys =>
        simp only [Graph.addObj, Graph.mk.injEq, and_true]
        funext l
        by_cases hl : l = r
        · subst hl; simp_all
        · simp [hl]
    rw [this]; exact V'
  · have hnone : G.objs r = none := by
      cases hr : G.objs r with
      | none => rfl
      | some e => exact absurd rfl (alone r _ _ (.inl ⟨e, hr, rfl, rfl⟩))
    obtain ⟨a, P, hal, hsz, hid, hty⟩ := h.made
    exact V'.add ⟨a, P, hal, by simpa [Obj.hi] using hsz, by simpa [Obj.id] using hid, hty, trivial⟩ ht
      (fun _ _ he => by cases he) (fun _ _ _ he => by cases he) alone (h.addr hnone)

/-- What `BinaryOperator::Create(Op, S1, S2)` does, with no place to insert it, with `S1` at `x` and `S2` at `y`, both
of the type at `t`: it
makes a new allocation, `r`'s, holding two `Use`s and then the object, whose ID is the operator's, whose type is
`t`, and whose `Use`s hold `S1` and `S2`. Putting each `Use` on its operand's use list writes the operand's
`UseList`, and the `Prev` field of the `Use` that was first on it, which are the 8 bytes at each of `prevs`. It
writes nothing else that was there. -/
structure BinOpCreate (G : Graph) (M M' : Mem) (op : BinOp) (x y t : Loc) (prevs : List Loc) (r : Loc) : Prop
    where
  keeps : Keeps M M' fun b i =>
    ¬ (b = x.1 ∧ x.2 + Layout.valueUseList ≤ i ∧ i < x.2 + Layout.valueUseList + 8) ∧
    ¬ (b = y.1 ∧ y.2 + Layout.valueUseList ≤ i ∧ i < y.2 + Layout.valueUseList + 8) ∧
    ∀ p ∈ prevs, ¬ (b = p.1 ∧ p.2 ≤ i ∧ i < p.2 + 8)
  fresh : M.allocs r.1 = none
  made : ∃ a, Placed M' r.1 a ∧ r.2 = 2 * Layout.useSize ∧ r.2 + Layout.binOpSize ≤ a.size ∧
    a.bytes (r.2 + Layout.valueID) = .val (BitVec.ofNat 8 (Layout.instructionVal + op.opcode)) ∧
    PtrAt a (r.2 + Layout.valueType) (ptrOf t) ∧ PtrAt a Layout.useVal (ptrOf x) ∧
    PtrAt a (Layout.useSize + Layout.useVal) (ptrOf y)
  addr : ∀ l e, G.objs l = some e → M'.addr (ptrOf r) ≠ M'.addr (ptrOf l)

/-- No byte of a value's `UseList` is one the view reads. -/
theorem View.useList_unread {M : Mem} {G : Graph} {x : Loc} {ex : Obj × Loc} (V : View M G)
    (hx : G.objs x = some ex) {i : Nat} (h1 : x.2 + Layout.valueUseList ≤ i)
    (h2 : i < x.2 + Layout.valueUseList + 8) : ¬ G.Reads x.1 i := by
  have hlo := Obj.lo_le x.2 ex.1
  have hhi := Obj.hi_ge x.2 ex.1
  rintro (⟨l, e, he, hb, hr⟩ | ⟨t, ty, ht, hb, hr⟩)
  · by_cases hl : l = x
    · subst hl
      rw [hx] at he
      cases he
      revert hr
      cases ex.1 <;> simp only [Obj.reads] <;> llvm_layout <;> omega
    · have := V.apart l _ _ x _ _ (.inl ⟨e, he, rfl, rfl⟩) (.inl ⟨ex, hx, rfl, rfl⟩) hl hb
      have := Obj.reads_hi hr
      llvm_layout
      omega
  · have htx : t ≠ x := by
      rintro rfl
      rcases V.one t with h | h <;> simp_all
    have := V.apart t _ _ x _ _ (.inr ⟨ty, ht, rfl, rfl⟩) (.inl ⟨ex, hx, rfl, rfl⟩) htx hb
    simp only [Ty.reads] at hr
    llvm_layout
    omega

/-- **`BinaryOperator::Create` keeps the view, and adds the operator it makes**, given that the `Use`s it puts the
new ones before have their `Prev` field where the view reads nothing, `hprev`. That holds when those `Use`s are
`Use`s, as LLVM's use lists keep them, and the view doesn't describe use lists yet, so it's a hypothesis here. -/
theorem View.binOpCreate {M M' : Mem} {G : Graph} {op : BinOp} {x y t r : Loc} {ox oy : Obj} {prevs : List Loc}
    (V : View M G) (h : BinOpCreate G M M' op x y t prevs r) (hx : G.objs x = some (ox, t))
    (hy : G.objs y = some (oy, t)) (hprev : ∀ p ∈ prevs, ∀ i, p.2 ≤ i → i < p.2 + 8 → ¬ G.Reads p.1 i) :
    View M' (G.addObj r (.binOp op x y, t)) := by
  have V' := V.keep h.keeps fun b i hr => by
    refine ⟨?_, ?_, fun p hp ⟨hb, h1, h2⟩ => hprev p hp i h1 h2 (hb ▸ hr)⟩
    · rintro ⟨rfl, h1, h2⟩; exact V.useList_unread hx h1 h2 hr
    · rintro ⟨rfl, h1, h2⟩; exact V.useList_unread hy h1 h2 hr
  obtain ⟨a, P, hr, hsz, hid, hty, hx0, hy0⟩ := h.made
  have holds : Holds M' r (.binOp op x y, t) := by
    refine ⟨a, P, by rw [hr]; llvm_layout, by simpa [Obj.hi] using hsz, by simpa [Obj.id] using hid, hty, ?_⟩
    simp only [Obj.bytes]
    rw [hr]
    llvm_layout
    exact ⟨by omega, by simpa using hx0, by simpa using hy0⟩
  have typed : G.tys t ≠ none := V.typed x _ hx
  refine V'.add holds typed (fun _ _ he => by cases he)
    (fun op' x' y' he => by cases he; exact ⟨⟨ox, hx⟩, ⟨oy, hy⟩⟩) (fun l lo hi hs hb => ?_) h.addr
  exact V.allocated hs (hb ▸ h.fresh)

/-! ## What the code's reads give

The general lemmas are those of #74's prototype, `prototypes/binding/HeapView.lean`. -/

theorem toNat_ofNat_lt {o : Nat} (h : o < 2 ^ 64) : (BitVec.ofNat 64 o).toNat = o := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem Placed.addr {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (ho : o ≤ a.size) :
    (M.addr (ptrOf (b, o))).toNat = (M.base b).toNat + o := by
  have hb : (b == 0) = false := by simpa using P.ne
  have := P.fits
  have := P.size
  simp only [Mem.addr, ptrOf, hb, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem check_nil {M : Mem} {q : Ptr} {a : Alloc} {write : Bool} (hq : q.tags = []) (hc : M.calls = []) :
    M.check q a write = none := by
  simp [Mem.check, hq, hc]

theorem visible_nil {M : Mem} {q : Ptr} {a : Alloc} {o : Nat} (hc : M.calls = []) : M.visible q a o = a.bytes o := by
  simp [Mem.visible, Mem.unwritten, hc]

/-- A byte, read where `P` says it is. -/
theorem load8 {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 1 ≤ a.size)
    (hal : o % 8 = 0) {v : BitVec 8} (hv : a.bytes o = .val v) :
    Mem.loadInt 8 M (some (ptrOf (b, o))) 8 = Outcome.ok (some v) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (ptrOf (b, o))).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 8 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, ptrOf, P.alloc, hoff, fits, ite_false]
  simp only [ptrOf] at hal'
  simp [hal', check_nil (M := M) (q := ⟨b, BitVec.ofNat 64 o, []⟩) rfl hc, ptrOf, Mem.read, visible_nil hc, hmod, hv,
    Mem.collect, Outcome.ok]

theorem bytes_sum4 (x : BitVec 32) :
    (BitVec.ofNat 8 (x.toNat >>> (8 * 0))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 1))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 2))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 3))).toNat +
      256 * 0))) = x.toNat := by
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega

/-- A 32-bit word, read where `P` says it is. -/
theorem load32 {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 4 ≤ a.size)
    (hal : o % 8 = 0) {x : BitVec 32} (hx : IntAt a o x 4) :
    Mem.loadInt 32 M (some (ptrOf (b, o))) 8 = Outcome.ok (some x) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (ptrOf (b, o))).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 32 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, ptrOf, P.alloc, hoff, fits, ite_false]
  simp only [ptrOf] at hal'
  have h0 := hx 0 (by omega)
  have h1 := hx 1 (by omega)
  have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [hal', check_nil (M := M) (q := ⟨b, BitVec.ofNat 64 o, []⟩) rfl hc, ptrOf, Mem.read, visible_nil hc, List.range,
    List.range.loop, List.map, Nat.add_zero, hoff, hmod, h0, h1, h2, h3, Mem.intByte, Mem.collect, Nat.reduceDiv,
    bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, Outcome.ok, bytes_sum4, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem bytes_sum8 (x : BitVec 64) :
    (BitVec.ofNat 8 (x.toNat >>> (8 * 0))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 1))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 2))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 3))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 4))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 5))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 6))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 7))).toNat + 256 *
      0))))))) = x.toNat := by
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega

/-- A 64-bit word, read where `P` says it is. -/
theorem load64 {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 8 ≤ a.size)
    (hal : o % 8 = 0) {x : BitVec 64} (hx : IntAt a o x 8) :
    Mem.loadInt 64 M (some (ptrOf (b, o))) 8 = Outcome.ok (some x) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (ptrOf (b, o))).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 64 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, ptrOf, P.alloc, hoff, fits, ite_false]
  simp only [ptrOf] at hal'
  have h0 := hx 0 (by omega)
  have h1 := hx 1 (by omega)
  have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega)
  have h4 := hx 4 (by omega)
  have h5 := hx 5 (by omega)
  have h6 := hx 6 (by omega)
  have h7 := hx 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [hal', check_nil (M := M) (q := ⟨b, BitVec.ofNat 64 o, []⟩) rfl hc, ptrOf, Mem.read, visible_nil hc, List.range,
    List.range.loop, List.map, Nat.add_zero, hoff, hmod, h0, h1, h2, h3, h4, h5, h6, h7, Mem.intByte, Mem.collect,
    Nat.reduceDiv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, Outcome.ok, bytes_sum8,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A pointer stored whole, read where `P` says it is. -/
theorem loadPtr {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 8 ≤ a.size)
    (hal : o % 8 = 0) {p : Ptr} (hp : PtrAt a o p) :
    Mem.loadPtr M (some (ptrOf (b, o))) 8 = Outcome.ok (some p) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (ptrOf (b, o))).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 8 > a.size := by omega
  simp only [Mem.loadPtr, Mem.access, ptrOf, P.alloc, hoff, fits, ite_false]
  simp only [ptrOf] at hal'
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  have h5 := hp 5 (by omega)
  have h6 := hp 6 (by omega)
  have h7 := hp 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp [hal', check_nil (M := M) (q := ⟨b, BitVec.ofNat 64 o, []⟩) rfl hc, ptrOf, Mem.read, visible_nil hc, List.range,
    List.range.loop, hoff, hmod, h0, h1, h2, h3, h4, h5, h6, h7, Mem.assemblePtr, List.zipIdx, List.zipIdxTR,
    Outcome.ok]

/-- The ID a matcher reads first, `load i8, ptr %V, align 8`. -/
theorem View.load_id {M : Mem} {G : Graph} {l : Loc} {e : Obj × Loc} (V : View M G) (he : G.objs l = some e) :
    Mem.loadInt 8 M (some (ptrOf l)) 8 = Outcome.ok (some (BitVec.ofNat 8 e.1.id)) := by
  obtain ⟨a, P, hal, hhi, hid, -, -⟩ := V.objs l e he
  have := Obj.hi_ge l.2 e.1
  llvm_layout
  exact load8 P V.calls (by omega) hal (by simpa using hid)

/-- A value's type, the pointer at offset 8. -/
theorem View.load_type {M : Mem} {G : Graph} {l : Loc} {e : Obj × Loc} (V : View M G) (he : G.objs l = some e) :
    Mem.loadPtr M (some (ptrOf (l.1, l.2 + Layout.valueType))) 8 = Outcome.ok (some (ptrOf e.2)) := by
  obtain ⟨a, P, hal, hhi, -, hty, -⟩ := V.objs l e he
  have := Obj.hi_ge l.2 e.1
  llvm_layout
  exact loadPtr P V.calls (by omega) (by omega) hty

/-- A `ConstantInt`'s word, at offset 24: its value, with the bits above its width 0. -/
theorem View.load_word {M : Mem} {G : Graph} {l t : Loc} {w : Nat} {v : BitVec w} (V : View M G)
    (he : G.objs l = some (.constInt w v, t)) :
    Mem.loadInt 64 M (some (ptrOf (l.1, l.2 + Layout.constWord))) 8 = Outcome.ok (some (v.setWidth 64)) := by
  obtain ⟨a, P, hal, hhi, -, -, -, -, hword, -⟩ := V.objs l _ he
  simp only [Obj.hi] at hhi
  llvm_layout
  exact load64 P V.calls (by omega) (by omega) hword

/-- A `ConstantInt`'s width, at offset 32. -/
theorem View.load_width {M : Mem} {G : Graph} {l t : Loc} {w : Nat} {v : BitVec w} (V : View M G)
    (he : G.objs l = some (.constInt w v, t)) :
    Mem.loadInt 32 M (some (ptrOf (l.1, l.2 + Layout.constWidth))) 8 = Outcome.ok (some (BitVec.ofNat 32 w)) := by
  obtain ⟨a, P, hal, hhi, -, -, -, -, -, hwidth⟩ := V.objs l _ he
  simp only [Obj.hi] at hhi
  llvm_layout
  exact load32 P V.calls (by omega) (by omega) hwidth

/-- A binary operator's first operand: the `Value *` of the `Use` 64 bytes before it. -/
theorem View.load_op0 {M : Mem} {G : Graph} {l t x y : Loc} {op : BinOp} (V : View M G)
    (he : G.objs l = some (.binOp op x y, t)) :
    Mem.loadPtr M (some (ptrOf (l.1, l.2 - 2 * Layout.useSize))) 8 = Outcome.ok (some (ptrOf x)) := by
  obtain ⟨a, P, hal, hhi, -, -, h64, hx, -⟩ := V.objs l _ he
  simp only [Obj.hi] at hhi
  llvm_layout
  exact loadPtr P V.calls (by omega) (by omega) hx

/-- Its second operand: the `Value *` of the `Use` 32 bytes before it. -/
theorem View.load_op1 {M : Mem} {G : Graph} {l t x y : Loc} {op : BinOp} (V : View M G)
    (he : G.objs l = some (.binOp op x y, t)) :
    Mem.loadPtr M (some (ptrOf (l.1, l.2 - Layout.useSize))) 8 = Outcome.ok (some (ptrOf y)) := by
  obtain ⟨a, P, hal, hhi, -, -, h64, -, hy⟩ := V.objs l _ he
  simp only [Obj.hi] at hhi
  llvm_layout
  exact loadPtr P V.calls (by omega) (by omega) hy

/-- An `IntegerType`'s word, at offset 8: its ID, 12, and its width above. -/
theorem View.load_intType {M : Mem} {G : Graph} {t : Loc} {w : Nat} (V : View M G) (ht : G.tys t = some (.int w)) :
    Mem.loadInt 32 M (some (ptrOf (t.1, t.2 + Layout.typeWord))) 8 = Outcome.ok (some (intTypeWord w)) := by
  obtain ⟨a, P, hal, hsz, -, -, hword⟩ := V.tys t _ ht
  llvm_layout
  exact load32 P V.calls (by omega) (by omega) hword

/-- Two values the view has are the same `Value *` exactly when they're at the same place, so comparing addresses,
as `m_Specific` does, compares them. -/
theorem View.addr_eq_iff {M : Mem} {G : Graph} {l l' : Loc} {e e' : Obj × Loc} (V : View M G)
    (he : G.objs l = some e) (he' : G.objs l' = some e') : M.addr (ptrOf l) = M.addr (ptrOf l') ↔ l = l' :=
  ⟨V.distinct l e l' e' he he', fun h => h ▸ rfl⟩

/-! ## APInt's clean words -/

theorem IntAt.toNat_eq {a : Alloc} {o : Nat} {X Y : BitVec 64} (hX : IntAt a o X 8) (hY : IntAt a o Y 8) : X = Y := by
  have h : ∀ i, i < 8 → BitVec.ofNat 8 (X.toNat >>> (8 * i)) = BitVec.ofNat 8 (Y.toNat >>> (8 * i)) := by
    intro i hi
    have := (hX i hi).symm.trans (hY i hi)
    simpa [Mem.intByte] using this
  apply BitVec.eq_of_toNat_eq
  rw [← bytes_sum8 X, ← bytes_sum8 Y, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- **A dirty word is no `ConstantInt` the view describes.** A word with a bit set at or above the width, which the
pinned release build stores for `ConstantInt::get(i1, 7)`, doesn't hold `v.setWidth 64` for any `v` of that width, so
no `View` has a `ConstantInt` there, and a theorem resting on one says nothing about such a heap. -/
theorem dirty_not_constInt {a : Alloc} {o w : Nat} {X : BitVec 64} (hX : 2 ^ w ≤ X.toNat)
    (h : IntAt a o X 8) (v : BitVec w) : ¬ IntAt a o (v.setWidth 64) 8 := by
  intro hv
  have := congrArg BitVec.toNat (IntAt.toNat_eq h hv)
  have := v.isLt
  simp only [BitVec.toNat_setWidth] at *
  have : v.toNat % 2 ^ 64 ≤ v.toNat := Nat.mod_le _ _
  omega

end IRLean.LLVMHeap
