import IRLean
import SimplifyAddModel

/-! # What LLVM's objects hold, for the reads `llvm::isKnownNegation` makes

A first slice of BIND-04, for one function: what bytes in IRLean's memory mean as the `Value *`s that #47's model calls
`Operand`s. It covers only what the compiled `isKnownNegation` reads, at the pin, on x86-64:

- a `Value`'s ID is the byte at offset 0, and its type is the pointer at offset 8;
- a `sub` instruction's ID is 46, `Value::InstructionVal + Instruction::Sub`, and its operands are the `Value *` at
  offsets -64 and -32, the `Val` of its two `Use`s;
- a `ConstantInt`'s ID is 5, its width is the 32-bit word at offset 32, and, up to 64 bits, its value is the word at
  offset 24, with the bits above the width 0;
- a type's ID is the low byte of the 32-bit word at offset 8, and it's a vector exactly when that byte is 18 or 19.

These come from the compiled IR, which reads those offsets and compares with those numbers. `layout_probe.cpp` checks
each against objects the pinned `libLLVM` builds. Nothing here proves that a heap LLVM builds meets them: that's the
rest of BIND-04, and until then they're hypotheses of the theorem that uses them. -/

set_option linter.unusedSimpArgs false

namespace Binding

open IRLean CppCorrespondence.SimplifyAdd

/-! ## Reading memory -/

/-- A pointer with no tags, `o` bytes into allocation `b`. -/
abbrev obj (b o : Nat) : Ptr := ⟨b, BitVec.ofNat 64 o, []⟩

/-- Allocation `b` is `a`, where every access the compiled code makes into it is valid: not null, aligned to 8 from
its start, and not crossing the top of the address space. -/
structure Placed (M : Mem) (b : Nat) (a : Alloc) : Prop where
  alloc : M.allocs b = some a
  ne : b ≠ 0
  base_pos : 0 < (M.base b).toNat
  base_align : (M.base b).toNat % 8 = 0
  fits : (M.base b).toNat + a.size < 2 ^ 64
  size : a.size < 2 ^ 63

/-- What the code does to memory leaves allocation `s` and nothing else changed. -/
structure Same (M M' : Mem) (s : Nat) : Prop where
  allocs : ∀ b, b ≠ s → M'.allocs b = M.allocs b
  base : M'.base = M.base
  calls : M'.calls = M.calls

theorem Same.trans {M M' M'' : Mem} {s : Nat} (h : Same M M' s) (h' : Same M' M'' s) : Same M M'' s :=
  ⟨fun b hb => (h'.allocs b hb).trans (h.allocs b hb), h'.base.trans h.base, h'.calls.trans h.calls⟩

theorem Placed.same {M M' : Mem} {b s : Nat} {a : Alloc} (P : Placed M b a) (S : Same M M' s) (hb : b ≠ s) :
    Placed M' b a :=
  ⟨(S.allocs b hb).trans P.alloc, P.ne, by rw [S.base]; exact P.base_pos, by rw [S.base]; exact P.base_align,
    by rw [S.base]; exact P.fits, P.size⟩

theorem Placed.addr {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (ho : o ≤ a.size) :
    (M.addr (obj b o)).toNat = (M.base b).toNat + o := by
  have hb : (b == 0) = false := by simpa using P.ne
  have := P.fits
  have := P.size
  simp only [Mem.addr, obj, hb, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem check_nil {M : Mem} {q : Ptr} {a : Alloc} {write : Bool} (hq : q.tags = []) (hc : M.calls = []) :
    M.check q a write = none := by
  simp [Mem.check, hq, hc]

theorem visible_nil {M : Mem} {q : Ptr} {a : Alloc} {o : Nat} (hc : M.calls = []) : M.visible q a o = a.bytes o := by
  simp [Mem.visible, Mem.unwritten, hc]

theorem toNat_ofNat_lt {o : Nat} (h : o < 2 ^ 64) : (BitVec.ofNat 64 o).toNat = o := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- A byte, read where `P` says it is. -/
theorem load8 {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 1 ≤ a.size)
    (hal : o % 8 = 0) {v : BitVec 8} (hv : a.bytes o = .val v) :
    Mem.loadInt 8 M (some (obj b o)) 8 = Outcome.ok (some v) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (obj b o)).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 8 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, obj, P.alloc, hoff, fits, ite_false]
  simp only [obj] at hal'
  simp [hal', check_nil (M := M) (q := obj b o) rfl hc, Mem.read, visible_nil hc, hmod, hv, Mem.collect,
    Outcome.ok]

theorem bytes_sum4 (x : BitVec 32) :
    (BitVec.ofNat 8 (x.toNat >>> (8 * 0))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 1))).toNat + 256 *
      ((BitVec.ofNat 8 (x.toNat >>> (8 * 2))).toNat + 256 * ((BitVec.ofNat 8 (x.toNat >>> (8 * 3))).toNat +
      256 * 0))) = x.toNat := by
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  omega

/-- A 32-bit word, read where `P` says it is. -/
theorem load32 {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 4 ≤ a.size)
    (hal : o % 8 = 0) {x : BitVec 32} (hx : ∀ i, i < 4 → a.bytes (o + i) = Mem.intByte x i) :
    Mem.loadInt 32 M (some (obj b o)) 8 = Outcome.ok (some x) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (obj b o)).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 32 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, obj, P.alloc, hoff, fits, ite_false]
  simp only [obj] at hal'
  have h0 := hx 0 (by omega)
  have h1 := hx 1 (by omega)
  have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [hal', check_nil (M := M) (q := obj b o) rfl hc, Mem.read, visible_nil hc, List.range, List.range.loop,
    List.map, Nat.add_zero, hoff, hmod, h0, h1, h2, h3, Mem.intByte, Mem.collect, Nat.reduceDiv, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, ite_false, Outcome.ok, bytes_sum4, BitVec.ofNat_toNat, BitVec.setWidth_eq]

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
    (hal : o % 8 = 0) {x : BitVec 64} (hx : ∀ i, i < 8 → a.bytes (o + i) = Mem.intByte x i) :
    Mem.loadInt 64 M (some (obj b o)) 8 = Outcome.ok (some x) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (obj b o)).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 64 / 8 > a.size := by omega
  simp only [Mem.loadInt, Mem.access, obj, P.alloc, hoff, fits, ite_false]
  simp only [obj] at hal'
  have h0 := hx 0 (by omega)
  have h1 := hx 1 (by omega)
  have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega)
  have h4 := hx 4 (by omega)
  have h5 := hx 5 (by omega)
  have h6 := hx 6 (by omega)
  have h7 := hx 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [hal', check_nil (M := M) (q := obj b o) rfl hc, Mem.read, visible_nil hc, List.range, List.range.loop,
    List.map, Nat.add_zero, hoff, hmod, h0, h1, h2, h3, h4, h5, h6, h7, Mem.intByte, Mem.collect, Nat.reduceDiv,
    bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false, Outcome.ok, bytes_sum8, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- A pointer stored whole, read where `P` says it is. -/
theorem loadPtr {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) (hc : M.calls = []) (ho : o + 8 ≤ a.size)
    (hal : o % 8 = 0) {p : Ptr} (hp : ∀ i, i < 8 → a.bytes (o + i) = .ptr p i) :
    Mem.loadPtr M (some (obj b o)) 8 = Outcome.ok (some p) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have hmod : o % 18446744073709551616 = o := Nat.mod_eq_of_lt (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (obj b o)).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 8 > a.size := by omega
  simp only [Mem.loadPtr, Mem.access, obj, P.alloc, hoff, fits, ite_false]
  simp only [obj] at hal'
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  have h5 := hp 5 (by omega)
  have h6 := hp 6 (by omega)
  have h7 := hp 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp [hal', check_nil (M := M) (q := obj b o) rfl hc, Mem.read, visible_nil hc, List.range, List.range.loop,
    hoff, hmod, h0, h1, h2, h3, h4, h5, h6, h7, Mem.assemblePtr, List.zipIdx, List.zipIdxTR, Outcome.ok]

/-- Stepping back `k` bytes inside an allocation, as `getelementptr inbounds` with a negative offset does. -/
theorem gep_back {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) {k : Nat} (hk : k ≤ o) (ho : o ≤ a.size)
    (hk0 : 0 < k) {d : BitVec 64} (hd : d.toNat = 2 ^ 64 - k) :
    Mem.gep M (some (obj b o)) (some d) (inbounds := true) = some (obj b (o - k)) := by
  have := P.size
  have := P.fits
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have haddr := P.addr (o := o) ho
  have hmsb : d.msb = true := by
    simp only [BitVec.msb_eq_decide, hd, decide_eq_true_eq]; omega
  have hneg : (-d).toNat = k := by
    rw [BitVec.toNat_neg, hd]; omega
  have hwrap : BitVec.ult (M.addr (obj b o)) (-d) = false := by
    simp only [BitVec.ult, hneg, haddr, decide_eq_false_iff_not]; omega
  have hmoved : BitVec.ofNat 64 o + d = BitVec.ofNat 64 (o - k) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hoff, hd, toNat_ofNat_lt (by omega)]
    omega
  have hd0 : (d != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro h
    rw [h] at hd
    simp at hd
    omega
  simp only [Mem.gep, Mem.addressWraps, hmsb, ite_true, hwrap, Bool.false_eq_true, Bool.and_false, Bool.or_false,
    Bool.true_or, Bool.and_true, ite_false, hd0, P.alloc, obj, hmoved, hoff]
  have h1 : o ≤ a.size := ho
  have h2 : (BitVec.ofNat 64 (o - k)).toNat ≤ a.size := by rw [toNat_ofNat_lt (by omega)]; omega
  simp [h1, h2, Nat.mod_eq_of_lt (show o - k < 18446744073709551616 by omega)]
  omega

/-- Stepping forward `k` bytes inside an allocation, as `getelementptr inbounds nuw` does. -/
theorem gep_fwd {M : Mem} {b o : Nat} {a : Alloc} (P : Placed M b a) {k : Nat} (ho : o + k ≤ a.size) :
    Mem.gep M (some (obj b o)) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some (obj b (o + k)) := by
  have := P.size
  have := P.fits
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have haddr := P.addr (o := o) (by omega)
  have h := Mem.gep_forward (m := M) (q := obj b o) (a := a) (k := k) P.alloc (by rw [hoff]; omega) (by omega)
    (by omega) (by omega)
  rw [h]
  simp [obj, BitVec.ofNat_add]

/-! ## The function's own stack slots -/

/-- A 16-byte `alloca` before `llvm.lifetime.start`: it can't be written, and reads as uninitialized. -/
def deadSlot : Alloc := { size := 16, readonly := true, bytes := fun _ => .uninit, stack := true }

theorem same_frame (M : Mem) (f : List Nat) (s : Nat) : Same M { M with frame := f } s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem alloca16 (M : Mem) :
    ∃ M', Mem.alloca M (some 16#64) (dead := true) = Outcome.ok (some ⟨M.next, 0#64, []⟩, M') ∧
      Same M M' M.next ∧ M'.allocs M.next = some deadSlot ∧ M'.next = M.next + 1 ∧ M'.base = M.base := by
  refine ⟨_, rfl, ⟨fun b hb => ?_, rfl, rfl⟩, ?_, rfl, rfl⟩
  · simp [hb]
  · simp [deadSlot]

/-- `llvm.lifetime.start` or `.end` on a slot, through the `nonnull` the emitter puts on its pointer. -/
theorem lifetime_slot (M : Mem) {s : Nat} {a : Alloc} (ha : M.allocs s = some a) (hs : s ≠ 0)
    (hbase : M.base s ≠ 0#64) (alive : Bool) :
    ∃ M', Mem.lifetime M (Mem.nonnull M (some ⟨s, 0#64, []⟩)) alive = Outcome.ok M' ∧ Same M M' s ∧
      M'.allocs s = some { a with readonly := !alive, bytes := fun _ => .uninit } ∧ M'.next = M.next := by
  have hs' : (s == 0) = false := by simpa using hs
  have hnn : Mem.nonnull M (some ⟨s, 0#64, []⟩) = some ⟨s, 0#64, []⟩ := by
    simp [Mem.nonnull, Mem.addr, hs', hbase]
  refine ⟨M.setAlloc s (some { a with readonly := !alive, bytes := fun _ => .uninit }),
    by rw [hnn]; simp only [Mem.lifetime, ha], ⟨fun b hb => ?_, rfl, rfl⟩, ?_, rfl⟩
  · simp [Mem.setAlloc, hb]
  · simp [Mem.setAlloc]

/-- Storing a pointer into a live slot. -/
theorem storePtr_slot {M : Mem} {s o : Nat} {a : Alloc} (P : Placed M s a) (hro : a.readonly = false)
    (hc : M.calls = []) (ho : o + 8 ≤ a.size) (hal : o % 8 = 0) (v : Ptr) :
    ∃ M', Mem.storePtr M (some (obj s o)) (some v) 8 = Outcome.ok M' ∧ Same M M' s ∧ M'.next = M.next ∧
      ∃ a', M'.allocs s = some a' ∧ a'.size = a.size ∧ a'.readonly = a.readonly ∧ a'.stack = a.stack ∧
        (∀ i, i < 8 → a'.bytes (o + i) = .ptr v i) := by
  have := P.size
  have hoff := toNat_ofNat_lt (o := o) (by omega)
  have haddr := P.addr (o := o) (by omega)
  have hal' : (M.addr (obj s o)).toNat % 8 = 0 := by rw [haddr]; have := P.base_align; omega
  have fits : ¬ o + 8 > a.size := by omega
  simp only [obj] at hal'
  refine ⟨M.write (obj s o) a 8 (fun i => .ptr v i), ?_, ⟨fun b hb => ?_, rfl, ?_⟩, rfl,
    ⟨{ a with bytes := fun i => if o ≤ i ∧ i < o + 8 then .ptr v (i - o) else a.bytes i }, ?_, rfl, rfl, rfl,
      fun i hi => ?_⟩⟩
  · simp only [Mem.storePtr, Mem.access, obj, P.alloc, hoff, fits, ite_false, hal', bne_self_eq_false,
      Bool.and_false, Bool.false_eq_true, hro, check_nil (M := M) (q := obj s o) rfl hc, Nat.reduceMod,
      Nat.reduceDiv]
  · simp [Mem.write, Mem.setAlloc, hb]
  · simp [Mem.write, hc]
  · simp [Mem.write, Mem.setAlloc, hoff]
  · simp only [show o ≤ o + i ∧ o + i < o + 8 from ⟨by omega, by omega⟩, and_self, ite_true,
      Nat.add_sub_cancel_left]

/-! ## The fragment's objects -/

variable {w : Nat}

/-- Where each `Value *` the model names is: `o` bytes into allocation `b`. -/
abbrev Locs (w : Nat) := Ident w → Nat × Nat

def ptrOf (l : Nat × Nat) : Ptr := obj l.1 l.2

/-- The header every `Value` has: its ID at offset 0, and its type at offset 8. -/
structure Header (M : Mem) (l : Nat × Nat) (id : BitVec 8) (ty : Nat × Nat) (a : Alloc) : Prop where
  placed : Placed M l.1 a
  align : l.2 % 8 = 0
  room : l.2 + 16 ≤ a.size
  id : a.bytes l.2 = .val id
  type : ∀ i, i < 8 → a.bytes (l.2 + 8 + i) = .ptr (ptrOf ty) i

def _root_.CppCorrespondence.SimplifyAdd.Operand.isSub : Operand w → Bool
  | .sub .. => true
  | _ => false

def _root_.CppCorrespondence.SimplifyAdd.Operand.isConstInt : Operand w → Bool
  | .const _ => true
  | _ => false

/-- What the heap holds for an operand, as far as `isKnownNegation` reads it. A `sub`'s operands are objects too,
and anything else is an object whose ID is neither a `sub`'s nor a `ConstantInt`'s, with nothing read past its
header. -/
inductive Holds (M : Mem) (loc : Locs w) (ty : Nat × Nat) : Operand w → Prop
  | const (c : BitVec w) (a : Alloc) :
      Header M (loc (.const c)) 5#8 ty a →
      (loc (.const c)).2 + 40 ≤ a.size →
      (∀ i, i < 4 → a.bytes ((loc (.const c)).2 + 32 + i) = Mem.intByte (BitVec.ofNat 32 w) i) →
      (∀ i, i < 8 → a.bytes ((loc (.const c)).2 + 24 + i) = Mem.intByte (c.setWidth 64) i) →
      Holds M loc ty (.const c)
  | sub (n : Nat) (nuw nsw : Bool) (x y : Operand w) (a : Alloc) :
      Header M (loc (.node n)) 46#8 ty a →
      64 ≤ (loc (.node n)).2 →
      (∀ i, i < 8 → a.bytes ((loc (.node n)).2 - 64 + i) = .ptr (ptrOf (loc x.ident)) i) →
      (∀ i, i < 8 → a.bytes ((loc (.node n)).2 - 32 + i) = .ptr (ptrOf (loc y.ident)) i) →
      Holds M loc ty x → Holds M loc ty y →
      Holds M loc ty (.sub n nuw nsw x y)
  | other (op : Operand w) (id : BitVec 8) (a : Alloc) :
      op.isSub = false → op.isConstInt = false → id ≠ 5#8 → id ≠ 46#8 →
      Header M (loc op.ident) id ty a →
      Holds M loc ty op

/-- The type every operand has: an object whose ID, the low byte at offset 8, isn't a vector's. -/
structure TypeObj (M : Mem) (ty : Nat × Nat) (a : Alloc) (tw : BitVec 32) : Prop where
  placed : Placed M ty.1 a
  align : ty.2 % 8 = 0
  room : ty.2 + 16 ≤ a.size
  word : ∀ i, i < 4 → a.bytes (ty.2 + 8 + i) = Mem.intByte tw i
  scalar : tw &&& 254#32 ≠ 18#32

/-- The identities the compiled code can compare, for an operand: its own, and a `sub`'s operands'. -/
def reads : Operand w → List (Ident w)
  | .sub n _ _ a b => .node n :: (reads a ++ reads b)
  | op => [op.ident]

theorem ident_mem_reads (x : Operand w) : x.ident ∈ reads x := by
  cases x <;> simp [reads, Operand.ident]

/-- The heap holds `x` and `y` for the compiled code, in allocations below `lo`, at distinct addresses. The
addresses are only asked to differ for the identities the code can see. Asking it of every `Ident` would ask
infinitely many objects for 2 ^ 64 addresses, and no heap could meet it. -/
structure View (M : Mem) (loc : Locs w) (ty : Nat × Nat) (x y : Operand w) (lo : Nat) : Prop where
  hx : Holds M loc ty x
  hy : Holds M loc ty y
  type : ∃ a tw, TypeObj M ty a tw
  distinct : ∀ i, i ∈ reads x ++ reads y → ∀ j, j ∈ reads x ++ reads y →
    M.addr (ptrOf (loc i)) = M.addr (ptrOf (loc j)) → i = j
  calls : M.calls = []
  below : ∀ i, i ∈ reads x ++ reads y → (loc i).1 < lo
  typeBelow : ty.1 < lo

theorem Header.same {M M' : Mem} {l : Nat × Nat} {id : BitVec 8} {ty : Nat × Nat} {a : Alloc} {s : Nat}
    (H : Header M l id ty a) (S : Same M M' s) (hb : l.1 ≠ s) : Header M' l id ty a :=
  ⟨H.placed.same S hb, H.align, H.room, H.id, H.type⟩

theorem Holds.same {M M' : Mem} {loc : Locs w} {ty : Nat × Nat} {s : Nat} {x : Operand w}
    (H : Holds M loc ty x) (S : Same M M' s) (hb : ∀ i, i ∈ reads x → (loc i).1 ≠ s) : Holds M' loc ty x := by
  induction H with
  | const c a h1 h2 h3 h4 => exact .const c a (h1.same S (hb _ (by simp [reads, Operand.ident]))) h2 h3 h4
  | sub n nuw nsw x y a h1 h2 h3 h4 _ _ ihx ihy =>
    exact .sub n nuw nsw x y a (h1.same S (hb _ (by simp [reads]))) h2 h3 h4
      (ihx fun i hi => hb i (by simp [reads, hi])) (ihy fun i hi => hb i (by simp [reads, hi]))
  | other op id a h1 h2 h3 h4 h5 => exact .other op id a h1 h2 h3 h4 (h5.same S (hb _ (ident_mem_reads op)))

/-- A change to an allocation at or above `lo`, such as a stack slot, leaves the view as it was. -/
theorem View.same {M M' : Mem} {loc : Locs w} {ty : Nat × Nat} {x y : Operand w} {lo s : Nat}
    (V : View M loc ty x y lo) (S : Same M M' s) (hs : lo ≤ s) : View M' loc ty x y lo := by
  have hb : ∀ i, i ∈ reads x ++ reads y → (loc i).1 ≠ s := fun i hi => by have := V.below i hi; omega
  refine ⟨V.hx.same S fun i hi => hb i (by simp [hi]), V.hy.same S fun i hi => hb i (by simp [hi]), ?_, ?_, ?_,
    V.below, V.typeBelow⟩
  · obtain ⟨a, tw, T⟩ := V.type
    exact ⟨a, tw, T.placed.same S (by have := V.typeBelow; omega), T.align, T.room, T.word, T.scalar⟩
  · intro i hi j hj h
    have e : ∀ l : Nat × Nat, M'.addr (ptrOf l) = M.addr (ptrOf l) := fun l => by simp [Mem.addr, S.base]
    exact V.distinct i hi j hj (by rw [← e, ← e]; exact h)
  · rw [S.calls]; exact V.calls

end Binding
