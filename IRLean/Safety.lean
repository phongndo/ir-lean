import IRLean.Lemmas

/-! Memory safety: a way to describe what memory a function may use, and lemmas that run loads, stores,
copies and `getelementptr` on memory described that way, each saying exactly what it changed. Proofs use these
to keep memory abstract: a store gives a new `Mem` and facts about it, not a term to unfold.

What a theorem built on this claims, and what it doesn't, is in `docs/memory.md`. In short: these lemmas are
about `Mem`, the model, and a safety theorem says a function returns normally in the model, for every input
meeting its preconditions, having changed only the bytes it names. -/

namespace IRLean

/-- Two versions of an allocation that agree on everything but the bytes in `touched`. -/
structure Alloc.Agree (a a' : Alloc) (touched : Nat → Prop) : Prop where
  size : a'.size = a.size
  readonly : a'.readonly = a.readonly
  heap : a'.heap = a.heap
  stack : a'.stack = a.stack
  bytes : ∀ i, ¬ touched i → a'.bytes i = a.bytes i

theorem Alloc.Agree.refl (a : Alloc) (t : Nat → Prop) : Alloc.Agree a a t :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Alloc.Agree.trans {a a' a'' : Alloc} {t t' T : Nat → Prop} (h : Alloc.Agree a a' t)
    (h' : Alloc.Agree a' a'' t') (hT : ∀ i, t i ∨ t' i → T i) : Alloc.Agree a a'' T :=
  ⟨h'.size.trans h.size, h'.readonly.trans h.readonly, h'.heap.trans h.heap, h'.stack.trans h.stack,
    fun i hi => (h'.bytes i fun h2 => hi (hT i (.inr h2))).trans (h.bytes i fun h1 => hi (hT i (.inl h1)))⟩

namespace Mem

variable {m m' m'' : Mem}

/-! ### Objects

LangRef's allocated objects, as `Mem` holds them. A pointer reaches only the allocation in its `block`, so these
are about allocations, and offsets into them. -/

/-- Allocation `b` exists and is `size` bytes long, and its addresses follow LangRef's rules for an allocated
object: it's smaller than `2 ^ 63`, and neither it nor the address just past its end crosses the top of the address
space. Two more facts the model needs: it isn't allocation 0, where null points, and it doesn't start at address 0,
which in address space 0 no object does, since null can't be accessed there. `Mem.base` promises none of this, so a
theorem assumes it of each object it uses. -/
structure Object (m : Mem) (b size : Nat) : Prop where
  live : ∃ a, m.allocs b = some a ∧ a.size = size
  notNull : b ≠ 0
  small : size < 2 ^ 63
  nonzero : m.base b ≠ 0#64
  fits : (m.base b).toNat + size < 2 ^ 64

/-- Writing to allocation `b` isn't ruled out by the allocation itself: it isn't a constant, or a stack
object outside its lifetime. -/
def Writable (m : Mem) (b : Nat) : Prop := ∃ a, m.allocs b = some a ∧ a.readonly = false

/-- Bytes `o` to `o + w / 8` of allocation `b` hold `v`, little-endian. -/
def HoldsInt {w : Nat} (m : Mem) (b o : Nat) (v : BitVec w) : Prop :=
  ∃ a, m.allocs b = some a ∧ ∀ i, i < w / 8 → a.bytes (o + i) = intByte v i

/-- Bytes `o` to `o + 8` of allocation `b` hold the pointer `p`, stored whole. -/
def HoldsPtr (m : Mem) (b o : Nat) (p : Ptr) : Prop :=
  ∃ a, m.allocs b = some a ∧ ∀ i, i < 8 → a.bytes (o + i) = .ptr p i

/-- The pointer to byte `o` of allocation `b`, with the tags `t`. -/
abbrev at_ (b o : Nat) (t : List Tag := []) : Ptr := ⟨b, BitVec.ofNat 64 o, t⟩

/-! ### What rules apply

An access has to satisfy the promises in force: every running call's `memory(...)`, and its pointer's tags.
These say when there are none to satisfy, or when the pointer's own allow it. -/

/-- No running call restricts memory: each is of a function with no `memory(...)` attribute, which tracks
nothing. So the only rules on an access are the allocation's, and its pointer's tags. -/
def Unrestricted (m : Mem) : Prop := ∀ c, c ∈ m.calls → c.effects = {} ∧ c.tracked = false

/-- The tags on `q` allow an access, which writes if `write` and reads otherwise. -/
def TagsAllow (m : Mem) (q : Ptr) (write : Bool) : Prop := ∀ t, t ∈ q.tags → m.tagRule write t = none

theorem unrestricted_nil (h : m.calls = []) : m.Unrestricted := by
  intro c hc; simp [h] at hc

theorem tagsAllow_nil (b : Nat) (o : BitVec 64) (write : Bool) : m.TagsAllow ⟨b, o, []⟩ write := by
  intro t ht; simp at ht

/-- A tag of a call that's running allows a read, unless it's `readnone`. -/
theorem tagRule_read {t : Tag} (hr : m.isRunning t.call = true) (hn : t.readnone = false) :
    m.tagRule false t = none := by
  simp [tagRule, hr, hn]

theorem check_of_unrestricted {q : Ptr} {a : Alloc} {write : Bool} (hu : m.Unrestricted)
    (ht : m.TagsAllow q write) : m.check q a write = none := by
  rw [check_eq_none]
  refine ⟨ht, fun c hc => ?_⟩
  have he := (hu c hc).1
  have hacc : callAccess c q a = .readwrite := by
    unfold callAccess
    rw [he]
    split
    · rfl
    · split <;> rfl
  simp [callRule, hacc]

theorem unwritten_of_unrestricted {q : Ptr} {a : Alloc} {o : Nat} (hu : m.Unrestricted) :
    m.unwritten q a o = false := by
  simp only [unwritten, List.any_eq_false]
  intro c hc
  simp [(hu c hc).2]

theorem visible_of_unrestricted {q : Ptr} {a : Alloc} {o : Nat} (hu : m.Unrestricted) :
    m.visible q a o = a.bytes o := by
  simp [visible, unwritten_of_unrestricted hu]

/-! ### Addresses -/

theorem toNat_ofNat_of_lt {o : Nat} (h : o < 2 ^ 63) : (BitVec.ofNat 64 o).toNat = o := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem Object.addr {b n o : Nat} (O : m.Object b n) (ho : o ≤ n) (t : List Tag) :
    (m.addr ⟨b, BitVec.ofNat 64 o, t⟩).toNat = (m.base b).toNat + o := by
  have := O.fits
  have hb : (b == 0) = false := by simpa using O.notNull
  simp only [Mem.addr, hb, Bool.false_eq_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Object.addr_ne_zero {b n o : Nat} (O : m.Object b n) (ho : o ≤ n) (t : List Tag) :
    m.addr ⟨b, BitVec.ofNat 64 o, t⟩ ≠ 0#64 := by
  intro h
  have h1 := O.addr ho t
  have h2 : (m.base b).toNat ≠ 0 := fun e => O.nonzero (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [h] at h1
  simp at h1
  omega

/-- `access` succeeds, for an access inside the allocation, aligned or at alignment 1. -/
theorem access_ok {q : Ptr} {a : Alloc} {n align : Nat} (ha : m.allocs q.block = some a)
    (hn : q.offset.toNat + n ≤ a.size) (hal : align = 1 ∨ (m.addr q).toNat % align = 0) :
    m.access (some q) n align = .ok (q, a) := by
  have h1 : ¬ q.offset.toNat + n > a.size := by omega
  have h2 : (align != 1 && (m.addr q).toNat % align != 0) = false := by
    rcases hal with h | h <;> simp [h]
  simp only [access, ha, h1, ite_false, h2, Bool.false_eq_true]

theorem Object.access {b n o k align : Nat} (O : m.Object b n) (h : o + k ≤ n) (t : List Tag)
    (hal : align = 1 ∨ ((m.base b).toNat + o) % align = 0) :
    ∃ a, m.access (some ⟨b, BitVec.ofNat 64 o, t⟩) k align = .ok (⟨b, BitVec.ofNat 64 o, t⟩, a) ∧
      m.allocs b = some a ∧ a.size = n := by
  obtain ⟨a, ha, hs⟩ := O.live
  have ho := toNat_ofNat_of_lt (o := o) (by have := O.small; omega)
  refine ⟨a, access_ok ha (by simp only [ho]; omega) ?_, ha, hs⟩
  rw [O.addr (by omega)]
  exact hal

/-! ### `getelementptr` -/

/-- Moving forward inside an object, as a field or an index does. -/
theorem Object.gep {b n o k : Nat} (O : m.Object b n) (h : o + k ≤ n) (t : List Tag) :
    m.gep (some ⟨b, BitVec.ofNat 64 o, t⟩) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some ⟨b, BitVec.ofNat 64 (o + k), t⟩ := by
  obtain ⟨a, ha, hs⟩ := O.live
  have := O.small
  have hf := O.fits
  have ho := toNat_ofNat_of_lt (o := o) (by omega)
  have r := gep_forward (m := m) (q := ⟨b, BitVec.ofNat 64 o, t⟩) (k := k) ha (by simp only [ho]; omega)
    (by omega) (by rw [O.addr (by omega)]; omega) (by omega)
  rw [r]
  simp [BitVec.ofNat_add]

/-- Moving back inside an object, as `p - k` does: an `inbounds` step by minus `k`. -/
theorem Object.gep_back {b n o k : Nat} (O : m.Object b n) (ho : o ≤ n) (hk : k ≤ o) (t : List Tag) :
    m.gep (some ⟨b, BitVec.ofNat 64 o, t⟩) (some (0#64 - BitVec.ofNat 64 k)) (inbounds := true) =
      some ⟨b, BitVec.ofNat 64 (o - k), t⟩ := by
  obtain ⟨a, ha, hs⟩ := O.live
  have := O.small
  have hf := O.fits
  have tk := toNat_ofNat_of_lt (o := k) (by omega)
  have to := toNat_ofNat_of_lt (o := o) (by omega)
  have haddr := O.addr ho t
  have hsum : BitVec.ofNat 64 o + (0#64 - BitVec.ofNat 64 k) = BitVec.ofNat 64 (o - k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hwrap : addressWraps (m.addr ⟨b, BitVec.ofNat 64 o, t⟩) (0#64 - BitVec.ofNat 64 k) = false := by
    by_cases k0 : k = 0
    · subst k0
      simp only [addressWraps, BitVec.sub_zero, BitVec.msb_zero, Bool.false_eq_true,
        ite_false, BitVec.uaddOverflow, BitVec.toNat_zero, decide_eq_false_iff_not, Nat.not_le]
      omega
    · have hmsb : (0#64 - BitVec.ofNat 64 k).msb = true := by
        simp only [BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_true_eq]
        omega
      have hneg : -(0#64 - BitVec.ofNat 64 k) = BitVec.ofNat 64 k := by
        simp
      simp only [addressWraps, hmsb, ite_true, hneg, BitVec.ult, haddr, tk, decide_eq_false_iff_not]
      omega
  have hmoved : (BitVec.ofNat 64 o + (0#64 - BitVec.ofNat 64 k)).toNat ≤ a.size := by
    rw [hsum, toNat_ofNat_of_lt (by omega)]; omega
  have hmoved' : (BitVec.ofNat 64 (o - k)).toNat ≤ a.size := by rw [← hsum]; exact hmoved
  have hbase : (BitVec.ofNat 64 o).toNat ≤ a.size := by rw [to]; omega
  simp only [Mem.gep, Bool.false_and, Bool.false_eq_true, ite_false, Bool.true_or, Bool.true_and, hwrap, ha,
    hsum, hbase, hmoved', and_self, ite_true]
  split <;> rfl

/-- `0 - k` with `nsw`, as the negation of a small offset comes out of the optimizer. -/
theorem neg_nsw {k : Nat} (h : k < 2 ^ 63) :
    Val.sub (some 0#64) (some (BitVec.ofNat 64 k)) (nsw := true) = some (0#64 - BitVec.ofNat 64 k) := by
  have tk := toNat_ofNat_of_lt (o := k) h
  have hm : (BitVec.ofNat 64 k).msb = false := by
    simp only [BitVec.msb_eq_decide, tk, decide_eq_false_iff_not]
    omega
  have : (0#64).ssubOverflow (BitVec.ofNat 64 k) = false := by
    generalize BitVec.ofNat 64 k = y at hm ⊢
    bv_decide
  simp [Val.sub, this]

/-- A 32-bit offset, widened. -/
theorem zext32 (x : BitVec 32) : Val.zext 64 (some x) = some (BitVec.ofNat 64 x.toNat) := by
  simp [Val.zext, BitVec.ofNat_toNat]

/-- The `align 1` attribute says nothing. -/
theorem aligned_one (p : PtrVal) : m.aligned 1 p = p := by
  cases p <;> simp [aligned, Nat.mod_one]

theorem Object.nonnull {b n o : Nat} (O : m.Object b n) (ho : o ≤ n) (t : List Tag) :
    m.nonnull (some ⟨b, BitVec.ofNat 64 o, t⟩) = some ⟨b, BitVec.ofNat 64 o, t⟩ := by
  simp [Mem.nonnull, O.addr_ne_zero ho t]

theorem Object.dereferenceable {b n o k : Nat} (O : m.Object b n) (h : o + k ≤ n) (t : List Tag)
    (x : Outcome α) : m.dereferenceable (some ⟨b, BitVec.ofNat 64 o, t⟩) k x = x := by
  obtain ⟨a, hacc, _⟩ := O.access h t (align := 1) (.inl rfl)
  simp [Mem.dereferenceable, hacc]

/-! ### Loads -/

/-- The bytes of a little-endian number, read back. -/
theorem collect_bytes (x n : Nat) :
    collect ((List.range n).map fun i => Byte.val (BitVec.ofNat 8 (x >>> (8 * i)))) =
      .ok (some (x % 2 ^ (8 * n))) := by
  induction n generalizing x with
  | zero => simp [collect, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have e : ((fun i => Byte.val (BitVec.ofNat 8 (x >>> (8 * i)))) ∘ Nat.succ) =
        fun i => Byte.val (BitVec.ofNat 8 ((x >>> 8) >>> (8 * i))) := by
      funext i
      simp only [Function.comp, ← Nat.shiftRight_add]
      congr 3
      omega
    rw [e]
    simp only [collect, ih, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat]
    congr
    rw [Nat.shiftRight_eq_div_pow, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

theorem read_holds {w : Nat} {q : Ptr} {a : Alloc} {o : Nat} {v : BitVec w} (hu : m.Unrestricted)
    (hb : ∀ i, i < w / 8 → a.bytes (o + i) = intByte v i) :
    m.read q a o (w / 8) = (List.range (w / 8)).map fun i => Byte.val (BitVec.ofNat 8 (v.toNat >>> (8 * i))) := by
  simp only [read]
  apply List.map_congr_left
  intro i hi
  rw [visible_of_unrestricted hu, hb i (List.mem_range.mp hi)]
  rfl

/-- A load of an integer that memory holds. -/
theorem Object.loadInt {w b n o align : Nat} {v : BitVec w} {t : List Tag} (O : m.Object b n)
    (H : m.HoldsInt b o v) (hn : o + w / 8 ≤ n) (hw : w % 8 = 0)
    (hal : align = 1 ∨ ((m.base b).toNat + o) % align = 0) (hu : m.Unrestricted)
    (ht : m.TagsAllow ⟨b, BitVec.ofNat 64 o, t⟩ false) :
    m.loadInt w (some ⟨b, BitVec.ofNat 64 o, t⟩) align = Outcome.ok (some v) := by
  obtain ⟨a, hacc, ha, _⟩ := O.access hn t hal
  obtain ⟨a', ha', hb⟩ := H
  rw [ha] at ha'
  cases ha'
  have ho := toNat_ofNat_of_lt (o := o) (by have := O.small; omega)
  have hv : BitVec.ofNat w (v.toNat % 2 ^ (8 * (w / 8))) = v := by
    rw [show 8 * (w / 8) = w by omega, Nat.mod_eq_of_lt v.isLt]
    simp
  simp only [Mem.loadInt, hacc, check_of_unrestricted hu ht, ho, read_holds hu hb, collect_bytes, hv]

/-- A load of a pointer that memory holds. -/
theorem Object.loadPtr {b n o align : Nat} {p : Ptr} {t : List Tag} (O : m.Object b n) (H : m.HoldsPtr b o p)
    (hn : o + 8 ≤ n) (hal : align = 1 ∨ ((m.base b).toNat + o) % align = 0) (hu : m.Unrestricted)
    (ht : m.TagsAllow ⟨b, BitVec.ofNat 64 o, t⟩ false) :
    m.loadPtr (some ⟨b, BitVec.ofNat 64 o, t⟩) align = Outcome.ok (some p) := by
  obtain ⟨a, hacc, ha, _⟩ := O.access hn t hal
  obtain ⟨a', ha', hb⟩ := H
  rw [ha] at ha'
  cases ha'
  have ho := toNat_ofNat_of_lt (o := o) (by have := O.small; omega)
  have hr : m.read ⟨b, BitVec.ofNat 64 o, t⟩ a o 8 = (List.range 8).map fun i => Byte.ptr p i := by
    simp only [read]
    apply List.map_congr_left
    intro i hi
    rw [visible_of_unrestricted hu, hb i (List.mem_range.mp hi)]
  simp only [Mem.loadPtr, hacc, check_of_unrestricted hu ht, ho, hr]
  simp [List.range, List.range.loop, assemblePtr, List.zipIdx, Outcome.ok]

/-! ### What changed

`Changes m m' touched` says `m'` is `m` with at most the bytes in `touched` changed. It's how a safety
theorem says what a function wrote, and how a proof knows a load after a store still sees what it saw. -/

/-- `m'` is `m` with at most the bytes in `touched` changed, as allocation and offset. Every allocation keeps
whether it exists, its size and its flags, and nothing else about memory changes: not the layout, the next
allocation, the current frame, the allocator's choices or the calls. A whole call ends with `nextCall` one
higher, so a theorem about one says `Changes m.afterCall m' touched`. -/
structure Changes (m m' : Mem) (touched : Nat → Nat → Prop) : Prop where
  allocs : ∀ b, Option.Rel (fun a a' => Alloc.Agree a a' (touched b)) (m.allocs b) (m'.allocs b)
  base : m'.base = m.base
  next : m'.next = m.next
  frame : m'.frame = m.frame
  failAlloc : m'.failAlloc = m.failAlloc
  calls : m'.calls = m.calls
  nextCall : m'.nextCall = m.nextCall

namespace Changes

variable {T T' : Nat → Nat → Prop}

theorem refl (m : Mem) (T : Nat → Nat → Prop) : Changes m m T where
  allocs b := by
    cases h : m.allocs b
    · exact .none
    · exact .some (Alloc.Agree.refl _ _)
  base := rfl
  next := rfl
  frame := rfl
  failAlloc := rfl
  calls := rfl
  nextCall := rfl

theorem trans {T'' : Nat → Nat → Prop} (h : Changes m m' T) (h' : Changes m' m'' T')
    (hT : ∀ b i, T b i ∨ T' b i → T'' b i) : Changes m m'' T'' where
  allocs b := by
    have h1 := h.allocs b
    have h2 := h'.allocs b
    revert h1 h2
    generalize m.allocs b = x
    generalize m'.allocs b = y
    generalize m''.allocs b = z
    intro h1 h2
    cases h1 with
    | none => cases h2; exact .none
    | some r1 =>
      cases h2 with
      | some r2 => exact .some (r1.trans r2 (hT b))
  base := h'.base.trans h.base
  next := h'.next.trans h.next
  frame := h'.frame.trans h.frame
  failAlloc := h'.failAlloc.trans h.failAlloc
  calls := h'.calls.trans h.calls
  nextCall := h'.nextCall.trans h.nextCall

theorem mono (h : Changes m m' T) (hT : ∀ b i, T b i → T' b i) : Changes m m' T' where
  allocs b := by
    have h1 := h.allocs b
    revert h1
    generalize m.allocs b = x
    generalize m'.allocs b = y
    intro h1
    cases h1 with
    | none => exact .none
    | some r =>
      exact .some ⟨r.size, r.readonly, r.heap, r.stack, fun i hi => r.bytes i fun t => hi (hT b i t)⟩
  base := h.base
  next := h.next
  frame := h.frame
  failAlloc := h.failAlloc
  calls := h.calls
  nextCall := h.nextCall

/-- Counting calls from elsewhere changes nothing else. -/
theorem shift (h : Changes m m' T) (k : Nat) :
    Changes { m with nextCall := m.nextCall + k } { m' with nextCall := m'.nextCall + k } T :=
  { h with nextCall := by simp [h.nextCall] }

/-- An allocation in `m`, and what it became. -/
theorem alloc (h : Changes m m' T) {b : Nat} {a : Alloc} (ha : m.allocs b = some a) :
    ∃ a', m'.allocs b = some a' ∧ Alloc.Agree a a' (T b) := by
  have h1 := h.allocs b
  revert h1
  rw [ha]
  generalize m'.allocs b = y
  intro h1
  cases h1 with
  | some r => exact ⟨_, rfl, r⟩

/-- An allocation that's gone stays gone. -/
theorem gone (h : Changes m m' T) {b : Nat} (ha : m.allocs b = none) : m'.allocs b = none := by
  have h1 := h.allocs b
  revert h1
  rw [ha]
  generalize m'.allocs b = y
  intro h1
  cases h1
  rfl

theorem addr (h : Changes m m' T) : m'.addr = m.addr := by
  funext p
  simp [Mem.addr, h.base]

theorem object (h : Changes m m' T) {b n : Nat} (O : m.Object b n) : m'.Object b n := by
  obtain ⟨a, ha, hs⟩ := O.live
  obtain ⟨a', ha', r⟩ := h.alloc ha
  exact ⟨⟨a', ha', r.size.trans hs⟩, O.notNull, O.small, by rw [h.base]; exact O.nonzero,
    by rw [h.base]; exact O.fits⟩

theorem writable (h : Changes m m' T) {b : Nat} (W : m.Writable b) : m'.Writable b := by
  obtain ⟨a, ha, hr⟩ := W
  obtain ⟨a', ha', r⟩ := h.alloc ha
  exact ⟨a', ha', r.readonly.trans hr⟩

theorem holdsInt (h : Changes m m' T) {w b o : Nat} {v : BitVec w} (H : m.HoldsInt b o v)
    (hT : ∀ i, i < w / 8 → ¬ T b (o + i)) : m'.HoldsInt b o v := by
  obtain ⟨a, ha, hb⟩ := H
  obtain ⟨a', ha', r⟩ := h.alloc ha
  exact ⟨a', ha', fun i hi => (r.bytes _ (hT i hi)).trans (hb i hi)⟩

theorem holdsPtr (h : Changes m m' T) {b o : Nat} {p : Ptr} (H : m.HoldsPtr b o p)
    (hT : ∀ i, i < 8 → ¬ T b (o + i)) : m'.HoldsPtr b o p := by
  obtain ⟨a, ha, hb⟩ := H
  obtain ⟨a', ha', r⟩ := h.alloc ha
  exact ⟨a', ha', fun i hi => (r.bytes _ (hT i hi)).trans (hb i hi)⟩

theorem unrestricted (h : Changes m m' T) (hu : m.Unrestricted) : m'.Unrestricted := by
  intro c hc; rw [h.calls] at hc; exact hu c hc

theorem isRunning (h : Changes m m' T) (c : Nat) : m'.isRunning c = m.isRunning c := by
  simp [Mem.isRunning, h.calls]

theorem tagsAllow (h : Changes m m' T) {q : Ptr} {write : Bool} (ht : m.TagsAllow q write) :
    m'.TagsAllow q write := by
  intro t hq
  have := ht t hq
  simp only [tagRule, h.isRunning] at this ⊢
  exact this

end Changes

/-! ### Stores and copies -/

theorem write_calls {q : Ptr} {a : Alloc} {n : Nat} {f : Nat → Byte} (hu : m.Unrestricted) :
    (m.write q a n f).calls = m.calls := by
  simp only [write]
  conv => rhs; rw [← List.map_id m.calls]
  apply List.map_congr_left
  intro c hc
  simp [(hu c hc).2]

/-- A write changes only the bytes it writes. -/
theorem write_changes {q : Ptr} {a : Alloc} {n : Nat} {f : Nat → Byte} (ha : m.allocs q.block = some a)
    (hu : m.Unrestricted) :
    Changes m (m.write q a n f) (fun b i => b = q.block ∧ q.offset.toNat ≤ i ∧ i < q.offset.toNat + n) where
  allocs b := by
    by_cases hb : b = q.block
    · subst hb
      simp only [write, setAlloc, beq_self_eq_true, ite_true, ha]
      refine .some ⟨rfl, rfl, rfl, rfl, fun i hi => ?_⟩
      simp only [true_and] at hi
      simp [hi]
    · have : (b == q.block) = false := by simpa using hb
      simp only [write, setAlloc, this, Bool.false_eq_true, ite_false]
      cases m.allocs b
      · exact .none
      · exact .some (Alloc.Agree.refl _ _)
  base := rfl
  next := rfl
  frame := rfl
  failAlloc := rfl
  calls := write_calls hu
  nextCall := rfl

/-- A store of an integer inside a writable object: it changes those bytes, which then hold it. -/
theorem Object.storeInt {w b n o align : Nat} {t : List Tag} (O : m.Object b n) (W : m.Writable b)
    (hn : o + w / 8 ≤ n) (hal : align = 1 ∨ ((m.base b).toNat + o) % align = 0) (hu : m.Unrestricted)
    (ht : m.TagsAllow ⟨b, BitVec.ofNat 64 o, t⟩ true) (x : BitVec w) :
    ∃ m', m.storeInt (some ⟨b, BitVec.ofNat 64 o, t⟩) (some x) align = Outcome.ok m' ∧
      Changes m m' (fun b' i => b' = b ∧ o ≤ i ∧ i < o + w / 8) ∧ m'.HoldsInt b o x := by
  obtain ⟨a, hacc, ha, _⟩ := O.access hn t hal
  obtain ⟨a', ha', hr⟩ := W
  rw [ha] at ha'
  cases ha'
  have ho := toNat_ofNat_of_lt (o := o) (by have := O.small; omega)
  refine ⟨m.write ⟨b, BitVec.ofNat 64 o, t⟩ a (w / 8) fun i => intByte x i, ?_, ?_, ?_⟩
  · simp only [Mem.storeInt, hacc, hr, check_of_unrestricted hu ht, Bool.false_eq_true, ite_false]
  · have := write_changes (q := ⟨b, BitVec.ofNat 64 o, t⟩) (n := w / 8) (f := fun i => intByte x i) ha hu
    simpa only [ho] using this
  · refine ⟨{ a with bytes := fun i =>
        (if (BitVec.ofNat 64 o).toNat ≤ i ∧ i < (BitVec.ofNat 64 o).toNat + w / 8 then
          intByte x (i - (BitVec.ofNat 64 o).toNat) else a.bytes i) },
      by simp only [write, setAlloc, beq_self_eq_true, ite_true], fun i hi => ?_⟩
    simp only [ho]
    simp [show o ≤ o + i by omega, show o + i < o + w / 8 by omega]

/-- `llvm.memcpy` between two objects: it changes only the bytes it copies to. -/
theorem Object.memcpy {d nd od s ns os k : Nat} {td ts : List Tag} (Od : m.Object d nd) (W : m.Writable d)
    (hd : od + k ≤ nd) (Os : m.Object s ns) (hs : os + k ≤ ns) (hne : d ≠ s) (hu : m.Unrestricted)
    (htd : m.TagsAllow ⟨d, BitVec.ofNat 64 od, td⟩ true) (hts : m.TagsAllow ⟨s, BitVec.ofNat 64 os, ts⟩ false) :
    ∃ m', m.memcpy (some ⟨d, BitVec.ofNat 64 od, td⟩) (some ⟨s, BitVec.ofNat 64 os, ts⟩)
        (some (BitVec.ofNat 64 k)) = Outcome.ok m' ∧ Changes m m' (fun b i => b = d ∧ od ≤ i ∧ i < od + k) := by
  have hk := toNat_ofNat_of_lt (o := k) (by have := Od.small; omega)
  by_cases k0 : k = 0
  · subst k0
    exact ⟨m, by simp [Mem.memcpy, Outcome.ok], Changes.refl m _⟩
  have hk0 : (BitVec.ofNat 64 k == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp only [hk, BitVec.toNat_zero] at this
    exact k0 this
  obtain ⟨da, haccd, had, _⟩ := Od.access hd td (align := 1) (.inl rfl)
  obtain ⟨sa, hacss, has, _⟩ := Os.access hs ts (align := 1) (.inl rfl)
  obtain ⟨a', ha', hr⟩ := W
  rw [had] at ha'
  cases ha'
  have hod := toNat_ofNat_of_lt (o := od) (by have := Od.small; omega)
  have hne' : (d == s) = false := by simpa using hne
  refine ⟨m.write ⟨d, BitVec.ofNat 64 od, td⟩ da k fun i =>
    m.visible ⟨s, BitVec.ofNat 64 os, ts⟩ sa ((BitVec.ofNat 64 os).toNat + i), ?_, ?_⟩
  · simp only [Mem.memcpy, hk0, hk, Bool.false_eq_true, ite_false, haccd, hacss, hr, hne', Bool.false_and,
      check_of_unrestricted hu hts, check_of_unrestricted hu htd]
  · have := write_changes (q := ⟨d, BitVec.ofNat 64 od, td⟩) (n := k)
      (f := fun i => m.visible ⟨s, BitVec.ofNat 64 os, ts⟩ sa ((BitVec.ofNat 64 os).toNat + i)) had hu
    simpa only [hod] using this

/-! ### Accesses the model rules out -/

/-- An access that runs past the end of its allocation. -/
theorem access_past_end {q : Ptr} {a : Alloc} {n align : Nat} (ha : m.allocs q.block = some a)
    (h : a.size < q.offset.toNat + n) : m.access (some q) n align = .error .badAccess := by
  simp [access, ha, show q.offset.toNat + n > a.size from h]

/-- An access to an allocation that's gone: freed, out of its function's frame, or never made. -/
theorem access_gone {q : Ptr} {n align : Nat} (ha : m.allocs q.block = none) :
    m.access (some q) n align = .error .badAccess := by
  simp [access, ha]

/-- `dereferenceable` of an allocation that's gone. -/
theorem dereferenceable_gone {q : Ptr} {n : Nat} (ha : m.allocs q.block = none) (x : Outcome α) :
    m.dereferenceable (some q) n x = Outcome.ub .badAccess := by
  simp [dereferenceable, access_gone ha]

/-- A copy that runs past the end of where it copies to. -/
theorem memcpy_past_end {d : Ptr} {da : Alloc} {src : PtrVal} {k : Nat} (hd : m.allocs d.block = some da)
    (hk0 : k ≠ 0) (hk : k < 2 ^ 64) (h : da.size < d.offset.toNat + k) :
    m.memcpy (some d) src (some (BitVec.ofNat 64 k)) = Outcome.ub .badAccess := by
  have tk : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  have hk0' : (BitVec.ofNat 64 k == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [tk, BitVec.toNat_zero] at this
    exact hk0 this
  simp only [Mem.memcpy, hk0', tk, Bool.false_eq_true, ite_false, access_past_end hd h]

/-- `p - k` with `inbounds`, for `k` more than `p`'s offset: before the start of its allocation, which is poison. -/
theorem Object.gep_back_out {b n o k : Nat} (O : m.Object b n) (ho : o ≤ n) (hk : o < k) (hk63 : k < 2 ^ 63)
    (t : List Tag) :
    m.gep (some ⟨b, BitVec.ofNat 64 o, t⟩) (some (0#64 - BitVec.ofNat 64 k)) (inbounds := true) = none := by
  obtain ⟨a, ha, hs⟩ := O.live
  have := O.small
  have hmoved : ¬ (BitVec.ofNat 64 o + (0#64 - BitVec.ofNat 64 k)).toNat ≤ a.size := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hd : (0#64 - BitVec.ofNat 64 k != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  simp only [Mem.gep, Bool.false_and, Bool.false_eq_true, ite_false, Bool.true_or, Bool.true_and, hd, ite_true,
    ha, hmoved, and_false]
  split <;> rfl

/-! ### Calls -/

/-- `m'` has the same allocations as `m`, at the same addresses: all that `Object`, `Writable`, `HoldsInt`
and `HoldsPtr` depend on. -/
structure SameObjects (m m' : Mem) : Prop where
  allocs : ∀ b, m'.allocs b = m.allocs b
  base : m'.base = m.base

namespace SameObjects

theorem object (h : SameObjects m m') {b n : Nat} (O : m.Object b n) : m'.Object b n := by
  obtain ⟨a, ha, hs⟩ := O.live
  exact ⟨⟨a, (h.allocs b).trans ha, hs⟩, O.notNull, O.small, by rw [h.base]; exact O.nonzero,
    by rw [h.base]; exact O.fits⟩

theorem writable (h : SameObjects m m') {b : Nat} (W : m.Writable b) : m'.Writable b := by
  obtain ⟨a, ha, hr⟩ := W
  exact ⟨a, (h.allocs b).trans ha, hr⟩

theorem holdsInt (h : SameObjects m m') {w b o : Nat} {v : BitVec w} (H : m.HoldsInt b o v) :
    m'.HoldsInt b o v := by
  obtain ⟨a, ha, hb⟩ := H
  exact ⟨a, (h.allocs b).trans ha, hb⟩

theorem holdsPtr (h : SameObjects m m') {b o : Nat} {p : Ptr} (H : m.HoldsPtr b o p) : m'.HoldsPtr b o p := by
  obtain ⟨a, ha, hb⟩ := H
  exact ⟨a, (h.allocs b).trans ha, hb⟩

end SameObjects

/-- Memory inside a call of a function that promised nothing about memory: one more running call, which
restricts nothing and tracks nothing. -/
abbrev enter (m : Mem) : Mem :=
  { m with
    calls := { id := m.nextCall, effects := {}, start := m.next, tracked := false } :: m.calls
    nextCall := m.nextCall + 1 }

theorem unrestricted_enter (hu : m.Unrestricted) : m.enter.Unrestricted := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨rfl, rfl⟩
  · exact hu c hc

theorem isRunning_enter : m.enter.isRunning m.nextCall = true := by
  simp [isRunning]

/-- A call of a function that promised nothing about memory, whose body returns having changed only `T`: the
call returns the same, having changed only `T`, with the call over. -/
theorem call_unrestricted {k : Mem → Nat → Outcome (α × Mem)} {r : α} {T : Nat → Nat → Prop}
    (hk : k m.enter m.nextCall = Outcome.ok (r, m')) (F : Changes m.enter m' T) :
    ∃ m'', m.call {} false k = Outcome.ok (r, m'') ∧ Changes m.afterCall m'' T ∧ SameObjects m' m'' := by
  have hc : m'.calls = { id := m.nextCall, effects := {}, start := m.next, tracked := false } :: m.calls :=
    F.calls
  refine ⟨{ m' with calls := m.calls, allocs := m'.allocs }, ?_, ?_, ⟨fun _ => rfl, rfl⟩⟩
  · simp only [call, hk, andThen_ok, hc, List.any_nil]
  · exact { F with calls := rfl, nextCall := F.nextCall }

/-- A call whose body stops, stops the same way. -/
theorem call_stop {k : Mem → Nat → Outcome (α × Mem)} {e : Effects} {tracked : Bool} {r : Stop}
    (hk : k { m with
        calls := { id := m.nextCall, effects := e, start := m.next, tracked } :: m.calls
        nextCall := m.nextCall + 1 } m.nextCall = some (.error r)) :
    m.call e tracked k = some (.error r) := by
  simp only [call, hk]
  rfl

end Mem

end IRLean
