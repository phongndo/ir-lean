import IRLean.MemRefine
import IRLean.CutPromised

/-! # Executable memory

`ExecMem` is memory as tests run it: each allocation's bytes in a `ByteArray`, and the allocations in an `Array`, so a
load reads its bytes directly and a store changes them in place. `Mem`, in `IRLean/Mem.lean`, stays what every
theorem is about. Its bytes are functions, and running a store wraps one in another, so a load walks back through
every earlier store to its allocation.

`ExecMem.toMem` reads one back as the `Mem` it stands for, and each operation here is proved to agree with `Mem`'s
through it: for one that changes memory, `Mem.op x.toMem args = Outcome.map toMem (ExecMem.op x args)`, and for one that
doesn't, the two are equal. Operations that only read are `Mem`'s own, run on `x.toMem`, which is cheap to build and
to read from, since its allocations are lookups into `x`'s arrays. So they agree by definition, and only the operations
that make new memory are written again here. The last section takes agreement from blocks to whole runs.

None of this uses `implemented_by` or `extern`: the code tests run is the code the kernel checked.

`docs/memory.md#executable-memory` says how tests use this, and why what they find holds of `Mem`. -/

namespace IRLean

/-- An outcome with `f` applied to its result, if it has one. -/
def Outcome.map (f : α → β) : Outcome α → Outcome β
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok a) => some (.ok (f a))

@[simp] theorem Outcome.map_none (f : α → β) : Outcome.map f none = none := rfl
@[simp] theorem Outcome.map_error (f : α → β) (e : Stop) : Outcome.map f (some (.error e)) = some (.error e) := rfl
@[simp] theorem Outcome.map_ok (f : α → β) (a : α) : Outcome.map f (Outcome.ok a) = Outcome.ok (f a) := rfl
@[simp] theorem Outcome.map_ub (f : α → β) (r : UB) : Outcome.map f (Outcome.ub r) = Outcome.ub r := rfl
@[simp] theorem Outcome.map_stop (f : α → β) (r : ModelStop) : Outcome.map f (Outcome.stop r) = Outcome.stop r := rfl

theorem Outcome.map_andThen (f : β → γ) (o : Outcome α) (k : α → Outcome β) :
    Outcome.map f (andThen o k) = andThen o fun a => Outcome.map f (k a) := by
  rcases o with _ | _ | _ <;> rfl

theorem Outcome.andThen_map (f : α → β) (o : Outcome α) (k : β → Outcome γ) :
    andThen (Outcome.map f o) k = andThen o fun a => k (f a) := by
  rcases o with _ | _ | _ <;> rfl

theorem Outcome.map_map (f : α → β) (g : β → γ) (o : Outcome α) :
    Outcome.map g (Outcome.map f o) = Outcome.map (fun a => g (f a)) o := by
  rcases o with _ | _ | _ <;> rfl

theorem Outcome.map_id' (o : Outcome α) : Outcome.map (fun a => a) o = o := by
  rcases o with _ | _ | _ <;> rfl

/-- One allocation's bytes. -/
structure ExecBytes where
  /-- Two entries for each byte: what kind it is, and its value. A kind of 1 is a value, 2 poison, 3 a byte of a
  pointer, and anything else uninitialized, so zeros are uninitialized memory. -/
  data : ByteArray
  /-- For a byte of a pointer: which pointer, and which byte of it. Empty until a pointer is stored. -/
  ptrs : Array (Option (Ptr × Nat))
  /-- The bytes from `data.size / 2` on. Only an allocation too big to hold whole, or the bytes past an
  allocation's end, which nothing reads, are here. -/
  rest : Nat → Byte

namespace ExecBytes

/-- The most bytes of one allocation held in `data`, 64 MiB. Bytes past it are in `rest`, which is slow. -/
def cap : Nat := 67108864

/-- A byte of a pointer, as `ptrs` holds it. -/
def ptrByte : Option (Option (Ptr × Nat)) → Byte
  | some (some (p, j)) => .ptr p j
  | _ => .uninit

/-- A byte, from its kind, its value, and its entry in `ptrs`. -/
def decode (k v : UInt8) (e : Option (Option (Ptr × Nat))) : Byte :=
  if k == 1 then .val v.toBitVec
  else if k == 2 then .poison
  else if k == 3 then ptrByte e
  else .uninit

/-- Byte `i`. -/
def get (s : ExecBytes) (i : Nat) : Byte :=
  if h : 2 * i + 1 < s.data.size then decode (s.data[2 * i]'(by omega)) s.data[2 * i + 1] s.ptrs[i]?
  else s.rest i

/-- `a`, made at least `n` long. -/
def grow (a : Array (Option (Ptr × Nat))) (n : Nat) : Array (Option (Ptr × Nat)) :=
  if a.size < n then a ++ Array.replicate (n - a.size) none else a

/-- Sets byte `i`. -/
def set (s : ExecBytes) (i : Nat) (b : Byte) : ExecBytes :=
  if 2 * i + 1 < s.data.size then
    match s, b with
    | ⟨data, ptrs, rest⟩, .uninit => ⟨data.set! (2 * i) 0, ptrs, rest⟩
    | ⟨data, ptrs, rest⟩, .poison => ⟨data.set! (2 * i) 2, ptrs, rest⟩
    | ⟨data, ptrs, rest⟩, .val v => ⟨(data.set! (2 * i) 1).set! (2 * i + 1) (UInt8.ofBitVec v), ptrs, rest⟩
    | ⟨data, ptrs, rest⟩, .ptr p j => ⟨data.set! (2 * i) 3, (grow ptrs (data.size / 2)).set! i (some (p, j)), rest⟩
  else
    match s with
    | ⟨data, ptrs, rest⟩ => ⟨data, ptrs, fun k => if k = i then b else rest k⟩

/-- Sets bytes `o + j` to `f j`, for `j` from `i` up to `i + n`. -/
def writeFrom (f : Nat → Byte) (o : Nat) : (i n : Nat) → ExecBytes → ExecBytes
  | _, 0, s => s
  | i, n + 1, s => writeFrom f o (i + 1) n (s.set (o + i) (f i))

/-- Sets bytes `o + i` to `f i`, for `i` below `n`. -/
def writeRange (s : ExecBytes) (o n : Nat) (f : Nat → Byte) : ExecBytes := writeFrom f o 0 n s

/-- `a` with `n` zeros pushed. -/
def zeros : Nat → ByteArray → ByteArray
  | 0, a => a
  | n + 1, a => zeros n (a.push 0)

/-- `n` bytes, all uninitialized, and every byte past them `rest`. -/
def blank (n : Nat) (rest : Nat → Byte) : ExecBytes :=
  ⟨zeros (2 * min n cap) (ByteArray.emptyWithCapacity (2 * min n cap)), #[], rest⟩

/-- Uninitialized memory, for an allocation of `n` bytes. -/
def uninit (n : Nat) : ExecBytes := blank n fun _ => .uninit

/-- Byte `i` is `f i`, holding the first `n` in `data`. -/
def ofFn (n : Nat) (f : Nat → Byte) : ExecBytes := (blank n f).writeRange 0 (min n cap) f

/-- Sets the bytes from `i` up to `i + n` that `P` holds of to uninitialized. -/
def clearFrom (P : Nat → Bool) : (i n : Nat) → ExecBytes → ExecBytes
  | _, 0, s => s
  | i, n + 1, s => clearFrom P (i + 1) n (if P i then s.set i .uninit else s)

/-- Every byte `P` holds of, uninitialized. -/
def clearWhere (s : ExecBytes) (P : Nat → Bool) : ExecBytes :=
  match clearFrom P 0 (s.data.size / 2) s with
  | ⟨data, ptrs, _⟩ => ⟨data, ptrs, fun i => if P i then .uninit else s.rest i⟩

/-! ### What each of these does to the bytes -/

private theorem ba_size_set! (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  rcases a with ⟨d⟩
  show (d.set! i v).size = d.size
  simp [Array.set!_eq_setIfInBounds]

private theorem ba_get_set! (a : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (h : j < (a.set! i v).size) :
    (a.set! i v)[j] = if i = j then v else a[j]'(by rw [ba_size_set!] at h; exact h) := by
  rcases a with ⟨d⟩
  show (d.set! i v)[j]'h = if i = j then v else d[j]'(by rw [ba_size_set!] at h; exact h)
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]

private theorem ba_size_push (a : ByteArray) (v : UInt8) : (a.push v).size = a.size + 1 := by
  rcases a with ⟨d⟩
  show (d.push v).size = d.size + 1
  simp

private theorem ba_get_push (a : ByteArray) (v : UInt8) (j : Nat) (h : j < (a.push v).size) :
    (a.push v)[j] = if hj : j < a.size then a[j] else v := by
  rcases a with ⟨d⟩
  show (d.push v)[j]'h = if hj : j < d.size then d[j] else v
  rw [Array.getElem_push]

theorem decode_congr (k v : UInt8) {e e' : Option (Option (Ptr × Nat))} (h : ptrByte e = ptrByte e') :
    decode k v e = decode k v e' := by
  simp only [decode, h]

private theorem ba_size_empty (c : Nat) : (ByteArray.emptyWithCapacity c).size = 0 := rfl

theorem get_lt (s : ExecBytes) (i : Nat) (h : 2 * i + 1 < s.data.size) :
    s.get i = decode (s.data[2 * i]'(by omega)) s.data[2 * i + 1] s.ptrs[i]? := by
  simp only [get, dite_eq_left h]

theorem get_ge (s : ExecBytes) (i : Nat) (h : ¬ 2 * i + 1 < s.data.size) : s.get i = s.rest i := by
  simp only [get, dite_eq_right h]

theorem size_set (s : ExecBytes) (i : Nat) (b : Byte) : (s.set i b).data.size = s.data.size := by
  rcases s with ⟨data, ptrs, rest⟩
  unfold set
  split
  · cases b <;> simp only [ba_size_set!]
  · rfl

theorem ptrByte_grow (a : Array (Option (Ptr × Nat))) (n j : Nat) : ptrByte (grow a n)[j]? = ptrByte a[j]? := by
  unfold grow
  split
  · rw [Array.getElem?_append]
    split
    · rfl
    · rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega)]
      split <;> rfl
  · rfl

theorem get_set (s : ExecBytes) (i : Nat) (b : Byte) (j : Nat) :
    (s.set i b).get j = if j = i then b else s.get j := by
  have hsz := size_set s i b
  rcases s with ⟨data, ptrs, rest⟩
  by_cases hi : 2 * i + 1 < data.size
  · by_cases hj : 2 * j + 1 < data.size
    · rw [get_lt _ _ (by rw [hsz]; exact hj), get_lt _ _ hj]
      by_cases e : j = i
      · subst e
        rw [ite_eq_left rfl]
        cases b with
        | uninit => simp only [set, ite_eq_left hi, ba_get_set!]; simp [decode]
        | poison => simp only [set, ite_eq_left hi, ba_get_set!]; simp [decode]
        | val v => simp only [set, ite_eq_left hi, ba_get_set!]; simp [decode]
        | ptr p k =>
          have hg : j < (grow ptrs (data.size / 2)).size := by
            unfold grow; split
            · simp; omega
            · omega
          simp only [set, ite_eq_left hi, ba_get_set!]
          simp [decode, Array.set!_eq_setIfInBounds, hg, ptrByte]
      · rw [ite_eq_right e]
        have h1 : ¬ 2 * i = 2 * j := by omega
        have h2 : ¬ 2 * i = 2 * j + 1 := by omega
        have h3 : ¬ 2 * i + 1 = 2 * j := by omega
        have h4 : ¬ 2 * i + 1 = 2 * j + 1 := by omega
        have h5 : ¬ i = j := fun h => e h.symm
        cases b with
        | uninit => simp only [set, ite_eq_left hi, ba_get_set!, h1, h2, ite_false]
        | poison => simp only [set, ite_eq_left hi, ba_get_set!, h1, h2, ite_false]
        | val v => simp only [set, ite_eq_left hi, ba_get_set!, h1, h2, h3, h4, ite_false]
        | ptr p k =>
          simp only [set, ite_eq_left hi, ba_get_set!, h1, h2, ite_false, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds, h5]
          exact decode_congr _ _ (ptrByte_grow _ _ _)
    · rw [get_ge _ _ (by rw [hsz]; exact hj), get_ge _ _ hj, ite_eq_right (by omega)]
      cases b <;> simp only [set, ite_eq_left hi]
  · have e : ¬ 2 * i + 1 < (ExecBytes.mk data ptrs rest).data.size := hi
    by_cases hj : 2 * j + 1 < data.size
    · rw [get_lt _ _ (by rw [hsz]; exact hj), get_lt _ _ hj, ite_eq_right (by omega)]
      simp only [set, ite_eq_right e]
    · rw [get_ge _ _ (by rw [hsz]; exact hj), get_ge _ _ hj]
      simp only [set, ite_eq_right e]

theorem size_writeFrom (f : Nat → Byte) (o i n : Nat) (s : ExecBytes) :
    (writeFrom f o i n s).data.size = s.data.size := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [writeFrom, ih, size_set]

theorem get_writeFrom (f : Nat → Byte) (o i n : Nat) (s : ExecBytes) (j : Nat) :
    (writeFrom f o i n s).get j = if o + i ≤ j ∧ j < o + i + n then f (j - o) else s.get j := by
  induction n generalizing i s with
  | zero =>
    rw [ite_eq_right (by omega)]; rfl
  | succ n ih =>
    simp only [writeFrom, ih, get_set]
    by_cases h1 : o + (i + 1) ≤ j ∧ j < o + (i + 1) + n
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      by_cases e : j = o + i
      · rw [ite_eq_left e, ite_eq_left (by omega)]; congr 1; omega
      · rw [ite_eq_right e]
        by_cases h2 : o + i ≤ j ∧ j < o + i + (n + 1)
        · omega
        · rw [ite_eq_right h2]

theorem size_writeRange (s : ExecBytes) (o n : Nat) (f : Nat → Byte) :
    (s.writeRange o n f).data.size = s.data.size := size_writeFrom ..

theorem get_writeRange (s : ExecBytes) (o n : Nat) (f : Nat → Byte) (j : Nat) :
    (s.writeRange o n f).get j = if o ≤ j ∧ j < o + n then f (j - o) else s.get j := by
  simp [writeRange, get_writeFrom]

/-- What a write of `n` bytes at `o` does, as `Mem.write` says it. -/
theorem get_writeRange_eq (s : ExecBytes) (o n : Nat) (f : Nat → Byte) :
    (s.writeRange o n f).get = fun i => if o ≤ i ∧ i < o + n then f (i - o) else s.get i := by
  funext j; exact get_writeRange s o n f j

theorem size_zeros (n : Nat) (a : ByteArray) : (zeros n a).size = a.size + n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [zeros, ih, ba_size_push]; omega

theorem get_zeros (n : Nat) (a : ByteArray) (j : Nat) (h : j < (zeros n a).size) (ha : a.size ≤ j) :
    (zeros n a)[j] = 0 := by
  induction n generalizing a with
  | zero => rw [size_zeros] at h; omega
  | succ n ih =>
    simp only [zeros] at h ⊢
    by_cases hj : a.size + 1 ≤ j
    · exact ih _ h (by rw [ba_size_push]; exact hj)
    · have hj' : j = a.size := by omega
      subst hj'
      -- the zero just pushed, which later pushes keep
      have key : ∀ (m : Nat) (b : ByteArray) (k : Nat) (hk : k < b.size) (hk' : k < (zeros m b).size),
          (zeros m b)[k] = b[k] := by
        intro m
        induction m with
        | zero => intro b k _ _; rfl
        | succ m ihm =>
          intro b k hk hk'
          simp only [zeros] at hk' ⊢
          rw [ihm _ _ (by rw [ba_size_push]; omega), ba_get_push, dite_eq_left hk]
      rw [key n (a.push 0) a.size (by rw [ba_size_push]; omega), ba_get_push, dite_eq_right (by omega)]

theorem get_blank (n : Nat) (rest : Nat → Byte) (i : Nat) :
    (blank n rest).get i = if i < min n cap then .uninit else rest i := by
  have hs : (zeros (2 * min n cap) (ByteArray.emptyWithCapacity (2 * min n cap))).size = 2 * min n cap := by
    rw [size_zeros, ba_size_empty]; omega
  by_cases h : 2 * i + 1 < (blank n rest).data.size
  · rw [get_lt _ _ h, ite_eq_left (by simp only [blank] at h; omega)]
    simp only [blank] at h ⊢
    rw [get_zeros _ _ _ _ (Nat.zero_le _)]
    rfl
  · rw [get_ge _ _ h, ite_eq_right (by simp only [blank] at h; omega)]
    rfl

theorem get_uninit (n i : Nat) : (uninit n).get i = .uninit := by
  simp only [uninit, get_blank]; split <;> rfl

theorem get_uninit_eq (n : Nat) : (uninit n).get = fun _ => .uninit := by
  funext i; exact get_uninit n i

theorem get_ofFn (n : Nat) (f : Nat → Byte) (i : Nat) : (ofFn n f).get i = f i := by
  simp only [ofFn, get_writeRange, get_blank]
  by_cases h : 0 ≤ i ∧ i < 0 + min n cap
  · rw [ite_eq_left h, Nat.sub_zero]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem get_ofFn_eq (n : Nat) (f : Nat → Byte) : (ofFn n f).get = f := by
  funext i; exact get_ofFn n f i

theorem clearFrom_spec (P : Nat → Bool) (i n : Nat) (s : ExecBytes) :
    (clearFrom P i n s).data.size = s.data.size ∧ ∀ j, (clearFrom P i n s).get j =
      if i ≤ j ∧ j < i + n ∧ P j = true then .uninit else s.get j := by
  induction n generalizing i s with
  | zero => exact ⟨rfl, fun j => by rw [ite_eq_right (by omega)]; rfl⟩
  | succ n ih =>
    simp only [clearFrom]
    obtain ⟨h1, h2⟩ := ih (i + 1) (if P i then s.set i .uninit else s)
    refine ⟨?_, fun j => ?_⟩
    · rw [h1]; split <;> simp [size_set]
    · rw [h2]
      by_cases hj : i + 1 ≤ j ∧ j < i + 1 + n ∧ P j = true
      · rw [ite_eq_left hj, ite_eq_left ⟨by omega, by omega, hj.2.2⟩]
      · rw [ite_eq_right hj]
        by_cases hp : P i = true
        · rw [ite_eq_left hp, get_set]
          by_cases e : j = i
          · subst e; rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega, hp⟩]
          · rw [ite_eq_right e]
            by_cases h3 : i ≤ j ∧ j < i + (n + 1) ∧ P j = true
            · exact absurd ⟨by omega, by omega, h3.2.2⟩ hj
            · rw [ite_eq_right h3]
        · simp only [hp, Bool.false_eq_true, ite_false]
          by_cases h3 : i ≤ j ∧ j < i + (n + 1) ∧ P j = true
          · have : j ≠ i := fun e => by subst e; exact hp h3.2.2
            exact absurd ⟨by omega, by omega, h3.2.2⟩ hj
          · rw [ite_eq_right h3]

theorem get_clearWhere (s : ExecBytes) (P : Nat → Bool) (j : Nat) :
    (s.clearWhere P).get j = if P j then .uninit else s.get j := by
  obtain ⟨h1, h2⟩ := clearFrom_spec P 0 (s.data.size / 2) s
  have h2j := h2 j
  unfold clearWhere
  revert h1 h2j
  generalize clearFrom P 0 (s.data.size / 2) s = t
  rcases t with ⟨data, ptrs, rest⟩
  intro h1 h2j
  simp only at h1
  by_cases hj : 2 * j + 1 < data.size
  · rw [get_lt _ _ hj]
    rw [get_lt _ _ hj] at h2j
    rw [h2j]
    by_cases hp : P j = true
    · rw [ite_eq_left ⟨by omega, by omega, hp⟩, ite_eq_left hp]
    · rw [ite_eq_right (by simp [hp]), ite_eq_right hp]
  · rw [get_ge _ _ hj, get_ge s j (by omega)]

end ExecBytes

/-- An allocation, as `ExecMem` holds it. -/
structure ExecAlloc where
  size : Nat
  readonly : Bool
  bytes : ExecBytes
  heap : Bool := false
  stack : Bool := false

/-- The allocation this stands for. -/
def ExecAlloc.toAlloc (a : ExecAlloc) : Alloc :=
  { size := a.size, readonly := a.readonly, bytes := a.bytes.get, heap := a.heap, stack := a.stack }

/-- Memory as tests run it. Everything but the allocations is as `Mem` has it. -/
structure ExecMem where
  /-- Allocation `b` is entry `b`, if there is one. There are none past the end. -/
  allocs : Array (Option ExecAlloc)
  next : Nat
  base : Nat → BitVec 64
  frame : List Nat
  failAlloc : Nat → Bool := fun _ => false
  calls : List Call := []
  nextCall : Nat := 1

namespace ExecMem

/-- Allocation `b`. -/
def getAlloc (x : ExecMem) (b : Nat) : Option ExecAlloc := x.allocs[b]?.join

/-- The memory this stands for. -/
def toMem (x : ExecMem) : Mem where
  allocs b := (x.getAlloc b).map ExecAlloc.toAlloc
  next := x.next
  base := x.base
  frame := x.frame
  failAlloc := x.failAlloc
  calls := x.calls
  nextCall := x.nextCall

/-- A result with its memory, read back as `Mem`'s. -/
def out (r : α × ExecMem) : α × Mem := (r.1, r.2.toMem)

instance : Inhabited ExecMem := ⟨{ allocs := #[], next := 1, base := fun _ => 0#64, frame := [] }⟩

theorem toMem_eq {x : ExecMem} {m : Mem} (ha : ∀ b, (x.getAlloc b).map ExecAlloc.toAlloc = m.allocs b)
    (hn : x.next = m.next) (hb : x.base = m.base) (hf : x.frame = m.frame) (hfa : x.failAlloc = m.failAlloc)
    (hc : x.calls = m.calls) (hnc : x.nextCall = m.nextCall) : x.toMem = m := by
  rcases m with ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩
  simp only at hn hb hf hfa hc hnc
  subst hn hb hf hfa hc hnc
  simp only [toMem, Mem.mk.injEq, and_true]
  funext b; exact ha b

/-! ### The table of allocations -/

/-- `t` with entry `b` set to `a`, grown if it has to be. -/
def setEntry (t : Array (Option ExecAlloc)) (b : Nat) (a : Option ExecAlloc) : Array (Option ExecAlloc) :=
  if b < t.size then t.set! b a else (t ++ Array.replicate (b - t.size) none).push a

theorem join_setEntry (t : Array (Option ExecAlloc)) (b : Nat) (a : Option ExecAlloc) (b' : Nat) :
    (setEntry t b a)[b']?.join = if b' = b then a else t[b']?.join := by
  unfold setEntry
  split
  · rename_i h
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : b' = b
    · subst e; simp [h]
    · rw [ite_eq_right (fun h => e h.symm), ite_eq_right e]
  · rename_i h
    rw [Array.getElem?_push]
    simp only [Array.size_append, Array.size_replicate]
    by_cases e : b' = b
    · subst e; rw [ite_eq_left (by omega), ite_eq_left rfl]; rfl
    · rw [ite_eq_right (by omega), ite_eq_right e, Array.getElem?_append]
      split
      · rfl
      · rw [Array.getElem?_replicate, Array.getElem?_eq_none (by omega)]
        split <;> rfl

theorem join_modify (t : Array (Option ExecAlloc)) (b : Nat) (g : ExecAlloc → ExecAlloc) (b' : Nat) :
    (t.modify b (Option.map g))[b']?.join = if b' = b then (t[b]?.join).map g else t[b']?.join := by
  rw [Array.getElem?_modify]
  by_cases e : b' = b
  · subst e; rw [ite_eq_left rfl, ite_eq_left rfl]
    cases t[b']? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [ite_eq_right (fun h => e h.symm), ite_eq_right e]

/-- Removes the allocations in `frame`. -/
def clearFrame (t : Array (Option ExecAlloc)) : List Nat → Array (Option ExecAlloc)
  | [] => t
  | b :: rest => clearFrame (t.set! b none) rest

theorem join_clearFrame (t : Array (Option ExecAlloc)) (frame : List Nat) (b : Nat) :
    (clearFrame t frame)[b]?.join = if frame.contains b then none else t[b]?.join := by
  induction frame generalizing t with
  | nil => rfl
  | cons b' rest ih =>
    rw [clearFrame, ih]
    have hs : (t.set! b' none)[b]?.join = if b = b' then none else t[b]?.join := by
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases e : b' = b
      · subst e; rw [ite_eq_left rfl, ite_eq_left rfl]; split <;> rfl
      · rw [ite_eq_right e, ite_eq_right (fun h => e h.symm)]
    rw [hs]
    by_cases e : b = b' <;> simp [e]

/-! ### Making memory -/

/-- Memory with nothing allocated. -/
def empty (base : Nat → BitVec 64) : ExecMem := { allocs := #[], next := 1, base := base, frame := [] }

theorem toMem_empty (base : Nat → BitVec 64) : (empty base).toMem = Mem.empty base :=
  toMem_eq (fun _ => by simp [getAlloc, empty, Mem.empty]) rfl rfl rfl rfl rfl rfl

/-- `Mem.spacedOut`. -/
@[inline] def spacedOut (block : Nat) : BitVec 64 := Mem.spacedOut block

def setAlloc (x : ExecMem) (b : Nat) (a : Option ExecAlloc) : ExecMem :=
  match x with
  | ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩ =>
    ⟨setEntry allocs b a, next, base, frame, failAlloc, calls, nextCall⟩

theorem getAlloc_setAlloc (x : ExecMem) (b : Nat) (a : Option ExecAlloc) (b' : Nat) :
    (x.setAlloc b a).getAlloc b' = if b' = b then a else x.getAlloc b' := by
  rcases x with ⟨⟩; exact join_setEntry ..

theorem toMem_setAlloc (x : ExecMem) (b : Nat) (a : Option ExecAlloc) :
    (x.setAlloc b a).toMem = x.toMem.setAlloc b (a.map ExecAlloc.toAlloc) := by
  rcases x with ⟨⟩
  refine toMem_eq (fun b' => ?_) rfl rfl rfl rfl rfl rfl
  rw [getAlloc_setAlloc]
  simp only [Mem.setAlloc, toMem, beq_iff_eq]
  split <;> rfl

/-- `Mem.addGlobal`. -/
def addGlobal (x : ExecMem) (block size : Nat) (readonly : Bool) (init : Array Nat) : ExecMem :=
  let next := max x.next (block + 1)
  match x.setAlloc block (some { size := size, readonly := readonly, bytes := ExecBytes.ofFn size (Mem.globalBytes init) }) with
  | ⟨allocs, _, base, frame, failAlloc, calls, nextCall⟩ => ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩

theorem toMem_addGlobal (x : ExecMem) (block size : Nat) (readonly : Bool) (init : Array Nat) :
    (x.addGlobal block size readonly init).toMem = x.toMem.addGlobal block size readonly init := by
  rcases x with ⟨⟩
  refine toMem_eq (fun b' => ?_) rfl rfl rfl rfl rfl rfl
  simp only [addGlobal, setAlloc, getAlloc, join_setEntry, Mem.addGlobal, toMem, beq_iff_eq]
  split
  · simp [ExecAlloc.toAlloc, ExecBytes.get_ofFn_eq]
  · rfl

/-- `Mem.addReloc`. -/
def addReloc (x : ExecMem) (block offset : Nat) (target : Ptr) : ExecMem :=
  match x.getAlloc block with
  | none => x
  | some a => x.setAlloc block (some { a with bytes := a.bytes.writeRange offset 8 fun i => .ptr target i })

theorem toMem_addReloc (x : ExecMem) (block offset : Nat) (target : Ptr) :
    (x.addReloc block offset target).toMem = x.toMem.addReloc block offset target := by
  unfold addReloc Mem.addReloc
  have hm : x.toMem.allocs block = (x.getAlloc block).map ExecAlloc.toAlloc := rfl
  rw [hm]
  cases h : x.getAlloc block with
  | none => rfl
  | some a =>
    simp only [toMem_setAlloc, Option.map_some]
    simp only [toMem]
    simp only [ExecAlloc.toAlloc, ExecBytes.get_writeRange_eq]

/-- `Mem.reserve`. -/
def reserve (x : ExecMem) (next : Nat) : ExecMem := { x with next := max x.next next }

theorem toMem_reserve (x : ExecMem) (next : Nat) : (x.reserve next).toMem = x.toMem.reserve next := rfl

/-! ### Writing -/

/-- What `Mem.write` records of a write, in each running call that tracks them. -/
def noteWrite (calls : List Call) (q : Ptr) (n : Nat) : List Call :=
  if calls.any (·.tracked) then
    let o := q.offset.toNat
    calls.map fun c =>
      if c.tracked then
        let here := fun b i => b == q.block && decide (o ≤ i) && decide (i < o + n)
        { c with
          written := fun b i => here b i || c.written b i
          initialized := fun b i =>
            (q.tags.any (fun t => t.call == c.id && t.initializes) && here b i) || c.initialized b i }
      else c
  else calls

theorem noteWrite_eq (x : ExecMem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) :
    noteWrite x.calls q n = (x.toMem.write q a n f).calls := by
  simp only [noteWrite, Mem.write, toMem]
  split
  · rfl
  · rename_i h
    simp only [Bool.not_eq_true, List.any_eq_false] at h
    conv => lhs; rw [← List.map_id x.calls]
    refine List.map_congr_left fun c hc => ?_
    have := h c hc
    simp [this]

/-- `Mem.write`: overwrites `n` bytes from `q`, `f` giving each byte from its position in the write. -/
def write (x : ExecMem) (q : Ptr) (n : Nat) (f : Nat → Byte) : ExecMem :=
  let calls := noteWrite x.calls q n
  match x with
  | ⟨allocs, next, base, frame, failAlloc, _, nextCall⟩ =>
    ⟨allocs.modify q.block (Option.map fun a => { a with bytes := a.bytes.writeRange q.offset.toNat n f }),
      next, base, frame, failAlloc, calls, nextCall⟩

theorem toMem_write (x : ExecMem) (q : Ptr) (n : Nat) (f : Nat → Byte) (a : ExecAlloc)
    (h : x.getAlloc q.block = some a) : (x.write q n f).toMem = x.toMem.write q a.toAlloc n f := by
  have hc := noteWrite_eq x q a.toAlloc n f
  rcases x with ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩
  refine toMem_eq (fun b => ?_) rfl rfl rfl rfl hc rfl
  simp only [write, getAlloc, join_modify, Mem.write, Mem.setAlloc, toMem, beq_iff_eq]
  simp only [getAlloc] at h
  split
  · rw [h]; simp [ExecAlloc.toAlloc, ExecBytes.get_writeRange_eq]
  · rfl

/-- A write is the same whatever `f` gives past the bytes it writes. -/
theorem _root_.IRLean.Mem.write_congr (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) {f g : Nat → Byte}
    (h : ∀ i, i < n → f i = g i) : m.write q a n f = m.write q a n g := by
  have e : (fun i => if q.offset.toNat ≤ i ∧ i < q.offset.toNat + n then f (i - q.offset.toNat) else a.bytes i) =
      (fun i => if q.offset.toNat ≤ i ∧ i < q.offset.toNat + n then g (i - q.offset.toNat) else a.bytes i) := by
    funext i
    split
    · exact h _ (by omega)
    · rfl
  simp only [Mem.write, e]

/-- What a valid access found. -/
theorem access_ok {x : ExecMem} {p : PtrVal} {n align : Nat} {q : Ptr} {a : Alloc}
    (h : x.toMem.access p n align = .ok (q, a)) : ∃ e, x.getAlloc q.block = some e ∧ e.toAlloc = a := by
  have h2 := (Mem.access_ok_iff.mp h).2.1
  simp only [toMem] at h2
  cases hg : x.getAlloc q.block with
  | none => simp [hg] at h2
  | some e => simp only [hg, Option.map_some, Option.some.injEq] at h2; exact ⟨e, rfl, h2⟩

/-! ### Operations that only read

Each is `Mem`'s, on `x.toMem`, so it agrees with `Mem` by definition. Reading `x.toMem` reads `x`'s arrays. -/

@[inline] def addr (x : ExecMem) (p : Ptr) : BitVec 64 := Mem.addr x.toMem p
@[inline] def toVal (x : ExecMem) : PtrVal → Val 64 := Mem.toVal x.toMem
@[inline] def loadInt (w : Nat) (x : ExecMem) (p : PtrVal) (align : Nat) : Outcome (Val w) :=
  Mem.loadInt w x.toMem p align
@[inline] def loadPtr (x : ExecMem) (p : PtrVal) (align : Nat) : Outcome PtrVal := Mem.loadPtr x.toMem p align
@[inline] def loadVec (n w : Nat) (x : ExecMem) (p : PtrVal) (align : Nat) : Outcome (Vec n w) :=
  Mem.loadVec n w x.toMem p align
@[inline] def gep (x : ExecMem) (p : PtrVal) (off : Val 64) (inbounds nusw nuw : Bool := false) : PtrVal :=
  Mem.gep x.toMem p off inbounds nusw nuw
@[inline] def gepSteps (x : ExecMem) (p : PtrVal) (offsets : List (Val 64)) (inbounds nusw nuw : Bool := false) :
    PtrVal :=
  Mem.gepSteps x.toMem p offsets inbounds nusw nuw
@[inline] def nonnull (x : ExecMem) (p : PtrVal) : PtrVal := Mem.nonnull x.toMem p
@[inline] def aligned (x : ExecMem) (align : Nat) (p : PtrVal) : PtrVal := Mem.aligned x.toMem align p
@[inline] def dereferenceable (x : ExecMem) (p : PtrVal) (n : Nat) (k : Outcome α) : Outcome α :=
  Mem.dereferenceable x.toMem p n k
@[inline] def assumeNonnull (x : ExecMem) (p : PtrVal) (k : Outcome α) : Outcome α := Mem.assumeNonnull x.toMem p k
@[inline] def noaliasResult (x : ExecMem) (p : PtrVal) (k : Outcome α) : Outcome α := Mem.noaliasResult x.toMem p k

/-! `Mem`'s operations on pointers that don't read memory, under the names the emitter gives them. -/

@[inline] def observeAddress (p : PtrVal) (nullCheck : Bool) (k : Outcome α) : Outcome α :=
  Mem.observeAddress p nullCheck k
@[inline] def tag (t : Tag) (p : PtrVal) : PtrVal := Mem.tag t p
@[inline] def returnedArgument (arg result : PtrVal) (k : Outcome α) : Outcome α := Mem.returnedArgument arg result k
@[inline] def returnedInt (arg result : Val w) (k : Outcome α) : Outcome α := Mem.returnedInt arg result k

/-- C's `strlen`, which changes nothing. -/
def strlen (p : PtrVal) (x : ExecMem) : Outcome (Val 64 × ExecMem) :=
  andThen (Mem.strlen p x.toMem) fun r => Outcome.ok (r.1, x)

theorem strlen_agrees (p : PtrVal) (x : ExecMem) : Mem.strlen p x.toMem = Outcome.map out (strlen p x) := by
  simp only [strlen, Outcome.map_andThen, Outcome.map_ok, out]
  unfold Mem.strlen
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-! ### Operations that write -/

/-- `Mem.storeInt`. -/
def storeInt (x : ExecMem) (p : PtrVal) (v : Val w) (align : Nat) : Outcome ExecMem :=
  match x.toMem.access p (w / 8) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    match x.toMem.check q a true with
    | some e => some (.error e)
    | none =>
      Outcome.ok <| x.write q (w / 8) fun i =>
        match v with
        | none => .poison
        | some x => Mem.intByte x i

theorem storeInt_agrees (x : ExecMem) (p : PtrVal) (v : Val w) (align : Nat) :
    Mem.storeInt x.toMem p v align = Outcome.map toMem (x.storeInt p v align) := by
  simp only [Mem.storeInt, storeInt]
  cases hacc : x.toMem.access p (w / 8) align with
  | error e => rfl
  | ok r =>
    obtain ⟨q, a⟩ := r
    obtain ⟨e, he, rfl⟩ := access_ok hacc
    simp only
    by_cases hr : e.toAlloc.readonly = true
    · simp only [hr, ite_true]; rfl
    · simp only [hr, Bool.false_eq_true, ite_false]
      cases hc : x.toMem.check q e.toAlloc true with
      | some _ => rfl
      | none =>
        rw [Outcome.map_ok, toMem_write _ _ _ _ _ he]
        exact congrArg Outcome.ok (Mem.write_congr _ _ _ _ fun _ _ => rfl)

/-- `Mem.storePtr`. -/
def storePtr (x : ExecMem) (p : PtrVal) (v : PtrVal) (align : Nat) : Outcome ExecMem :=
  match x.toMem.access p 8 align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    match x.toMem.check q a true with
    | some e => some (.error e)
    | none =>
      Outcome.ok <| x.write q 8 fun i =>
        match v with
        | none => .poison
        | some x => .ptr x i

theorem storePtr_agrees (x : ExecMem) (p : PtrVal) (v : PtrVal) (align : Nat) :
    Mem.storePtr x.toMem p v align = Outcome.map toMem (x.storePtr p v align) := by
  simp only [Mem.storePtr, storePtr]
  cases hacc : x.toMem.access p 8 align with
  | error e => rfl
  | ok r =>
    obtain ⟨q, a⟩ := r
    obtain ⟨e, he, rfl⟩ := access_ok hacc
    simp only
    by_cases hr : e.toAlloc.readonly = true
    · simp only [hr, ite_true]; rfl
    · simp only [hr, Bool.false_eq_true, ite_false]
      cases hc : x.toMem.check q e.toAlloc true with
      | some _ => rfl
      | none =>
        rw [Outcome.map_ok, toMem_write _ _ _ _ _ he]
        exact congrArg Outcome.ok (Mem.write_congr _ _ _ _ fun _ _ => rfl)

/-- `Mem.storeVec`. -/
def storeVec (x : ExecMem) (p : PtrVal) (v : Vec n w) (align : Nat) : Outcome ExecMem :=
  match x.toMem.access p (n * (w / 8)) align with
  | .error e => Outcome.ub e
  | .ok (q, a) =>
    if a.readonly then Outcome.ub .writeToConstant else
    match x.toMem.check q a true with
    | some e => some (.error e)
    | none =>
      Outcome.ok <| x.write q (n * (w / 8)) fun i =>
        match Vec.lane v (i / (w / 8)) with
        | none => .poison
        | some x => Mem.intByte x (i % (w / 8))

theorem storeVec_agrees (x : ExecMem) (p : PtrVal) (v : Vec n w) (align : Nat) :
    Mem.storeVec x.toMem p v align = Outcome.map toMem (x.storeVec p v align) := by
  simp only [Mem.storeVec, storeVec]
  cases hacc : x.toMem.access p (n * (w / 8)) align with
  | error e => rfl
  | ok r =>
    obtain ⟨q, a⟩ := r
    obtain ⟨e, he, rfl⟩ := access_ok hacc
    simp only
    by_cases hr : e.toAlloc.readonly = true
    · simp only [hr, ite_true]; rfl
    · simp only [hr, Bool.false_eq_true, ite_false]
      cases hc : x.toMem.check q e.toAlloc true with
      | some _ => rfl
      | none =>
        rw [Outcome.map_ok, toMem_write _ _ _ _ _ he]
        exact congrArg Outcome.ok (Mem.write_congr _ _ _ _ fun _ _ => rfl)

/-- `llvm.memset`. -/
def memset (x : ExecMem) (p : PtrVal) (v : Val 8) (n : Val 64) : Outcome ExecMem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok x else
    match x.toMem.access p k.toNat 1 with
    | .error e => Outcome.ub e
    | .ok (q, a) =>
      if a.readonly then Outcome.ub .writeToConstant else
      match x.toMem.check q a true with
      | some e => some (.error e)
      | none =>
        Outcome.ok <| x.write q k.toNat fun _ =>
          match v with
          | none => .poison
          | some x => .val x

theorem memset_agrees (x : ExecMem) (p : PtrVal) (v : Val 8) (n : Val 64) :
    Mem.memset x.toMem p v n = Outcome.map toMem (x.memset p v n) := by
  simp only [Mem.memset, memset]
  cases n with
  | none => rfl
  | some k =>
    simp only
    split
    · rfl
    · cases hacc : x.toMem.access p k.toNat 1 with
      | error e => rfl
      | ok r =>
        obtain ⟨q, a⟩ := r
        obtain ⟨e, he, rfl⟩ := access_ok hacc
        simp only
        by_cases hr : e.toAlloc.readonly = true
        · simp only [hr, ite_true]; rfl
        · simp only [hr, Bool.false_eq_true, ite_false]
          cases hc : x.toMem.check q e.toAlloc true with
          | some _ => rfl
          | none =>
            rw [Outcome.map_ok, toMem_write _ _ _ _ _ he]
            exact congrArg Outcome.ok (Mem.write_congr _ _ _ _ fun _ _ => rfl)

/-- `llvm.memcpy`. The bytes are read before any is written, so the source isn't held while they are. -/
def memcpy (x : ExecMem) (dst src : PtrVal) (n : Val 64) : Outcome ExecMem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok x else
    match x.toMem.access dst k.toNat 1, x.toMem.access src k.toNat 1 with
    | .error e, _ => Outcome.ub e
    | _, .error e => Outcome.ub e
    | .ok (d, da), .ok (s, sa) =>
      if da.readonly then Outcome.ub .writeToConstant else
      let dOff := d.offset.toNat
      let sOff := s.offset.toNat
      if d.block == s.block && dOff != sOff && dOff < sOff + k.toNat && sOff < dOff + k.toNat then
        Outcome.ub .overlappingCopy
      else
        match x.toMem.check s sa false, x.toMem.check d da true with
        | some e, _ => some (.error e)
        | _, some e => some (.error e)
        | none, none =>
          let bytes := Array.ofFn (n := k.toNat) fun i => x.toMem.visible s sa (sOff + i)
          Outcome.ok <| x.write d k.toNat fun i => bytes[i]?.getD .uninit

theorem memcpy_agrees (x : ExecMem) (dst src : PtrVal) (n : Val 64) :
    Mem.memcpy x.toMem dst src n = Outcome.map toMem (x.memcpy dst src n) := by
  simp only [Mem.memcpy, memcpy]
  cases n with
  | none => rfl
  | some k =>
    simp only
    split
    · rfl
    · cases hd : x.toMem.access dst k.toNat 1 with
      | error e => rfl
      | ok r =>
        cases hs : x.toMem.access src k.toNat 1 with
        | error e => rfl
        | ok r' =>
          obtain ⟨d, da⟩ := r
          obtain ⟨s, sa⟩ := r'
          obtain ⟨e, he, rfl⟩ := access_ok hd
          simp only
          by_cases hr : e.toAlloc.readonly = true
          · simp only [hr, ite_true]; rfl
          · simp only [hr, Bool.false_eq_true, ite_false]
            split
            · rfl
            · cases hc1 : x.toMem.check s sa false with
              | some _ => rfl
              | none =>
                cases hc2 : x.toMem.check d e.toAlloc true with
                | some _ => rfl
                | none =>
                  simp only [Outcome.map_ok, toMem_write _ _ _ _ _ he]
                  congr 1
                  refine Mem.write_congr _ _ _ _ fun i hi => ?_
                  simp [hi]

/-- `llvm.memmove`, as `memcpy` with the ranges allowed to overlap: every byte is read before any is written. -/
def memmove (x : ExecMem) (dst src : PtrVal) (n : Val 64) : Outcome ExecMem :=
  match n with
  | none => Outcome.ub .poisonPointer
  | some k =>
    if k == 0#64 then Outcome.ok x else
    match x.toMem.access dst k.toNat 1, x.toMem.access src k.toNat 1 with
    | .error e, _ => Outcome.ub e
    | _, .error e => Outcome.ub e
    | .ok (d, da), .ok (s, sa) =>
      if da.readonly then Outcome.ub .writeToConstant else
      match x.toMem.check s sa false, x.toMem.check d da true with
      | some e, _ => some (.error e)
      | _, some e => some (.error e)
      | none, none =>
        let bytes := Array.ofFn (n := k.toNat) fun j => x.toMem.visible s sa (s.offset.toNat + j)
        Outcome.ok <| x.write d k.toNat fun i => bytes[i]?.getD .uninit

theorem memmove_agrees (x : ExecMem) (dst src : PtrVal) (n : Val 64) :
    Mem.memmove x.toMem dst src n = Outcome.map toMem (x.memmove dst src n) := by
  simp only [Mem.memmove, memmove]
  cases n with
  | none => rfl
  | some k =>
    simp only
    split
    · rfl
    · cases hd : x.toMem.access dst k.toNat 1 with
      | error e => rfl
      | ok r =>
        cases hs : x.toMem.access src k.toNat 1 with
        | error e => rfl
        | ok r' =>
          obtain ⟨d, da⟩ := r
          obtain ⟨s, sa⟩ := r'
          obtain ⟨e, he, rfl⟩ := access_ok hd
          simp only
          by_cases hr : e.toAlloc.readonly = true
          · simp only [hr, ite_true]; rfl
          · simp only [hr, Bool.false_eq_true, ite_false]
            cases hc1 : x.toMem.check s sa false with
            | some _ => rfl
            | none =>
              cases hc2 : x.toMem.check d e.toAlloc true with
              | some _ => rfl
              | none =>
                simp only [Outcome.map_ok, toMem_write _ _ _ _ _ he]
                congr 1
                refine Mem.write_congr _ _ _ _ fun i hi => ?_
                simp [hi]

/-- `alloca`. -/
def alloca (x : ExecMem) (size : Val 64) (dead : Bool := false) : Outcome (PtrVal × ExecMem) :=
  match size with
  | none => Outcome.ub .poisonPointer
  | some n =>
    let block := x.next
    Outcome.ok (some ⟨block, 0#64, []⟩,
      match x with
      | ⟨allocs, _, base, frame, failAlloc, calls, nextCall⟩ =>
        ⟨setEntry allocs block
            (some { size := n.toNat, readonly := dead, bytes := ExecBytes.uninit n.toNat, stack := true }),
          block + 1, base, block :: frame, failAlloc, calls, nextCall⟩)

theorem alloca_agrees (x : ExecMem) (size : Val 64) (dead : Bool) :
    Mem.alloca x.toMem size dead = Outcome.map out (x.alloca size dead) := by
  cases size with
  | none => rfl
  | some n =>
    simp only [Mem.alloca, alloca, Outcome.map_ok, out]
    congr 2
    rcases x with ⟨⟩
    refine (toMem_eq (fun b => ?_) rfl rfl rfl rfl rfl rfl).symm
    simp only [getAlloc, join_setEntry, toMem, beq_iff_eq]
    split
    · simp [ExecAlloc.toAlloc, ExecBytes.get_uninit_eq]
    · rfl

/-- C's `malloc`, which can fail. -/
def malloc (size : Val 64) (x : ExecMem) : Outcome (PtrVal × ExecMem) :=
  match size with
  | none => Outcome.ub .noundefPoison
  | some n =>
    let block := x.next
    match x.toMem.allocatorRule (x.failAlloc block) with
    | some e => some (.error e)
    | none =>
      if x.failAlloc block then Outcome.ok (some Ptr.null, { x with next := block + 1 }) else
      Outcome.ok (some ⟨block, 0#64, []⟩,
        match x with
        | ⟨allocs, _, base, frame, failAlloc, calls, nextCall⟩ =>
          ⟨setEntry allocs block
              (some { size := n.toNat, readonly := false, bytes := ExecBytes.uninit n.toNat, heap := true }),
            block + 1, base, frame, failAlloc, calls, nextCall⟩)

theorem malloc_agrees (size : Val 64) (x : ExecMem) :
    Mem.malloc size x.toMem = Outcome.map out (malloc size x) := by
  cases size with
  | none => rfl
  | some n =>
    have e1 : x.toMem.failAlloc = x.failAlloc := rfl
    have e2 : x.toMem.next = x.next := rfl
    simp only [Mem.malloc, malloc, e1, e2]
    cases hr : x.toMem.allocatorRule (x.failAlloc x.next) with
    | some _ => rfl
    | none =>
      simp only
      by_cases hf : x.failAlloc x.next = true
      · simp only [hf, ite_true]; rfl
      · simp only [hf, Bool.false_eq_true, ite_false, Outcome.map_ok, out]
        congr 2
        rcases x with ⟨⟩
        refine Eq.symm (toMem_eq (fun b => ?_) ?_ ?_ ?_ ?_ ?_ ?_)
        · simp only [getAlloc, join_setEntry, toMem, beq_iff_eq]
          split
          · simp [ExecAlloc.toAlloc, ExecBytes.get_uninit_eq]
          · rfl
        all_goals rfl

/-- C's `free`, which does nothing to null. -/
def free (p : PtrVal) (x : ExecMem) : Outcome (Unit × ExecMem) :=
  match p with
  | none => Outcome.ub .noundefPoison
  | some q =>
    if q.same Ptr.null then Outcome.ok ((), x) else
    match x.toMem.allocs q.block with
    | some a =>
      if a.heap && q.offset == 0#64 then
        if q.tags.any (fun t => t.nofree && x.toMem.isRunning t.call) then Outcome.ub .forbiddenFree else
        match x.toMem.check q a true, x.toMem.allocatorRule false with
        | some e, _ => some (.error e)
        | _, some e => some (.error e)
        | none, none => Outcome.ok ((), x.setAlloc q.block none)
      else Outcome.ub .badFree
    | none => Outcome.ub .badFree

theorem free_agrees (p : PtrVal) (x : ExecMem) : Mem.free p x.toMem = Outcome.map out (free p x) := by
  cases p with
  | none => rfl
  | some q =>
    simp only [Mem.free, free]
    split
    · rfl
    · cases ha : x.toMem.allocs q.block with
      | none => rfl
      | some a =>
        simp only
        split
        · split
          · rfl
          · cases hc1 : x.toMem.check q a true with
            | some _ => rfl
            | none =>
              cases hc2 : x.toMem.allocatorRule false with
              | some _ => rfl
              | none => simp only [Outcome.map_ok, out, toMem_setAlloc, Option.map_none]
        · rfl

/-- `llvm.lifetime.start` and `.end`. -/
def lifetime (x : ExecMem) (p : PtrVal) (alive : Bool) : Outcome ExecMem :=
  match p with
  | none => Outcome.ok x
  | some q =>
    match x.getAlloc q.block with
    | none => Outcome.ok x
    | some a =>
      Outcome.ok (x.setAlloc q.block (some { a with readonly := !alive, bytes := ExecBytes.uninit a.size }))

theorem lifetime_agrees (x : ExecMem) (p : PtrVal) (alive : Bool) :
    Mem.lifetime x.toMem p alive = Outcome.map toMem (x.lifetime p alive) := by
  cases p with
  | none => rfl
  | some q =>
    simp only [Mem.lifetime, lifetime]
    have hm : x.toMem.allocs q.block = (x.getAlloc q.block).map ExecAlloc.toAlloc := rfl
    rw [hm]
    cases x.getAlloc q.block with
    | none => rfl
    | some a =>
      simp only [Option.map_some, Outcome.map_ok, toMem_setAlloc]
      simp [ExecAlloc.toAlloc, ExecBytes.get_uninit_eq]

/-- The `initializes` attribute, which only changes the running call. -/
def addInitializes (x : ExecMem) (p : PtrVal) (lo hi : BitVec 64) : ExecMem :=
  { x with calls := (x.toMem.addInitializes p lo hi).calls }

theorem toMem_addInitializes (x : ExecMem) (p : PtrVal) (lo hi : BitVec 64) :
    (x.addInitializes p lo hi).toMem = x.toMem.addInitializes p lo hi := by
  simp only [addInitializes, Mem.addInitializes]
  split <;> rfl

/-! ### Frames and calls -/

/-- Runs a body that uses `alloca`, then removes what it allocated. -/
def withFrame (x : ExecMem) (body : ExecMem → Outcome (α × ExecMem)) : Outcome (α × ExecMem) :=
  let saved := x.frame
  andThen (body { x with frame := [] }) fun r =>
    Outcome.ok (r.1,
      match r.2 with
      | ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩ =>
        ⟨clearFrame allocs frame, next, base, saved, failAlloc, calls, nextCall⟩)

theorem withFrame_agrees (x : ExecMem) (body : Mem → Outcome (α × Mem)) (body' : ExecMem → Outcome (α × ExecMem))
    (h : ∀ y, body y.toMem = Outcome.map out (body' y)) :
    Mem.withFrame x.toMem body = Outcome.map out (x.withFrame body') := by
  simp only [Mem.withFrame, withFrame, Outcome.map_andThen]
  have e : ({ x.toMem with frame := [] } : Mem) = ({ x with frame := [] } : ExecMem).toMem := rfl
  rw [e, h, Outcome.andThen_map]
  congr 1
  funext r
  rcases r with ⟨r, ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩⟩
  simp only [out, Outcome.map_ok]
  refine congrArg _ (congrArg _ (toMem_eq (fun b => ?_) rfl rfl rfl rfl rfl rfl).symm)
  simp only [getAlloc, join_clearFrame, toMem]
  by_cases hc : b ∈ frame <;> simp [hc]

/-- What `Mem.call` does to allocation `b` when the call `c` returns: the bytes `initializes` covers that nothing
wrote through the argument go back to uninitialized. -/
def cleared (c : Call) (b : Nat) (i : Nat) : Bool :=
  c.ranges.any (fun (b', s, n) => b == b' && decide (s ≤ i) && decide (i < s + n)) && !c.initialized b i

/-- Clears the bytes `cleared` names, in each allocation of `blocks`. -/
def clearRanges (c : Call) (t : Array (Option ExecAlloc)) : List Nat → Array (Option ExecAlloc)
  | [] => t
  | b :: rest => clearRanges c (t.modify b (Option.map fun a => { a with bytes := a.bytes.clearWhere (cleared c b) })) rest

/-- An allocation with the bytes `cleared` names uninitialized, as `Mem.call` leaves it. -/
def clearAlloc (c : Call) (b : Nat) (a : Alloc) : Alloc :=
  { a with bytes := fun i => if cleared c b i then .uninit else a.bytes i }

theorem clearAlloc_twice (c : Call) (b : Nat) (a : Alloc) : clearAlloc c b (clearAlloc c b a) = clearAlloc c b a := by
  simp only [clearAlloc]
  congr 1
  funext i
  split <;> rfl

theorem toAlloc_clear (c : Call) (b : Nat) (a : ExecAlloc) :
    ({ a with bytes := a.bytes.clearWhere (cleared c b) } : ExecAlloc).toAlloc = clearAlloc c b a.toAlloc := by
  simp only [ExecAlloc.toAlloc, clearAlloc]
  congr 1
  funext i
  exact ExecBytes.get_clearWhere _ _ _

theorem map_clearRanges (c : Call) (t : Array (Option ExecAlloc)) (blocks : List Nat) (b : Nat) :
    ((clearRanges c t blocks)[b]?.join).map ExecAlloc.toAlloc =
      if blocks.contains b then ((t[b]?.join).map ExecAlloc.toAlloc).map (clearAlloc c b)
      else (t[b]?.join).map ExecAlloc.toAlloc := by
  induction blocks generalizing t with
  | nil => rfl
  | cons b' rest ih =>
    simp only [clearRanges, ih, join_modify, List.contains_cons]
    by_cases e : b = b'
    · subst e
      simp only [beq_self_eq_true, Bool.true_or, ite_true]
      split
      · cases t[b]?.join <;> simp [toAlloc_clear, clearAlloc_twice]
      · cases t[b]?.join <;> simp [toAlloc_clear]
    · simp only [show (b == b') = false from by simpa using e, Bool.false_or, ite_eq_right e]

theorem contains_map_fst (l : List (Nat × Nat × Nat)) (b : Nat) :
    (l.map (·.1)).contains b = l.any (fun (b', _, _) => b == b') := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, List.contains_cons, List.any_cons, ih]

/-- Runs a function that made promises about memory. -/
def call (x : ExecMem) (e : Effects) (tracked : Bool) (k : ExecMem → Nat → Outcome (α × ExecMem)) :
    Outcome (α × ExecMem) :=
  let id := x.nextCall
  andThen (k { x with
      calls := { id, effects := e, start := x.next, tracked } :: x.calls
      nextCall := id + 1 } id) fun r =>
    match r.2 with
    | ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩ =>
      match calls with
      | [] => Outcome.ok (r.1, ⟨allocs, next, base, frame, failAlloc, [], nextCall⟩)
      | c :: rest =>
        Outcome.ok (r.1,
          ⟨if c.ranges.isEmpty then allocs else clearRanges c allocs (c.ranges.map (·.1)),
            next, base, frame, failAlloc, rest, nextCall⟩)

/-- What `Mem.call` does when the call returns. -/
def callEnd : α × Mem → Outcome (α × Mem) := fun (r, m') =>
  match m'.calls with
  | [] => Outcome.ok (r, m')
  | c :: rest =>
    let cleared := fun b i =>
      if c.ranges.any (fun (b', s, n) => b == b' && decide (s ≤ i) && decide (i < s + n)) && !c.initialized b i
      then Byte.uninit
      else match m'.allocs b with
        | some a => a.bytes i
        | none => .uninit
    Outcome.ok (r, { m' with
      calls := rest
      allocs := fun b =>
        match c.ranges.any (fun (b', _, _) => b == b'), m'.allocs b with
        | true, some a => some { a with bytes := cleared b }
        | _, x => x })

theorem call_eq (x : ExecMem) (e : Effects) (tracked : Bool) (k : Mem → Nat → Outcome (α × Mem)) :
    Mem.call x.toMem e tracked k =
      andThen (k ({ x with
          calls := { id := x.nextCall, effects := e, start := x.next, tracked } :: x.calls
          nextCall := x.nextCall + 1 } : ExecMem).toMem x.nextCall) callEnd := rfl

theorem call_agrees (x : ExecMem) (e : Effects) (tracked : Bool) (k : Mem → Nat → Outcome (α × Mem))
    (k' : ExecMem → Nat → Outcome (α × ExecMem)) (h : ∀ y c, k y.toMem c = Outcome.map out (k' y c)) :
    Mem.call x.toMem e tracked k = Outcome.map out (x.call e tracked k') := by
  rw [call_eq, h, Outcome.andThen_map]
  simp only [call, Outcome.map_andThen]
  congr 1
  funext r
  rcases r with ⟨r, ⟨allocs, next, base, frame, failAlloc, calls, nextCall⟩⟩
  cases calls with
  | nil => rfl
  | cons c rest =>
    show Outcome.ok _ = Outcome.ok _
    congr 2
    refine Eq.symm (toMem_eq (fun b => ?_) ?_ ?_ ?_ ?_ ?_ ?_)
    · simp only [getAlloc, toMem]
      by_cases hE : c.ranges.isEmpty = true
      · rw [ite_eq_left hE]
        have : c.ranges.any (fun (b', _, _) => b == b') = false := by
          rw [List.isEmpty_iff] at hE; simp [hE]
        rw [this]
      · rw [ite_eq_right hE, map_clearRanges, contains_map_fst]
        cases hb : c.ranges.any (fun (b', _, _) => b == b') with
        | false => rfl
        | true =>
          simp only [ite_true]
          cases allocs[b]?.join with
          | none => rfl
          | some a => rfl
    all_goals rfl

end ExecMem

/-! ### Whole runs

The emitter's copy of a function on `ExecMem` runs the same blocks as the original, with each block's memory read back
by `toMem`. These take agreement from blocks to whole runs, once for every function, for each way the emitter runs
blocks: `run`, and `promised` with `runPromised` under a promise to progress. What a function on `ExecMem` would still
need, to be proved to agree with the original as a whole, is the equation for each of its blocks, `h` below. -/

/-- What a block does last, with the next block and the result each read back. -/
def Next.map (g : β' → β) (k : ρ' → ρ) : Next β' ρ' → Next β ρ
  | .jump b => .jump (g b)
  | .ret r => .ret (k r)

/-! What a block ends with, read back. With `storeInt_agrees` and the rest, `Outcome.andThen_map` and
`Outcome.map_andThen`, these take a block's equation apart by `simp`: `tests/exec_memory/Link.lean` does it. -/

theorem map_jump (g : β' → β) (k : ρ' → ρ) (b : β') :
    Outcome.map (Next.map g k) (jump b : Outcome (Next β' ρ')) = jump (g b) := rfl

theorem map_ret (g : β' → β) (k : ρ' → ρ) (r : ρ') :
    Outcome.map (Next.map g k) (ret r : Outcome (Next β' ρ')) = ret (k r) := rfl

theorem map_br (g : β' → β) (k : ρ' → ρ) (c : Val 1) (t e : β') :
    Outcome.map (Next.map g k) (br c t e : Outcome (Next β' ρ')) = br c (g t) (g e) := by
  rcases c with _ | b
  · rfl
  · simp only [br, jump, Outcome.ok, Outcome.map, Next.map]; split <;> rfl

theorem map_assume (f : α → β) (c : Val 1) (o : Outcome α) :
    Outcome.map f (assume c o) = assume c (Outcome.map f o) := by
  rcases c with _ | b
  · rfl
  · simp only [assume]; split <;> rfl

theorem map_noundef {τ : Type} (f : α → β) (x : Option τ) (o : Outcome α) :
    Outcome.map f (noundef x o) = noundef x (Outcome.map f o) := by
  rcases x with _ | _ <;> rfl

section Runs

variable {β β' ρ ρ' : Type} {g : β' → β} {k : ρ' → ρ} {step : β → Outcome (Next β ρ)}
  {step' : β' → Outcome (Next β' ρ')}

theorem runFuel_map (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (n : Nat) (b : β') :
    runFuel step n (g b) = (runFuel step' n b).map (Outcome.map k) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [runFuel, h]
    rcases step' b with _ | e | (n' | r)
    · rfl
    · rfl
    · exact ih n'
    · rfl

/-- Two runs of blocks that agree, block by block, agree. -/
theorem run_map (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (b : β') :
    run step (g b) = Outcome.map k (run step' b) := by
  cases hr : run step' b with
  | some x =>
    obtain ⟨n, hn⟩ := runFuel_of_run hr
    have e := runFuel_map h n b
    rw [hn] at e
    exact run_of_runFuel e
  | none =>
    cases hr' : run step (g b) with
    | none => rfl
    | some y =>
      obtain ⟨n, hn⟩ := runFuel_of_run hr'
      have e := runFuel_map h n b
      rw [hn] at e
      cases hf : runFuel step' n b with
      | none => rw [hf] at e; cases e
      | some o =>
        rw [run_of_runFuel hf] at hr
        subst hr
        rw [hf] at e
        cases e

theorem stayFuel_map {p : β → Bool} {p' : β' → Bool} (hp : ∀ b, p (g b) = p' b)
    (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (n : Nat) (b : β') :
    stayFuel p step n (g b) = (stayFuel p' step' n b).map (Outcome.map (Next.map g k)) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [stayFuel, h]
    rcases step' b with _ | e | (n' | r)
    · rfl
    · rfl
    · simp only [Outcome.map, Next.map, hp]
      split
      · exact ih n'
      · rfl
    · rfl

theorem stay_map {p : β → Bool} {p' : β' → Bool} (hp : ∀ b, p (g b) = p' b)
    (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (b : β') :
    stay p step (g b) = (stay p' step' b).map (Outcome.map (Next.map g k)) := by
  cases hr : stay p' step' b with
  | some o =>
    obtain ⟨n, hn⟩ := stayFuel_of_stay hr
    have e := stayFuel_map hp h n b
    rw [hn] at e
    exact stay_of_stayFuel e
  | none =>
    cases hr' : stay p step (g b) with
    | none => rfl
    | some o =>
      obtain ⟨n, hn⟩ := stayFuel_of_stay hr'
      have e := stayFuel_map hp h n b
      rw [hn] at e
      cases hf : stayFuel p' step' n b with
      | none => rw [hf] at e; cases e
      | some o' => rw [stay_of_stayFuel hf] at hr; cases hr

/-- `runPromised`, for at most `n` stays: `none` if it needs more. -/
def runPromisedFuel (p : β → Bool) (step : β → Outcome (Next β ρ)) : Nat → β → Option (Outcome ρ)
  | 0, _ => none
  | n + 1, b =>
    match stay p step b with
    | none => some (Outcome.ub .noProgress)
    | some none => some none
    | some (some (.error e)) => some (some (.error e))
    | some (some (.ok (.ret r))) => some (Outcome.ok r)
    | some (some (.ok (.jump m))) => runPromisedFuel p step n m

theorem runPromised_of_fuel {p : β → Bool} {n : Nat} {b : β} {o : Outcome ρ}
    (h : runPromisedFuel p step n b = some o) : runPromised p step b = o := by
  induction n generalizing b with
  | zero => cases h
  | succ n ih =>
    rw [runPromised]
    simp only [runPromisedFuel] at h
    split at h
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; cases h; rfl
    · rename_i hs; rw [hs]; exact ih h

theorem fuel_of_runPromised {p : β → Bool} {b : β} {x : Except Stop ρ} (h : runPromised p step b = some x) :
    ∃ n, runPromisedFuel p step n b = some (some x) := by
  have := runPromised.fixpoint_induct p step
    (fun f => ∀ b x, f b = some x → ∃ n, runPromisedFuel p step n b = some (some x))
    (Lean.Order.admissible_pi_apply _ fun _ =>
      Lean.Order.admissible_pi _ fun _ => Lean.Order.Option.admissible_eq_some _ _)
    (fun f hf b x h => by
      simp only at h
      split at h
      · rename_i hs; cases h; exact ⟨1, by simp only [runPromisedFuel, hs]; rfl⟩
      · cases h
      · rename_i e hs; cases h; exact ⟨1, by simp only [runPromisedFuel, hs]⟩
      · rename_i r hs; cases h; exact ⟨1, by simp only [runPromisedFuel, hs]; rfl⟩
      · rename_i m hs
        obtain ⟨n, hn⟩ := hf m x h
        exact ⟨n + 1, by simp only [runPromisedFuel, hs]; exact hn⟩)
  exact this b x h

theorem runPromisedFuel_map {p : β → Bool} {p' : β' → Bool} (hp : ∀ b, p (g b) = p' b)
    (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (n : Nat) (b : β') :
    runPromisedFuel p step n (g b) = (runPromisedFuel p' step' n b).map (Outcome.map k) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [runPromisedFuel, stay_map hp h]
    rcases stay p' step' b with _ | _ | _ | (n' | r)
    · rfl
    · rfl
    · rfl
    · exact ih n'
    · rfl

/-- The same, for a run under a promise to progress. -/
theorem runPromised_map {p : β → Bool} {p' : β' → Bool} (hp : ∀ b, p (g b) = p' b)
    (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (b : β') :
    runPromised p step (g b) = Outcome.map k (runPromised p' step' b) := by
  cases hr : runPromised p' step' b with
  | some x =>
    obtain ⟨n, hn⟩ := fuel_of_runPromised hr
    have e := runPromisedFuel_map hp h n b
    rw [hn] at e
    exact runPromised_of_fuel e
  | none =>
    cases hr' : runPromised p step (g b) with
    | none => rfl
    | some y =>
      obtain ⟨n, hn⟩ := fuel_of_runPromised hr'
      have e := runPromisedFuel_map hp h n b
      rw [hn] at e
      cases hf : runPromisedFuel p' step' n b with
      | none => rw [hf] at e; cases e
      | some o =>
        rw [runPromised_of_fuel hf] at hr
        subst hr
        rw [hf] at e
        cases e

/-- What the emitter gives a function under a promise to progress, the same way. -/
theorem promised_map {p : β → Bool} {p' : β' → Bool} (hp : ∀ b, p (g b) = p' b)
    (h : ∀ b, step (g b) = Outcome.map (Next.map g k) (step' b)) (b : β') :
    promised (run step (g b)) (fun _ => runPromised p step (g b)) =
      Outcome.map k (promised (run step' b) fun _ => runPromised p' step' b) := by
  rw [run_map h, runPromised_map hp h]
  rcases run step' b with _ | _ | _ <;> rfl

end Runs

section Monotone
open Lean.Order

variable {γ : Sort _} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_call (x : ExecMem) (e : Effects) (tracked : Bool)
    (k : γ → ExecMem → Nat → Outcome (α × ExecMem)) (hk : monotone k) :
    monotone fun g => ExecMem.call x e tracked (k g) := by
  intro g g' h
  have h2 := hk g g' h { x with
      calls := { id := x.nextCall, effects := e, start := x.next, tracked } :: x.calls
      nextCall := x.nextCall + 1 } x.nextCall
  simp only [ExecMem.call, andThen]
  revert h2
  generalize k g _ _ = a
  generalize k g' _ _ = b
  intro h2
  cases h2 with
  | bot => exact FlatOrder.rel.bot
  | refl => exact FlatOrder.rel.refl

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_withFrame (x : ExecMem) (k : γ → ExecMem → Outcome (α × ExecMem))
    (hk : monotone k) : monotone fun g => ExecMem.withFrame x (k g) := by
  intro g g' h
  have h1 := hk g g' h { x with frame := [] }
  simp only [ExecMem.withFrame, andThen]
  revert h1
  generalize k g _ = a
  generalize k g' _ = b
  intro h1
  cases h1 with
  | bot => exact FlatOrder.rel.bot
  | refl => exact FlatOrder.rel.refl

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_observeAddress (p : PtrVal) (nullCheck : Bool) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.observeAddress p nullCheck (k g) :=
  Mem.monotone_observeAddress p nullCheck k hk

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_returnedArgument (arg result : PtrVal) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.returnedArgument arg result (k g) :=
  Mem.monotone_returnedArgument arg result k hk

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_returnedInt (arg result : Val w) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.returnedInt arg result (k g) :=
  Mem.monotone_returnedInt arg result k hk

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_noaliasResult (x : ExecMem) (p : PtrVal) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.noaliasResult x p (k g) :=
  Mem.monotone_noaliasResult x.toMem p k hk

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_dereferenceable (x : ExecMem) (p : PtrVal) (n : Nat) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.dereferenceable x p n (k g) :=
  Mem.monotone_dereferenceable x.toMem p n k hk

@[partial_fixpoint_monotone]
theorem ExecMem.monotone_assumeNonnull (x : ExecMem) (p : PtrVal) (k : γ → Outcome α)
    (hk : monotone k) : monotone fun g => ExecMem.assumeNonnull x p (k g) :=
  Mem.monotone_assumeNonnull x.toMem p k hk

end Monotone

end IRLean
