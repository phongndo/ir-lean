import IRLean.Mono
import IRLean.Safety

/-! # Refinement for functions with memory

`IRLean.Refines` for the functions the emitter gives a `Mem`: SEM-06, F4. This is the simplest relation that's sound,
and [`docs/refinement.md`](../docs/refinement.md#functions-with-memory) says what it covers and what it doesn't.

A function with memory is `f args (m : Mem) : Outcome (ρ × Mem)`. With the instances here, and the ones for functions,
runs and pairs in `IRLean/Refine.lean`, `Refines src tgt` says: for every argument and every memory, the same for
both, the source's run allows the target's, where two runs that return are related in what they return and in the
memory they leave.

- **A pointer** allows itself, and poison any pointer: `Refine PtrVal`. Its allocation, offset and tags are all
  compared, so the two sides name every allocation the same.
- **A memory** allows one with the same allocations, each the same size and kind, the same layout, frame, and running
  calls, and bytes it allows: `Mem.le`. A poison byte allows any byte. An uninitialized one allows any but poison:
  LLVM reads it as `undef`, which poison doesn't refine, and the model reads it as poison, so this is right under
  both. A byte of a value or of a pointer allows only itself.

What it leaves out is a target that allocates differently: the two memories have to agree on `next`, the number the
next allocation gets, so removing an `alloca` isn't a refinement here, whatever LLVM says.

**A claim has to say where the source has an answer.** Every load and store checks the promises of the calls that are
running, and stops the model where LangRef leaves one open, as a load does on bytes it can't read as its type. `Mem`
ranges over memories with any calls running and any bytes, so a function that touches memory stops the model on some
of them, and `Refines src tgt` as it stands is false. `Outcome.answered`, in `IRLean/Cut.lean`, takes those inputs
out: `Refines (fun x m => (src x m).answered) tgt` is a claim for every memory the model has an answer for.

The lemmas after the instances say that the model's memory operations keep the relation, as `IRLean/Mono.lean` does
for integers, which is what the cut lemma needs of the code after a cut. A load is the exception, and says so. -/

namespace IRLean

/-! ### Bytes, allocations and calls -/

/-- A byte in the source allows this byte in the target. -/
def Byte.le : Byte → Byte → Prop
  | .poison, _ => True
  | .uninit, b => b ≠ .poison
  | .val x, b => b = .val x
  | .ptr p i, b => b = .ptr p i

namespace Byte.le

theorem refl : ∀ b : Byte, Byte.le b b
  | .poison => trivial
  | .uninit => nofun
  | .val _ => rfl
  | .ptr _ _ => rfl

theorem trans {a b c : Byte} (hab : Byte.le a b) (hbc : Byte.le b c) : Byte.le a c := by
  match a, hab with
  | .poison, _ => trivial
  | .val _, hab => subst hab; exact hbc
  | .ptr _ _, hab => subst hab; exact hbc
  | .uninit, hab =>
    match b, hab, hbc with
    | .uninit, _, hbc => exact hbc
    | .val _, _, hbc => intro h; rw [h] at hbc; cases hbc
    | .ptr _ _, _, hbc => intro h; rw [h] at hbc; cases hbc
    | .poison, hab, _ => exact absurd rfl hab

/-! What each kind of byte allows. These pin `Byte.le`: a change to it stops one of them. -/

theorem poison_le (b : Byte) : Byte.le .poison b := trivial

/-- An uninitialized byte allows any byte but poison. LLVM 23 reads it as `undef`, which a value refines and poison
doesn't, and the model reads it as poison, which anything refines: this is what both allow. -/
theorem uninit_le_iff (b : Byte) : Byte.le .uninit b ↔ b ≠ .poison := Iff.rfl

theorem not_uninit_le_poison : ¬ Byte.le .uninit .poison := fun h => h rfl

theorem val_le_iff (x : BitVec 8) (b : Byte) : Byte.le (.val x) b ↔ b = .val x := Iff.rfl

theorem ptr_le_iff (p : Ptr) (i : Nat) (b : Byte) : Byte.le (.ptr p i) b ↔ b = .ptr p i := Iff.rfl

end Byte.le

/-- An allocation in the source allows one of the same size and kind, with bytes it allows. -/
structure Alloc.le (a b : Alloc) : Prop where
  size : b.size = a.size
  readonly : b.readonly = a.readonly
  heap : b.heap = a.heap
  stack : b.stack = a.stack
  bytes : ∀ i, Byte.le (a.bytes i) (b.bytes i)

theorem Alloc.le.refl (a : Alloc) : Alloc.le a a := ⟨rfl, rfl, rfl, rfl, fun _ => Byte.le.refl _⟩

theorem Alloc.le.trans {a b c : Alloc} (hab : Alloc.le a b) (hbc : Alloc.le b c) : Alloc.le a c :=
  ⟨hbc.size.trans hab.size, hbc.readonly.trans hab.readonly, hbc.heap.trans hab.heap, hbc.stack.trans hab.stack,
    fun i => (hab.bytes i).trans (hbc.bytes i)⟩

/-- A running call in the source allows the same call, having written at least as much. What `initializes` covers has
to be written the same on both sides, since what isn't goes back to uninitialized when the call ends. -/
structure Call.le (c d : Call) : Prop where
  id : d.id = c.id
  effects : d.effects = c.effects
  start : d.start = c.start
  tracked : d.tracked = c.tracked
  ranges : d.ranges = c.ranges
  written : ∀ b i, c.written b i = true → d.written b i = true
  initialized : ∀ b i, d.initialized b i = c.initialized b i

theorem Call.le.refl (c : Call) : Call.le c c := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ _ => rfl⟩

theorem Call.le.trans {c d e : Call} (hcd : Call.le c d) (hde : Call.le d e) : Call.le c e :=
  ⟨hde.id.trans hcd.id, hde.effects.trans hcd.effects, hde.start.trans hcd.start, hde.tracked.trans hcd.tracked,
    hde.ranges.trans hcd.ranges, fun b i h => hde.written b i (hcd.written b i h),
    fun b i => (hde.initialized b i).trans (hcd.initialized b i)⟩

/-! ### Lists and options related pointwise -/

/-- Two lists of the same length, related entry by entry. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Forall₂ R l l' → Forall₂ R (a :: l) (b :: l')

theorem forall₂_refl {R : α → α → Prop} (h : ∀ a, R a a) : ∀ l : List α, Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_refl h l)

theorem forall₂_trans {R : α → α → Prop} (h : ∀ a b c, R a b → R b c → R a c) :
    ∀ {l₁ l₂ l₃ : List α}, Forall₂ R l₁ l₂ → Forall₂ R l₂ l₃ → Forall₂ R l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (h _ _ _ h₁ h₂) (forall₂_trans h t₁ t₂)

theorem forall₂_map {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ a b, R a b → S (f a) (g b)) : ∀ {l : List α} {l' : List β}, Forall₂ R l l' →
      Forall₂ S (l.map f) (l'.map g)
  | _, _, .nil => .nil
  | _, _, .cons h₁ t => .cons (h _ _ h₁) (forall₂_map h t)

theorem forall₂_findSome? {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ} (h : ∀ a b, R a b → g b = f a) :
    ∀ {l : List α} {l' : List β}, Forall₂ R l l' → l'.findSome? g = l.findSome? f
  | _, _, .nil => rfl
  | _, _, .cons h₁ t => by
    simp only [List.findSome?_cons, h _ _ h₁, forall₂_findSome? h t]

theorem forall₂_any_eq {R : α → β → Prop} {f : α → Bool} {g : β → Bool} (h : ∀ a b, R a b → g b = f a) :
    ∀ {l : List α} {l' : List β}, Forall₂ R l l' → l'.any g = l.any f
  | _, _, .nil => rfl
  | _, _, .cons h₁ t => by simp only [List.any_cons, h _ _ h₁, forall₂_any_eq h t]

theorem forall₂_any_imp {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (h : ∀ a b, R a b → g b = true → f a = true) :
    ∀ {l : List α} {l' : List β}, Forall₂ R l l' → l'.any g = true → l.any f = true
  | _, _, .nil => fun h' => h'
  | _, _, .cons h₁ t => by
    simp only [List.any_cons, Bool.or_eq_true]
    rintro (hg | hg)
    · exact .inl (h _ _ h₁ hg)
    · exact .inr (forall₂_any_imp h t hg)

theorem forall₂_map_self {R : γ → δ → Prop} {f : α → γ} {g : α → δ} (h : ∀ a, R (f a) (g a)) :
    ∀ l : List α, Forall₂ R (l.map f) (l.map g)
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_map_self h l)

theorem forall₂_nil_left {R : α → β → Prop} {l' : List β} (h : Forall₂ R [] l') : l' = [] := by
  cases h; rfl

theorem forall₂_cons_left {R : α → β → Prop} {a : α} {l : List α} {l' : List β} (h : Forall₂ R (a :: l) l') :
    ∃ b l'', l' = b :: l'' ∧ R a b ∧ Forall₂ R l l'' := by
  cases h with
  | cons hab ht => exact ⟨_, _, rfl, hab, ht⟩

theorem optionRel_trans {R : α → α → Prop} (h : ∀ a b c, R a b → R b c → R a c) {x y z : Option α}
    (hxy : Option.Rel R x y) (hyz : Option.Rel R y z) : Option.Rel R x z := by
  cases hxy with
  | none => cases hyz; exact .none
  | some r₁ => cases hyz with | some r₂ => exact .some (h _ _ _ r₁ r₂)

/-! ### Memory -/

/-- A memory in the source allows this one in the target: the same allocations, by number, each allowing the
target's, and the same layout, frame, allocator and running calls. -/
structure Mem.le (m m' : Mem) : Prop where
  allocs : ∀ b, Option.Rel Alloc.le (m.allocs b) (m'.allocs b)
  next : m'.next = m.next
  base : m'.base = m.base
  frame : m'.frame = m.frame
  failAlloc : m'.failAlloc = m.failAlloc
  calls : Forall₂ Call.le m.calls m'.calls
  nextCall : m'.nextCall = m.nextCall

namespace Mem.le

theorem refl (m : Mem) : Mem.le m m where
  allocs b := by
    cases m.allocs b
    · exact .none
    · exact .some (Alloc.le.refl _)
  next := rfl
  base := rfl
  frame := rfl
  failAlloc := rfl
  calls := forall₂_refl Call.le.refl _
  nextCall := rfl

theorem trans {m₁ m₂ m₃ : Mem} (h : Mem.le m₁ m₂) (h' : Mem.le m₂ m₃) : Mem.le m₁ m₃ where
  allocs b := optionRel_trans (R := Alloc.le) (fun _ _ _ => Alloc.le.trans) (h.allocs b) (h'.allocs b)
  next := h'.next.trans h.next
  base := h'.base.trans h.base
  frame := h'.frame.trans h.frame
  failAlloc := h'.failAlloc.trans h.failAlloc
  calls := forall₂_trans (R := Call.le) (fun _ _ _ => Call.le.trans) h.calls h'.calls
  nextCall := h'.nextCall.trans h.nextCall

/-- Two related memories give the next allocation the same number: what a target that allocates differently
breaks. -/
theorem next_eq {m m' : Mem} (h : Mem.le m m') : m'.next = m.next := h.next

/-- An allocation in the source, and the one the target has for it. -/
theorem alloc {m m' : Mem} (h : Mem.le m m') {b : Nat} {a : Alloc} (ha : m.allocs b = some a) :
    ∃ a', m'.allocs b = some a' ∧ Alloc.le a a' := by
  have h1 := h.allocs b
  revert h1
  rw [ha]
  generalize m'.allocs b = y
  intro h1
  cases h1 with
  | some r => exact ⟨_, rfl, r⟩

/-- An allocation the source doesn't have, the target doesn't either. -/
theorem gone {m m' : Mem} (h : Mem.le m m') {b : Nat} (ha : m.allocs b = none) : m'.allocs b = none := by
  have h1 := h.allocs b
  revert h1
  rw [ha]
  generalize m'.allocs b = y
  intro h1
  cases h1
  rfl

theorem addr {m m' : Mem} (h : Mem.le m m') (p : Ptr) : m'.addr p = m.addr p := by
  simp [Mem.addr, h.base]

end Mem.le

/-! ### The instances -/

/-- Poison allows any pointer, and a pointer only itself: allocation, offset and tags. -/
instance : Refine PtrVal where
  le a b := match a with
    | none => True
    | some p => b = some p
  trans {a b c} hab hbc := by
    cases a with
    | none => trivial
    | some p => cases hab; exact hbc

/-- The memory a run leaves: `Mem.le`. -/
instance : Refine Mem where
  le := Mem.le
  trans := Mem.le.trans

instance : Refine.Reflexive PtrVal where
  refl
    | none => trivial
    | some _ => rfl

instance : Refine.Reflexive Mem := ⟨Mem.le.refl⟩

instance : Refine.PoisonLeast PtrVal := ⟨fun _ => trivial⟩

namespace Refine

theorem ptr_none (b : PtrVal) : Refine.le (none : PtrVal) b := trivial
theorem ptr_some (p : Ptr) (b : PtrVal) : Refine.le (some p : PtrVal) b ↔ b = some p := Iff.rfl
theorem mem_iff (m m' : Mem) : Refine.le m m' ↔ Mem.le m m' := Iff.rfl

theorem ptr_iff (a b : PtrVal) : Refine.le a b ↔ a = none ∨ b = a := by
  cases a with
  | none => exact iff_of_true trivial (Or.inl rfl)
  | some p => exact ⟨Or.inr, fun h => h.resolve_left nofun⟩

end Refine

/-! ### What an access needs, and what a store leaves

For proofs about loads and stores on any memory: what a store's success depends on, that the memory it leaves answers
the same checks, and that a load of what was just stored gives it back. -/

namespace Mem

variable {m m' : Mem} {w : Nat}

/-- The bytes a `store` of `v` writes: poison for poison. -/
def intBytes (v : Val w) (i : Nat) : Byte :=
  match v with
  | none => .poison
  | some x => intByte x i

/-- `storeInt`, with the bytes it writes named. -/
theorem storeInt_eq (m : Mem) (p : PtrVal) (v : Val w) (align : Nat) :
    m.storeInt p v align =
      match m.access p (w / 8) align with
      | .error e => Outcome.ub e
      | .ok (q, a) =>
        if a.readonly then Outcome.ub .writeToConstant else
        match m.check q a true with
        | some e => some (.error e)
        | none => Outcome.ok (m.write q a (w / 8) (intBytes v)) := by
  unfold storeInt intBytes
  rfl

/-- What a successful access says: the pointer, its allocation, the bounds and the alignment. -/
theorem access_ok_iff {p : PtrVal} {n align : Nat} {q : Ptr} {a : Alloc} :
    m.access p n align = .ok (q, a) ↔
      p = some q ∧ m.allocs q.block = some a ∧ q.offset.toNat + n ≤ a.size ∧
        (align = 1 ∨ (m.addr q).toNat % align = 0) := by
  cases p with
  | none => simp [access]
  | some q' =>
    simp only [access, Option.some.injEq]
    cases hq : m.allocs q'.block with
    | none => simp; intro h; subst h; simp [hq]
    | some a' =>
      simp only
      by_cases hn : q'.offset.toNat + n > a'.size
      · simp only [hn, ite_true, reduceCtorEq, false_iff]
        rintro ⟨rfl, ha, hle, _⟩
        rw [hq] at ha
        cases ha
        omega
      · simp only [hn, ite_false]
        by_cases hal : (align != 1 && (m.addr q').toNat % align != 0) = true
        · simp only [hal, ite_true, reduceCtorEq, false_iff]
          rintro ⟨rfl, _, _, h⟩
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hal
          rcases h with h | h
          · exact hal.1 h
          · exact hal.2 h
        · simp only [hal, Bool.false_eq_true, ite_false, Except.ok.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩
            refine ⟨rfl, hq, by omega, ?_⟩
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hal
            by_cases h1 : align = 1
            · exact .inl h1
            · exact .inr (hal h1)
          · rintro ⟨rfl, ha, _, _⟩
            rw [hq] at ha
            cases ha
            exact ⟨rfl, rfl⟩

/-- An allocation with the `n` bytes from `o` on replaced by `f`'s. -/
def Alloc.overlay (a : Alloc) (o n : Nat) (f : Nat → Byte) : Alloc :=
  { a with bytes := fun i => if o ≤ i ∧ i < o + n then f (i - o) else a.bytes i }

theorem write_allocs_self (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) :
    (m.write q a n f).allocs q.block = some (Alloc.overlay a q.offset.toNat n f) := by
  simp [write, setAlloc, Alloc.overlay]

theorem write_allocs_other (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) {b : Nat}
    (hb : b ≠ q.block) : (m.write q a n f).allocs b = m.allocs b := by
  simp [write, setAlloc, hb]

theorem write_addr (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) (p : Ptr) :
    (m.write q a n f).addr p = m.addr p := rfl

theorem isRunning_write (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) (call : Nat) :
    (m.write q a n f).isRunning call = m.isRunning call := by
  simp only [isRunning, write, List.any_map]
  congr 1
  funext c
  simp only [Function.comp]
  split <;> rfl

/-- A check asks the same of two allocations of the same kind. -/
theorem check_congr (m : Mem) (q : Ptr) {a a' : Alloc} (hr : a'.readonly = a.readonly) (hs : a'.stack = a.stack)
    (write : Bool) : m.check q a' write = m.check q a write := by
  simp only [check, callRule, callAccess, hr, hs]

/-- A store leaves every check as it was: it changes no call's promises, and no tag's. -/
theorem check_write (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) (q' : Ptr) (a' : Alloc)
    (wr : Bool) : (m.write q a n f).check q' a' wr = m.check q' a' wr := by
  have ht : (m.write q a n f).tagRule wr = m.tagRule wr := by
    funext t
    simp only [tagRule, isRunning_write]
  have hc : (m.write q a n f).calls.findSome? (fun c => callRule c q' a' wr) =
      m.calls.findSome? fun c => callRule c q' a' wr := by
    simp only [write, List.findSome?_map]
    congr 1
    funext c
    simp only [Function.comp]
    by_cases htr : c.tracked = true
    · simp only [htr, ite_true]; rfl
    · simp only [htr, Bool.false_eq_true, ite_false]
  simp only [check, ht, hc]

/-- After a store, a read through the pointer that stored sees the bytes it wrote, whatever promises are running. -/
theorem unwritten_write_self (m : Mem) (q : Ptr) (a a' : Alloc) (n : Nat) (f : Nat → Byte) {i : Nat}
    (hi : q.offset.toNat ≤ i ∧ i < q.offset.toNat + n) : (m.write q a n f).unwritten q a' i = false := by
  simp only [unwritten, write, List.any_map, List.any_eq_false, Function.comp]
  intro c _
  by_cases ht : c.tracked = true
  · simp only [ht, ite_true, Bool.true_and, beq_self_eq_true, hi.1, hi.2, decide_true, Bool.and_true, Bool.true_or,
      Bool.not_true, Bool.false_and, Bool.false_or]
    cases hinit : q.tags.any fun t => t.call == c.id && t.initializes <;> simp
  · simp [ht]

theorem visible_write_self (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) {i : Nat} (hi : i < n) :
    (m.write q a n f).visible q (Alloc.overlay a q.offset.toNat n f) (q.offset.toNat + i) = f i := by
  have hr : q.offset.toNat ≤ q.offset.toNat + i ∧ q.offset.toNat + i < q.offset.toNat + n := by omega
  simp [visible, unwritten_write_self m q a _ n f hr, Alloc.overlay, hr]

/-- The same access succeeds after a store through it, on the allocation as the store left it. -/
theorem access_write_self {q : Ptr} {a : Alloc} {k align : Nat} (h : m.access (some q) k align = .ok (q, a))
    (n : Nat) (f : Nat → Byte) :
    (m.write q a n f).access (some q) k align = .ok (q, Alloc.overlay a q.offset.toNat n f) := by
  obtain ⟨_, _, hn, hal⟩ := access_ok_iff.1 h
  exact access_ok_iff.2 ⟨rfl, write_allocs_self m q a n f, hn, hal⟩

/-- A store's bytes, read back as an integer of the width stored: the value, or poison for poison. -/
theorem collect_intBytes (v : Val w) (h0 : 0 < w / 8) :
    collect ((List.range (w / 8)).map (intBytes v)) =
      .ok (v.map fun x => x.toNat % 2 ^ (8 * (w / 8))) := by
  cases v with
  | some x => exact collect_bytes x.toNat (w / 8)
  | none =>
    have : ∀ n, 0 < n → collect ((List.range n).map (intBytes (none : Val w))) = .ok none := by
      intro n
      induction n with
      | zero => intro h; omega
      | succ n ih =>
        intro _
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        have e : (intBytes (none : Val w)) ∘ Nat.succ = intBytes (none : Val w) := rfl
        rw [e]
        cases n with
        | zero => rfl
        | succ n => simp only [intBytes, collect, ih (by omega)]
    exact this _ h0

/-- **A load of what was just stored gives it back,** if it's allowed to read: the same pointer, the same width and
alignment, a whole number of bytes. -/
theorem loadInt_write_self {q : Ptr} {a : Alloc} {align : Nat} (h : m.access (some q) (w / 8) align = .ok (q, a))
    (hw : w % 8 = 0) (h0 : 0 < w / 8) (v : Val w) :
    (m.write q a (w / 8) (intBytes v)).loadInt w (some q) align =
      match m.check q a false with
      | some e => some (.error e)
      | none => Outcome.ok v := by
  have hread : (m.write q a (w / 8) (intBytes v)).read q (Alloc.overlay a q.offset.toNat (w / 8) (intBytes v))
      q.offset.toNat (w / 8) = (List.range (w / 8)).map (intBytes v) := by
    simp only [read]
    apply List.map_congr_left
    intro i hi
    exact visible_write_self m q a (w / 8) (intBytes v) (List.mem_range.mp hi)
  simp only [loadInt, access_write_self h, check_write, hread, collect_intBytes v h0]
  rw [check_congr m q (a := a) (a' := Alloc.overlay a q.offset.toNat (w / 8) (intBytes v)) rfl rfl false]
  cases m.check q a false with
  | some e => rfl
  | none =>
    cases v with
    | none => rfl
    | some x =>
      simp only [Option.map]
      have : BitVec.ofNat w (x.toNat % 2 ^ (8 * (w / 8))) = x := by
        rw [show 8 * (w / 8) = w by omega, Nat.mod_eq_of_lt x.isLt]
        simp
      rw [this]

/-- A store ends in an error, undefined behavior or a model stop, or returns a memory. It always finishes. -/
theorem storeInt_error_or_ok (m : Mem) (p : PtrVal) (v : Val w) (align : Nat) :
    (∃ e, m.storeInt p v align = some (.error e)) ∨ ∃ m₁, m.storeInt p v align = Outcome.ok m₁ := by
  rw [storeInt_eq]
  cases m.access p (w / 8) align with
  | error e => exact .inl ⟨_, rfl⟩
  | ok qa =>
    obtain ⟨q, a⟩ := qa
    simp only
    split
    · exact .inl ⟨_, rfl⟩
    · cases m.check q a true with
      | some e => exact .inl ⟨e, rfl⟩
      | none => exact .inr ⟨_, rfl⟩

/-- What a store that returns did: the access was valid, to an allocation that can be written, no promise forbade
it, and the memory is the old one with the value's bytes written. -/
theorem storeInt_ok {p : PtrVal} {v : Val w} {align : Nat} {m₁ : Mem} (h : m.storeInt p v align = Outcome.ok m₁) :
    ∃ q a, p = some q ∧ m.access (some q) (w / 8) align = .ok (q, a) ∧ a.readonly = false ∧
      m.check q a true = none ∧ m₁ = m.write q a (w / 8) (intBytes v) := by
  rw [storeInt_eq] at h
  cases hacc : m.access p (w / 8) align with
  | error e => rw [hacc] at h; cases h
  | ok qa =>
    obtain ⟨q, a⟩ := qa
    rw [hacc] at h
    simp only at h
    have hp : p = some q := (access_ok_iff.1 hacc).1
    subst hp
    cases hr : a.readonly with
    | true => simp only [hr, ite_true] at h; cases h
    | false =>
      simp only [hr, Bool.false_eq_true, ite_false] at h
      cases hc : m.check q a true with
      | some e => rw [hc] at h; cases h
      | none =>
        rw [hc] at h
        exact ⟨q, a, rfl, hacc, hr, hc, by cases h; rfl⟩

/-- Whether a store returns doesn't depend on the value stored, and nor does where it writes. -/
theorem storeInt_ok_of_ok {p : PtrVal} {v : Val w} {align : Nat} {m₁ : Mem} (h : m.storeInt p v align = Outcome.ok m₁)
    (v' : Val w) :
    ∃ q a, m.access (some q) (w / 8) align = .ok (q, a) ∧ m₁ = m.write q a (w / 8) (intBytes v) ∧
      m.storeInt p v' align = Outcome.ok (m.write q a (w / 8) (intBytes v')) := by
  obtain ⟨q, a, rfl, hacc, hr, hc, rfl⟩ := storeInt_ok h
  refine ⟨q, a, hacc, rfl, ?_⟩
  simp only [storeInt_eq, hacc, hr, hc, Bool.false_eq_true, ite_false]

/-- **A store through the pointer a store just returned from returns too,** whatever promises are running: the
first changed none of them. -/
theorem storeInt_write_self {q : Ptr} {a : Alloc} {align : Nat} (hacc : m.access (some q) (w / 8) align = .ok (q, a))
    (hr : a.readonly = false) (hc : m.check q a true = none) (f : Nat → Byte) (v' : Val w) :
    (m.write q a (w / 8) f).storeInt (some q) v' align =
      Outcome.ok ((m.write q a (w / 8) f).write q (Alloc.overlay a q.offset.toNat (w / 8) f) (w / 8) (intBytes v')) := by
  have hc' : (m.write q a (w / 8) f).check q (Alloc.overlay a q.offset.toNat (w / 8) f) true = none := by
    rw [check_write, check_congr m q (a := a) (a' := Alloc.overlay a q.offset.toNat (w / 8) f) rfl rfl true, hc]
  simp only [storeInt_eq, access_write_self hacc, hc']
  simp [Alloc.overlay, hr]

/-- A store over a store through the same pointer leaves what the second alone would. -/
theorem write_write_le (m : Mem) (q : Ptr) (a : Alloc) (n : Nat) (f g : Nat → Byte) :
    Mem.le ((m.write q a n f).write q (Alloc.overlay a q.offset.toNat n f) n g) (m.write q a n g) where
  allocs b := by
    by_cases hb : b = q.block
    · subst hb
      rw [write_allocs_self, write_allocs_self]
      refine .some ⟨rfl, rfl, rfl, rfl, fun i => ?_⟩
      simp only [Alloc.overlay]
      split <;> exact Byte.le.refl _
    · rw [write_allocs_other _ _ _ _ _ hb, write_allocs_other _ _ _ _ _ hb, write_allocs_other _ _ _ _ _ hb]
      cases m.allocs b
      · exact .none
      · exact .some (Alloc.le.refl _)
  next := rfl
  base := rfl
  frame := rfl
  failAlloc := rfl
  calls := by
    simp only [write, List.map_map]
    refine forall₂_map (R := Eq) (fun c d hcd => ?_) (forall₂_refl (fun _ => rfl) m.calls)
    subst hcd
    simp only [Function.comp]
    by_cases ht : c.tracked = true
    · simp only [ht, ite_true]
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun b i hw => ?_, fun b i => ?_⟩
      · simp only [Bool.or_eq_true] at hw ⊢
        rcases hw with hw | hw | hw
        · exact .inl hw
        · exact .inl hw
        · exact .inr hw
      · simp only
        cases (q.tags.any fun t => t.call == c.id && t.initializes) <;>
          cases (b == q.block && decide (q.offset.toNat ≤ i) && decide (i < q.offset.toNat + n)) <;>
          cases c.initialized b i <;> rfl
    · simp only [ht, Bool.false_eq_true, ite_false]
      exact Call.le.refl c
  nextCall := rfl

/-- **A store that's overwritten can go.** Two stores through one pointer, with nothing between them, are allowed to
be the second alone, on every memory: where the first is undefined or the model has no answer for it, anything is,
and where it returns, so does the second, to a memory the second alone leaves. -/
theorem storeInt_overwritten (m : Mem) (p : PtrVal) (v v' : Val w) (align : Nat) :
    Outcome.Sim Mem.le (andThen (m.storeInt p v align) fun m₁ => m₁.storeInt p v' align)
      (m.storeInt p v' align) := by
  rcases storeInt_error_or_ok m p v align with ⟨e, he⟩ | ⟨m₁, h₁⟩
  · rw [he]; trivial
  · obtain ⟨q, a, rfl, hacc, hr, hc, rfl⟩ := storeInt_ok h₁
    rw [h₁, andThen_ok, storeInt_write_self hacc hr hc]
    have h₂ : m.storeInt (some q) v' align = Outcome.ok (m.write q a (w / 8) (intBytes v')) := by
      simp only [storeInt_eq, hacc, hr, hc, Bool.false_eq_true, ite_false]
    rw [h₂]
    exact Outcome.Sim.ok (write_write_le m q a (w / 8) (intBytes v) (intBytes v'))

/-- **A load after a store through the same pointer gives what was stored,** or is undefined, or has no answer: it's
never another value. The width is a whole number of bytes, and the same as the store's, as is the alignment. -/
theorem loadInt_of_storeInt {p : PtrVal} {v : Val w} {align : Nat} {m₁ : Mem}
    (h : m.storeInt p v align = Outcome.ok m₁) (hw : w % 8 = 0) (h0 : 0 < w / 8) :
    m₁.loadInt w p align = Outcome.ok v ∨ ∃ e, m₁.loadInt w p align = some (.error e) := by
  obtain ⟨q, a, rfl, hacc, _, _, rfl⟩ := storeInt_ok h
  rw [loadInt_write_self hacc hw h0]
  cases m.check q a false with
  | none => exact .inl rfl
  | some e => exact .inr ⟨e, rfl⟩

end Mem

/-! ### The operations keep the relation

What the cut lemma needs of memory: the same operation, on memories, pointers and values the target's refine, gives
runs that are related. -/

namespace Mem.le

variable {m m' : Mem} {w : Nat}

theorem isRunning (h : Mem.le m m') (call : Nat) : m'.isRunning call = m.isRunning call :=
  forall₂_any_eq (fun _ _ hcd => by rw [hcd.id]) h.calls

/-- The promises in force ask the same of an access on both sides. -/
theorem check (h : Mem.le m m') {a a' : Alloc} (ha : Alloc.le a a') (q : Ptr) (wr : Bool) :
    m'.check q a' wr = m.check q a wr := by
  have ht : m'.tagRule wr = m.tagRule wr := by
    funext t
    simp only [Mem.tagRule, h.isRunning]
  have hc : m'.calls.findSome? (fun c => Mem.callRule c q a' wr) =
      m.calls.findSome? fun c => Mem.callRule c q a wr :=
    forall₂_findSome?
      (fun c d hcd => by
        simp only [Mem.callRule, Mem.callAccess, hcd.id, hcd.effects, hcd.start, ha.readonly, ha.stack])
      h.calls
  simp only [Mem.check, ht, hc]

/-- An access that succeeds in the source succeeds in the target, on the allocation it has there, and one that
fails, fails the same way. -/
theorem access (h : Mem.le m m') (p : PtrVal) (n align : Nat) :
    match m.access p n align with
    | .error e => m'.access p n align = .error e
    | .ok (q, a) => ∃ a', m'.access p n align = .ok (q, a') ∧ Alloc.le a a' := by
  cases p with
  | none => rfl
  | some q =>
    simp only [Mem.access]
    cases hq : m.allocs q.block with
    | none => simp only [h.gone hq]
    | some a =>
      obtain ⟨a', ha', hle⟩ := h.alloc hq
      simp only [ha', hle.size, h.addr]
      by_cases hn : q.offset.toNat + n > a.size
      · simp only [hn, ite_true]
      · simp only [hn, ite_false]
        by_cases hal : (align != 1 && (m.addr q).toNat % align != 0) = true
        · simp only [hal, ite_true]
        · simp only [hal, Bool.false_eq_true, ite_false]
          exact ⟨a', rfl, hle⟩

/-- A store's bytes on related memories and allocations, where the target's bytes are allowed, leave related
memories. -/
theorem write (h : Mem.le m m') {a a' : Alloc} (ha : Alloc.le a a') (q : Ptr) (n : Nat) {f f' : Nat → Byte}
    (hf : ∀ i, Byte.le (f i) (f' i)) : Mem.le (m.write q a n f) (m'.write q a' n f') where
  allocs b := by
    by_cases hb : b = q.block
    · subst hb
      rw [Mem.write_allocs_self, Mem.write_allocs_self]
      refine .some ⟨ha.size, ha.readonly, ha.heap, ha.stack, fun i => ?_⟩
      simp only [Mem.Alloc.overlay]
      split
      · exact hf _
      · exact ha.bytes i
    · rw [Mem.write_allocs_other _ _ _ _ _ hb, Mem.write_allocs_other _ _ _ _ _ hb]
      exact h.allocs b
  next := h.next
  base := h.base
  frame := h.frame
  failAlloc := h.failAlloc
  calls := by
    simp only [Mem.write]
    refine forall₂_map (fun c d hcd => ?_) h.calls
    by_cases ht : c.tracked = true
    · have ht' : d.tracked = true := hcd.tracked.trans ht
      simp only [ht, ht', ite_true]
      refine ⟨hcd.id, hcd.effects, hcd.start, rfl, hcd.ranges, fun b i hw => ?_, fun b i => ?_⟩
      · simp only [Bool.or_eq_true] at hw ⊢
        exact hw.imp_right (hcd.written b i)
      · simp only [hcd.id, hcd.initialized]
    · have ht' : ¬ d.tracked = true := fun h' => ht (hcd.tracked ▸ h')
      simp only [ht, ht', Bool.false_eq_true, ite_false]
      exact hcd
  nextCall := h.nextCall

/-- **`store` keeps the relation:** on memories, pointers and values the target's refine, the stores are related.
Storing a value where the source stored poison leaves bytes the source's allow. -/
theorem storeInt (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {v v' : Val w} (hv : Refine.le v v')
    (align : Nat) : Outcome.Sim Refine.le (m.storeInt p v align) (m'.storeInt p' v' align) := by
  cases p with
  | none => simp only [Mem.storeInt_eq, Mem.access]; trivial
  | some q =>
    cases hp
    rw [Mem.storeInt_eq, Mem.storeInt_eq]
    have hacc := h.access (some q) (w / 8) align
    revert hacc
    cases m.access (some q) (w / 8) align with
    | error e => intro _; trivial
    | ok qa =>
      obtain ⟨q₀, a⟩ := qa
      rintro ⟨a', hacc', hle⟩
      simp only [hacc', hle.readonly, h.check hle]
      split
      · trivial
      · cases m.check q₀ a true with
        | some e => trivial
        | none =>
          refine Outcome.Sim.ok (h.write hle q₀ (w / 8) fun i => ?_)
          cases v with
          | none => trivial
          | some x => cases hv; exact Byte.le.refl _

/-- A byte as a pointer reads it: the source's allows the target's. A byte a promise makes poison in the target, it
makes poison in the source. -/
theorem visible (h : Mem.le m m') {a a' : Alloc} (ha : Alloc.le a a') (q : Ptr) (o : Nat) :
    Byte.le (m.visible q a o) (m'.visible q a' o) := by
  have hu : m'.unwritten q a' o = true → m.unwritten q a o = true := by
    simp only [Mem.unwritten]
    refine forall₂_any_imp (fun c d hcd => ?_) h.calls
    simp only [Mem.callAccess, hcd.id, hcd.effects, hcd.start, hcd.tracked, hcd.ranges, hcd.initialized, ha.readonly,
      ha.stack]
    cases hw : c.written q.block o with
    | true => simp only [hcd.written _ _ hw]; exact id
    | false =>
      cases d.written q.block o
      · exact id
      · simp only [Bool.not_true, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and, Bool.and_eq_true,
          Bool.or_eq_true]
        rintro ⟨h₁, h₂⟩
        exact ⟨h₁, .inr h₂⟩
  simp only [Mem.visible]
  cases hs : m.unwritten q a o with
  | true => trivial
  | false =>
    have : m'.unwritten q a' o = false := by
      cases ht : m'.unwritten q a' o with
      | false => rfl
      | true => rw [hu ht] at hs; cases hs
    simp only [this, Bool.false_eq_true, ite_false]
    exact ha.bytes o

/-- Bytes that read as a number in the source read as the same number in the target. Where the source's read as
poison, the target's may read as anything, or not as an integer at all. -/
theorem collect {bs bs' : List Byte} (h : Forall₂ Byte.le bs bs') {n : Nat} (hc : Mem.collect bs = .ok (some n)) :
    Mem.collect bs' = .ok (some n) := by
  induction h generalizing n with
  | nil => exact hc
  | @cons b b' l l' hb _ ih =>
    cases b with
    | uninit => simp only [Mem.collect] at hc; split at hc <;> cases hc
    | poison => simp only [Mem.collect] at hc; split at hc <;> cases hc
    | ptr _ _ => cases hc
    | val x =>
      have hb' : b' = .val x := hb
      subst hb'
      simp only [Mem.collect] at hc ⊢
      cases hr : Mem.collect l with
      | error e => rw [hr] at hc; cases hc
      | ok r =>
        rw [hr] at hc
        cases r with
        | none => cases hc
        | some k => rw [ih hr]; exact hc

/-- **`load` keeps the relation, unless the target can't read its bytes as an integer.** On memories and pointers the
target's refine, the loads are related, or the target's stops the model. The second happens only where the source
read poison and the target's bytes hold a pointer. -/
theorem loadInt (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (w align : Nat) :
    Outcome.Sim Refine.le (m.loadInt w p align) (m'.loadInt w p' align) ∨
      ∃ s, m'.loadInt w p' align = Outcome.stop s := by
  cases p with
  | none => exact .inl trivial
  | some q =>
    cases hp
    have hacc := h.access (some q) (w / 8) align
    simp only [Mem.loadInt]
    revert hacc
    cases m.access (some q) (w / 8) align with
    | error e => intro _; exact .inl trivial
    | ok qa =>
      obtain ⟨q₀, a⟩ := qa
      rintro ⟨a', hacc', hle⟩
      simp only [hacc', h.check hle]
      cases m.check q₀ a false with
      | some e => exact .inl trivial
      | none =>
        have hbytes : Forall₂ Byte.le (m.read q₀ a q₀.offset.toNat (w / 8)) (m'.read q₀ a' q₀.offset.toNat (w / 8)) :=
          forall₂_map_self (fun i => h.visible hle q₀ _) _
        cases hs : Mem.collect (m.read q₀ a q₀.offset.toNat (w / 8)) with
        | error e => exact .inl trivial
        | ok r =>
          cases r with
          | some n => simp only [collect hbytes hs]; exact .inl (Outcome.Sim.ok (Refine.refl_val _))
          | none =>
            cases Mem.collect (m'.read q₀ a' q₀.offset.toNat (w / 8)) with
            | error e => exact .inr ⟨e, rfl⟩
            | ok r' => cases r' <;> exact .inl (Outcome.Sim.ok (Refine.val_none _))

/-- A load that gives a value in the source gives the same in the target. -/
theorem loadInt_some (h : Mem.le m m') {p : PtrVal} {w align : Nat} {x : BitVec w}
    (hl : m.loadInt w p align = Outcome.ok (some x)) : m'.loadInt w p align = Outcome.ok (some x) := by
  rcases h.loadInt (Refine.Reflexive.refl p) w align with hsim | ⟨s, hs⟩
  · rw [hl] at hsim
    obtain ⟨y, hy, hxy⟩ := hsim
    rw [hy]
    exact congrArg Outcome.ok hxy
  · -- The target's bytes are the source's wherever those are a value, so it can't stop where the source gave one.
    exfalso
    cases p with
    | none => simp [Mem.loadInt, Mem.access, Outcome.ub, Outcome.ok] at hl
    | some q =>
      have hacc := h.access (some q) (w / 8) align
      simp only [Mem.loadInt] at hl hs
      revert hacc
      cases hq : m.access (some q) (w / 8) align with
      | error e => rw [hq] at hl; cases hl
      | ok qa =>
        obtain ⟨q₀, a⟩ := qa
        rintro ⟨a', hacc', hle⟩
        rw [hq] at hl
        simp only [hacc', h.check hle] at hl hs
        cases hc : m.check q₀ a false with
        | some e => rw [hc] at hl; cases hl
        | none =>
          rw [hc] at hl hs
          simp only at hl hs
          have hbytes : Forall₂ Byte.le (m.read q₀ a q₀.offset.toNat (w / 8))
              (m'.read q₀ a' q₀.offset.toNat (w / 8)) :=
            forall₂_map_self (fun i => h.visible hle q₀ _) _
          cases hcol : Mem.collect (m.read q₀ a q₀.offset.toNat (w / 8)) with
          | error e => rw [hcol] at hl; cases hl
          | ok r =>
            cases r with
            | none => rw [hcol] at hl; cases hl
            | some n => rw [collect hbytes hcol] at hs; cases hs

/-- `getelementptr` asks the same of both memories: the layout, and the allocation's size. -/
theorem gep_eq (h : Mem.le m m') (p : PtrVal) (off : Val 64) (inbounds nusw nuw : Bool) :
    m'.gep p off inbounds nusw nuw = m.gep p off inbounds nusw nuw := by
  cases p with
  | none => rfl
  | some q =>
    cases off with
    | none => rfl
    | some d =>
      simp only [Mem.gep, h.addr]
      cases hq : m.allocs q.block with
      | none => simp only [h.gone hq]
      | some a =>
        obtain ⟨a', ha', hle⟩ := h.alloc hq
        simp only [ha', hle.size]

/-- **`getelementptr` keeps the relation.** A poison pointer or offset gives poison. -/
theorem gep (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {off off' : Val 64} (ho : Refine.le off off')
    {inbounds nusw nuw : Bool} :
    Refine.le (m.gep p off inbounds nusw nuw) (m'.gep p' off' inbounds nusw nuw) := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    cases off with
    | none => trivial
    | some d =>
      cases ho
      rw [h.gep_eq]
      exact Refine.Reflexive.refl _

/-- A pointer as an integer: the layout is the same. -/
theorem toVal (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') : Refine.le (m.toVal p) (m'.toVal p') := by
  cases p with
  | none => trivial
  | some q => cases hp; simp only [Mem.toVal, h.addr]; exact Refine.refl_val _

theorem nonnull (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') :
    Refine.le (m.nonnull p) (m'.nonnull p') := by
  cases p with
  | none => trivial
  | some q => cases hp; simp only [Mem.nonnull, h.addr]; exact Refine.Reflexive.refl _

theorem aligned (h : Mem.le m m') (align : Nat) {p p' : PtrVal} (hp : Refine.le p p') :
    Refine.le (m.aligned align p) (m'.aligned align p') := by
  cases p with
  | none => trivial
  | some q => cases hp; simp only [Mem.aligned, h.addr]; exact Refine.Reflexive.refl _

/-- `dereferenceable`: a pointer that can't be read is undefined in the source. -/
theorem dereferenceable (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') (n : Nat) {r : α → β → Prop}
    {k : Outcome α} {k' : Outcome β} (hk : Outcome.Sim r k k') :
    Outcome.Sim r (m.dereferenceable p n k) (m'.dereferenceable p' n k') := by
  cases p with
  | none => trivial
  | some q =>
    cases hp
    have hacc := h.access (some q) n 1
    simp only [Mem.dereferenceable]
    revert hacc
    cases m.access (some q) n 1 with
    | error e => intro _; trivial
    | ok qa =>
      obtain ⟨q₀, a⟩ := qa
      rintro ⟨a', hacc', _⟩
      simp only [hacc']
      exact hk

/-- Looking at a pointer's address, where it's the same pointer on both sides. A pointer the target has for the
source's poison could carry a tag that makes the look stop the model, so that case isn't here. -/
theorem observeAddress (p : PtrVal) (nullCheck : Bool) {r : α → β → Prop} {k : Outcome α} {k' : Outcome β}
    (hk : Outcome.Sim r k k') :
    Outcome.Sim r (Mem.observeAddress p nullCheck k) (Mem.observeAddress p nullCheck k') := by
  cases p with
  | none => exact hk
  | some q =>
    simp only [Mem.observeAddress]
    split
    · trivial
    · exact hk

/-- **`alloca` keeps the relation:** both sides give the new allocation the same number. -/
theorem alloca (h : Mem.le m m') {size size' : Val 64} (hs : Refine.le size size') (dead : Bool) :
    Outcome.Sim Refine.le (m.alloca size dead) (m'.alloca size' dead) := by
  cases size with
  | none => trivial
  | some n =>
    cases hs
    simp only [Mem.alloca, h.next]
    refine Outcome.Sim.ok ⟨Refine.Reflexive.refl _, ?_⟩
    exact
      { allocs := fun b => by
          by_cases hb : b = m.next
          · simp only [hb, beq_self_eq_true, ite_true]; exact .some (Alloc.le.refl _)
          · simp only [show (b == m.next) = false by simpa using hb, Bool.false_eq_true, ite_false]
            exact h.allocs b
        next := rfl
        base := h.base
        frame := by simp only [h.frame]
        failAlloc := h.failAlloc
        calls := h.calls
        nextCall := h.nextCall }

/-- **A function's frame keeps the relation:** related bodies, started on related memories, leave related memories
once their `alloca`s are freed. -/
theorem withFrame (h : Mem.le m m') {r : α → β → Prop} {body : Mem → Outcome (α × Mem)}
    {body' : Mem → Outcome (β × Mem)}
    (hb : ∀ n n', Mem.le n n' → Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (body n) (body' n')) :
    Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (m.withFrame body) (m'.withFrame body') := by
  simp only [Mem.withFrame]
  refine Outcome.Sim.andThen (hb _ _ { h with frame := rfl }) ?_
  rintro ⟨x, n⟩ ⟨y, n'⟩ ⟨hxy, hn⟩
  have hn : Mem.le n n' := hn
  refine Outcome.Sim.ok ⟨hxy, ?_⟩
  exact
    { allocs := fun b => by
        have hf : n'.frame = n.frame := hn.frame
        simp only [hf]
        split
        · exact .none
        · exact hn.allocs b
      next := hn.next
      base := hn.base
      frame := h.frame
      failAlloc := hn.failAlloc
      calls := hn.calls
      nextCall := hn.nextCall }

/-- `store` of a vector keeps the relation, lane by lane. -/
theorem storeVec (h : Mem.le m m') {p p' : PtrVal} (hp : Refine.le p p') {n : Nat} {v v' : Vec n w}
    (hv : Refine.le v v') (align : Nat) :
    Outcome.Sim Refine.le (m.storeVec p v align) (m'.storeVec p' v' align) := by
  cases p with
  | none => simp only [Mem.storeVec, Mem.access]; trivial
  | some q =>
    cases hp
    simp only [Mem.storeVec]
    have hacc := h.access (some q) (n * (w / 8)) align
    revert hacc
    cases m.access (some q) (n * (w / 8)) align with
    | error e => intro _; trivial
    | ok qa =>
      obtain ⟨q₀, a⟩ := qa
      rintro ⟨a', hacc', hle⟩
      simp only [hacc', hle.readonly, h.check hle]
      split
      · trivial
      · cases m.check q₀ a true with
        | some e => trivial
        | none =>
          refine Outcome.Sim.ok (h.write hle q₀ _ fun i => ?_)
          have hl := Mono.lane hv (i / (w / 8))
          revert hl
          cases Vec.lane v (i / (w / 8)) with
          | none => intro _; trivial
          | some x => intro hl; rw [(Refine.val_some _ _).1 hl]; exact Byte.le.refl _

end Mem.le

/-- The same memory on both sides, for the operations a proof needs most: where a cut doesn't write, the memory
after it is the memory before, and a pointer or a value is all that's refined. -/
theorem Mono.loadInt (m : Mem) {p p' : PtrVal} (hp : Refine.le p p') (w align : Nat) :
    Outcome.Sim Refine.le (m.loadInt w p align) (m.loadInt w p' align) := by
  cases p with
  | none => trivial
  | some q => cases hp; exact Outcome.Sim.refl (fun x => Refine.refl_val x) _

theorem Mono.gep (m : Mem) {p p' : PtrVal} (hp : Refine.le p p') {off off' : Val 64} (ho : Refine.le off off')
    {inbounds nusw nuw : Bool} :
    Refine.le (m.gep p off inbounds nusw nuw) (m.gep p' off' inbounds nusw nuw) :=
  (Mem.le.refl m).gep hp ho

/-- `noundef` on a pointer: poison is undefined in the source. -/
theorem Mono.noundefPtr {r : α → β → Prop} {p p' : PtrVal} {k : Outcome α} {k' : Outcome β} (hp : Refine.le p p')
    (hk : Outcome.Sim r k k') : Outcome.Sim r (IRLean.noundef p k) (IRLean.noundef p' k') := by
  cases p with
  | none => trivial
  | some q => cases hp; exact hk

/-! ### A function's promises about memory

`Mem.call` runs a function that made promises about memory inside a call of its own, and `Mem.tag` marks a pointer
argument with what the function promised of it: what the emitter wraps a function clang compiled in. Both keep the
relation, so the cut lemma reaches such a function. -/

namespace Mem

/-- Memory inside a call of a function that made promises about memory: one more running call. -/
def enterCall (m : Mem) (e : Effects) (tracked : Bool) : Mem :=
  { m with
    calls := { id := m.nextCall, effects := e, start := m.next, tracked } :: m.calls
    nextCall := m.nextCall + 1 }

/-- What `Mem.call` does once its body returns: the call is over, and what `initializes` covers and nothing wrote is
uninitialized again. -/
def endCall (x : α × Mem) : Outcome (α × Mem) :=
  match x.2.calls with
  | [] => Outcome.ok (x.1, x.2)
  | c :: rest =>
    let cleared := fun b i =>
      if c.ranges.any (fun (b', s, n) => b == b' && decide (s ≤ i) && decide (i < s + n)) && !c.initialized b i
      then Byte.uninit
      else match x.2.allocs b with
        | some a => a.bytes i
        | none => .uninit
    Outcome.ok (x.1, { x.2 with
      calls := rest
      allocs := fun b =>
        match c.ranges.any (fun (b', _, _) => b == b'), x.2.allocs b with
        | true, some a => some { a with bytes := cleared b }
        | _, y => y })

/-- `Mem.call` is its body, inside the call, and then the call's end. -/
theorem call_eq (m : Mem) (e : Effects) (tracked : Bool) (k : Mem → Nat → Outcome (α × Mem)) :
    m.call e tracked k = andThen (k (m.enterCall e tracked) m.nextCall) endCall := rfl

end Mem

namespace Mem.le

variable {m m' : Mem}

/-- A pointer argument's tag: the same tag on both sides. -/
theorem tag (t : Tag) {p p' : PtrVal} (hp : Refine.le p p') : Refine.le (Mem.tag t p) (Mem.tag t p') := by
  cases p with
  | none => trivial
  | some q => cases hp; exact Refine.Reflexive.refl _

theorem enterCall (h : Mem.le m m') (e : Effects) (tracked : Bool) :
    Mem.le (m.enterCall e tracked) (m'.enterCall e tracked) where
  allocs := h.allocs
  next := h.next
  base := h.base
  frame := h.frame
  failAlloc := h.failAlloc
  calls := .cons ⟨h.nextCall, rfl, h.next, rfl, rfl, fun _ _ hw => hw, fun _ _ => rfl⟩ h.calls
  nextCall := congrArg (· + 1) h.nextCall

/-- The end of a call keeps the relation: what goes back to uninitialized does on both sides. -/
theorem endCall {r : α → β → Prop} {x : α × Mem} {y : β × Mem} (hxy : r x.1 y.1) (hn : Mem.le x.2 y.2) :
    Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (Mem.endCall x) (Mem.endCall y) := by
  obtain ⟨x, n⟩ := x
  obtain ⟨y, n'⟩ := y
  have hn : Mem.le n n' := hn
  have hcalls := hn.calls
  simp only [Mem.endCall]
  cases hc : n.calls with
  | nil =>
    rw [hc] at hcalls
    rw [forall₂_nil_left hcalls]
    exact Outcome.Sim.ok ⟨hxy, hn⟩
  | cons c rest =>
    rw [hc] at hcalls
    obtain ⟨c', rest', hc', hcc, hrest⟩ := forall₂_cons_left hcalls
    rw [hc']
    refine Outcome.Sim.ok ⟨hxy, ?_⟩
    exact
      { allocs := fun b => by
          simp only [hcc.ranges]
          have ha := hn.allocs b
          revert ha
          generalize n.allocs b = u
          generalize n'.allocs b = u'
          intro ha
          cases ha with
          | none => cases c.ranges.any fun x => b == x.1 <;> exact .none
          | some hle =>
            cases c.ranges.any fun x => b == x.1 with
            | false => exact .some hle
            | true =>
              refine .some ⟨hle.size, hle.readonly, hle.heap, hle.stack, fun i => ?_⟩
              simp only [hcc.initialized]
              split
              · exact Byte.le.refl _
              · exact hle.bytes i
        next := hn.next
        base := hn.base
        frame := hn.frame
        failAlloc := hn.failAlloc
        calls := hrest
        nextCall := hn.nextCall }

/-- **A call of a function that made promises about memory keeps the relation:** related bodies, started on related
memories inside the call, leave related memories once it's over. Both sides give the call the same number. -/
theorem call (h : Mem.le m m') (e : Effects) (tracked : Bool) {r : α → β → Prop}
    {k : Mem → Nat → Outcome (α × Mem)} {k' : Mem → Nat → Outcome (β × Mem)}
    (hk : ∀ n n' id, Mem.le n n' → Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (k n id) (k' n' id)) :
    Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (m.call e tracked k) (m'.call e tracked k') := by
  rw [Mem.call_eq, Mem.call_eq, h.nextCall]
  exact Outcome.Sim.andThen (hk _ _ _ (h.enterCall e tracked)) fun x y hxy => endCall hxy.1 hxy.2

end Mem.le

/-- The same, where both sides start on the same memory: the bodies are compared on the one memory inside the call,
which is what a function's own claim needs, since both sides are given the same memory. -/
theorem Mono.call (m : Mem) (e : Effects) (tracked : Bool) {r : α → β → Prop}
    {k : Mem → Nat → Outcome (α × Mem)} {k' : Mem → Nat → Outcome (β × Mem)}
    (hk : Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (k (m.enterCall e tracked) m.nextCall)
      (k' (m.enterCall e tracked) m.nextCall)) :
    Outcome.Sim (fun x y => r x.1 y.1 ∧ Mem.le x.2 y.2) (m.call e tracked k) (m.call e tracked k') := by
  rw [Mem.call_eq, Mem.call_eq]
  exact Outcome.Sim.andThen hk fun x y hxy => Mem.le.endCall hxy.1 hxy.2

/-! ### Where the model has an answer

A claim with `Outcome.answered` covers the memories the source doesn't stop the model on. These say that's every
memory no running call restricts, for a store: a store can be undefined there, and can't stop the model. -/

namespace Mem

variable {m : Mem} {w : Nat}

/-- Where no running call restricts memory, a check never stops the model: it allows the access, or it's undefined. -/
theorem check_ne_model (hu : m.Unrestricted) (q : Ptr) (a : Alloc) (wr : Bool) (s : ModelStop) :
    m.check q a wr ≠ some (.model s) := by
  cases ht : q.tags.findSome? (m.tagRule wr) with
  | some e =>
    obtain ⟨t, _, he⟩ := List.exists_of_findSome?_eq_some ht
    simp only [check, ht, ne_eq, Option.some.injEq]
    rintro rfl
    simp only [tagRule] at he
    split at he
    · split at he
      · cases he
      · split at he <;> cases he
    · split at he <;> cases he
  | none =>
    rw [check_of_unrestricted hu fun t ht' => List.findSome?_eq_none_iff.mp ht t ht']
    nofun

/-- So a store never stops the model there. -/
theorem storeInt_ne_stop (hu : m.Unrestricted) (p : PtrVal) (v : Val w) (align : Nat) (s : ModelStop) :
    m.storeInt p v align ≠ Outcome.stop s := by
  rw [storeInt_eq]
  cases m.access p (w / 8) align with
  | error e => nofun
  | ok qa =>
    obtain ⟨q, a⟩ := qa
    simp only
    split
    · nofun
    · have := check_ne_model hu q a true s
      revert this
      cases m.check q a true with
      | none => intro _; nofun
      | some e => intro h h'; exact h (by simpa [Outcome.stop] using h')

/-- A store leaves no call restricting memory, where none did. -/
theorem unrestricted_write (hu : m.Unrestricted) (q : Ptr) (a : Alloc) (n : Nat) (f : Nat → Byte) :
    (m.write q a n f).Unrestricted := by
  intro c hc
  rw [write_calls hu] at hc
  exact hu c hc

theorem unrestricted_storeInt (hu : m.Unrestricted) {p : PtrVal} {v : Val w} {align : Nat} {m₁ : Mem}
    (h : m.storeInt p v align = Outcome.ok m₁) : m₁.Unrestricted := by
  obtain ⟨q, a, _, _, _, _, rfl⟩ := storeInt_ok h
  exact unrestricted_write hu q a _ _

end Mem

/-- A function with no memory, as one with: it returns the memory it was given. A claim relating a function the
emitter gave a `Mem` to one it didn't lifts the second with this, as `Outcomes.det` does for choices. -/
@[llvm] def Mem.lift (o : Outcome α) (m : Mem) : Outcome (α × Mem) := andThen o fun r => Outcome.ok (r, m)

end IRLean
