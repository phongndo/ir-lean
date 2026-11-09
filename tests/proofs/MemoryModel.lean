import IRLean

/-! What the memory model does with invalid accesses, for every memory. Each theorem is one kind of memory error
the model claims to catch, and names the undefined behavior it gives, so a change to `Mem` that stopped catching
one would break it. They cover bounds, lifetime, frees, null, poison, alignment and overlapping copies. Broken
promises, `memset` and `strlen` out of bounds, and stores before `llvm.lifetime.start` are tested in `ub.ll`, not
proved here. These are about `Mem` alone. `UpdateWindow.lean` shows the same catches in real compiled code,
and `tests/real/memory_errors.ll` checks them through the emitter. `docs/memory.md` lists what the model doesn't
catch. -/

open IRLean

namespace MemoryModel

variable {m m' : Mem} {p q : Ptr} {a : Alloc} {w align : Nat}

/-! ### Bounds -/

/-- Reading past the end of an allocation. -/
theorem load_past_end (ha : m.allocs q.block = some a) (h : a.size < q.offset.toNat + w / 8) :
    m.loadInt w (some q) align = Outcome.ub .badAccess := by
  simp [Mem.loadInt, Mem.access_past_end ha h, Outcome.ub]

/-- Writing past the end of an allocation. -/
theorem store_past_end (ha : m.allocs q.block = some a) (h : a.size < q.offset.toNat + w / 8) (v : Val w) :
    m.storeInt (some q) v align = Outcome.ub .badAccess := by
  simp [Mem.storeInt, Mem.access_past_end ha h, Outcome.ub]

/-- The same for a pointer. -/
theorem loadPtr_past_end (ha : m.allocs q.block = some a) (h : a.size < q.offset.toNat + 8) :
    m.loadPtr (some q) align = Outcome.ub .badAccess := by
  simp [Mem.loadPtr, Mem.access_past_end ha h, Outcome.ub]

/-- Stepping back from an allocation's start with `inbounds` gives poison. -/
theorem gep_before_start {b n : Nat} (O : m.Object b n) (t : List Tag) :
    m.gep (some ⟨b, 0#64, t⟩) (some (0#64 - 1#64)) (inbounds := true) = none :=
  O.gep_back_out (o := 0) (k := 1) (by omega) (by omega) (by omega) t

/-- Without `inbounds`, the step is allowed, but offsets are unsigned, so the pointer is near `2 ^ 64` bytes into the
allocation, and reading through it is past the end. -/
theorem load_before_start {b : Nat} {t : List Tag} (ha : m.allocs b = some a) (hs : a.size < 2 ^ 63)
    (hw : 0 < w / 8) (hw' : w / 8 < 2 ^ 63) :
    m.loadInt w (m.gep (some ⟨b, 0#64, t⟩) (some (0#64 - 1#64))) align = Outcome.ub .badAccess := by
  have e : (0#64 + (0#64 - 1#64)).toNat = 2 ^ 64 - 1 := by decide
  simp only [Mem.gep, Bool.false_and, Bool.false_eq_true, ite_false]
  exact load_past_end (q := ⟨b, 0#64 + (0#64 - 1#64), t⟩) ha (by simp only [e]; omega)

/-- Provenance: an access reaches only the allocation its pointer came from. Past the end of one allocation is
undefined in every layout, including ones that put another allocation at that address. -/
theorem past_end_any_layout (ha : m.allocs q.block = some a) (h : a.size < q.offset.toNat + w / 8)
    (base : Nat → BitVec 64) : { m with base := base }.loadInt w (some q) align = Outcome.ub .badAccess :=
  load_past_end (m := { m with base := base }) ha h

/-! ### Lifetime -/

/-- An allocation that's gone, because it was never made, was freed, or its function returned: any access through
any pointer into it is undefined. -/
theorem load_gone (ha : m.allocs q.block = none) : m.loadInt w (some q) align = Outcome.ub .badAccess := by
  simp [Mem.loadInt, Mem.access_gone ha, Outcome.ub]

theorem store_gone (ha : m.allocs q.block = none) (v : Val w) :
    m.storeInt (some q) v align = Outcome.ub .badAccess := by
  simp [Mem.storeInt, Mem.access_gone ha, Outcome.ub]

/-- Once `free` returns, the allocation is gone. -/
theorem free_gone (hf : Mem.free (some p) m = Outcome.ok ((), m')) (hp : p.block ≠ 0) :
    m'.allocs p.block = none := by
  have hn : p.same Ptr.null = false := by simp [Ptr.same, Ptr.null, hp]
  rcases hb : m.allocs p.block with _ | a
  · simp [Mem.free, hn, hb, Outcome.ub, Outcome.ok] at hf
  · by_cases hh : (a.heap && p.offset == 0#64) = true
    · by_cases hnf : (p.tags.any fun t => t.nofree && m.isRunning t.call) = true
      · simp [Mem.free, hn, hb, hh, hnf, Outcome.ub, Outcome.ok] at hf
      · simp only [Mem.free, hn, hb, hh, hnf, Bool.false_eq_true, ite_false, ite_true] at hf
        cases hc : m.check p a true <;> cases hr : m.allocatorRule false <;>
          simp only [hc, hr, Outcome.ok, reduceCtorEq, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq,
            true_and] at hf
        subst hf
        simp [Mem.setAlloc]
    · simp [Mem.free, hn, hb, hh, Outcome.ub, Outcome.ok] at hf

/-- Use after free: once `free` returns, any access through any pointer into what it freed is undefined. -/
theorem use_after_free (hf : Mem.free (some p) m = Outcome.ok ((), m')) (hp : p.block ≠ 0) (hq : q.block = p.block) :
    m'.loadInt w (some q) align = Outcome.ub .badAccess :=
  load_gone (by rw [hq]; exact free_gone hf hp)

/-- Freeing something twice. -/
theorem double_free (hf : Mem.free (some p) m = Outcome.ok ((), m')) (hp : p.block ≠ 0) :
    Mem.free (some p) m' = Outcome.ub .badFree := by
  have hn : p.same Ptr.null = false := by simp [Ptr.same, Ptr.null, hp]
  simp [Mem.free, hn, free_gone hf hp]

/-- After a function returns, its `alloca`s are gone, so a pointer to one that got out is dangling, and writing
through it is undefined. So is reading through it, in the model, where LangRef says a load from a dead stack
object gives poison: the model has more undefined behavior than LLVM here, which `docs/memory.md` lists. -/
theorem dangling_after_return {α : Type} {body : Mem → Outcome (α × Mem)} {r : α} {m1 : Mem} {b : Nat}
    (hb : body { m with frame := [] } = Outcome.ok (r, m1)) (hin : b ∈ m1.frame) :
    ∃ m2, m.withFrame body = Outcome.ok (r, m2) ∧
      (∀ (o : BitVec 64) (t : List Tag) (v : Val w), m2.storeInt (some ⟨b, o, t⟩) v align = Outcome.ub .badAccess) ∧
      ∀ (o : BitVec 64) (t : List Tag), m2.loadInt w (some ⟨b, o, t⟩) align = Outcome.ub .badAccess := by
  have hg : ({ m1 with allocs := fun b => if m1.frame.contains b then none else m1.allocs b, frame := m.frame } :
      Mem).allocs b = none := by simp [hin]
  exact ⟨_, by simp only [Mem.withFrame, hb, andThen_ok], fun o t v => store_gone hg v, fun o t => load_gone hg⟩

/-- An `alloca` is in the frame that `withFrame` clears. -/
theorem alloca_in_frame {n : BitVec 64} {dead : Bool} {r : PtrVal}
    (h : m.alloca (some n) dead = Outcome.ok (r, m')) : r = some ⟨m.next, 0#64, []⟩ ∧ m.next ∈ m'.frame := by
  simp only [Mem.alloca, Outcome.ok, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp

/-- A stack object outside its lifetime, or a constant: writing it is undefined. -/
theorem store_readonly (ha : m.allocs q.block = some a) (hin : q.offset.toNat + w / 8 ≤ a.size)
    (hal : align = 1 ∨ (m.addr q).toNat % align = 0) (hro : a.readonly = true) (x : Val w) :
    m.storeInt (some q) x align = Outcome.ub .writeToConstant := by
  simp [Mem.storeInt, Mem.access_ok ha hin hal, hro]

/-- After `llvm.lifetime.end`, writing the object is undefined. -/
theorem store_after_lifetime_end (hl : m.lifetime (some p) false = Outcome.ok m') (ha : m.allocs p.block = some a)
    (hq : q.block = p.block) (hin : q.offset.toNat + w / 8 ≤ a.size)
    (hal : align = 1 ∨ (m'.addr q).toNat % align = 0) (x : Val w) :
    m'.storeInt (some q) x align = Outcome.ub .writeToConstant := by
  simp only [Mem.lifetime, ha, Outcome.ok, Option.some.injEq, Except.ok.injEq] at hl
  subst hl
  exact store_readonly (a := { a with readonly := true, bytes := fun _ => .uninit })
    (by simp [Mem.setAlloc, hq]) hin hal rfl x

theorem collect_uninit (l : List Nat) (hl : l ≠ []) : Mem.collect (l.map fun _ => Byte.uninit) = .ok none := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp [Mem.collect]
    | cons y ys =>
      simp only [List.map_cons] at ih ⊢
      rw [Mem.collect, ih (by simp)]

/-- But reading it isn't undefined: it gives poison, as LangRef says of a stack object outside its lifetime. -/
theorem load_after_lifetime_end (hl : m.lifetime (some p) false = Outcome.ok m') (ha : m.allocs p.block = some a)
    (hq : q.block = p.block) (ht : q.tags = []) (hin : q.offset.toNat + w / 8 ≤ a.size)
    (hal : align = 1 ∨ (m'.addr q).toNat % align = 0) (hw : 0 < w / 8) :
    m'.loadInt w (some q) align = Outcome.ok none := by
  simp only [Mem.lifetime, ha, Outcome.ok, Option.some.injEq, Except.ok.injEq] at hl
  subst hl
  have ha' : (m.setAlloc p.block (some { a with readonly := !false, bytes := fun _ => .uninit })).allocs q.block =
      some { a with readonly := true, bytes := fun _ => .uninit } := by simp [Mem.setAlloc, hq]
  have hc := Mem.check_constant
    (m := m.setAlloc p.block (some { a with readonly := !false, bytes := fun _ => .uninit }))
    (a := { a with readonly := true, bytes := fun _ => .uninit }) ht rfl
  have hr : (m.setAlloc p.block (some { a with readonly := !false, bytes := fun _ => .uninit })).read q
      { a with readonly := true, bytes := fun _ => .uninit } q.offset.toNat (w / 8) =
      (List.range (w / 8)).map fun _ => Byte.uninit := by
    simp only [Mem.read, Mem.visible,
      Mem.unwritten_constant (a := { a with readonly := true, bytes := fun _ => .uninit }) rfl,
      Bool.false_eq_true, ite_false]
  have hne : List.range (w / 8) ≠ [] := by simp; omega
  simp only [Mem.loadInt, Mem.access_ok ha' hin hal, hc, hr, collect_uninit _ hne]

/-! ### Frees -/

/-- Freeing something `malloc` didn't return: a stack object or a global. -/
theorem free_not_heap (ha : m.allocs p.block = some a) (hh : a.heap = false) (hp : p.block ≠ 0) :
    Mem.free (some p) m = Outcome.ub .badFree := by
  have hn : p.same Ptr.null = false := by simp [Ptr.same, Ptr.null, hp]
  simp [Mem.free, hn, ha, hh]

/-- Freeing a pointer into the middle of an allocation. -/
theorem free_interior (ha : m.allocs p.block = some a) (ho : p.offset ≠ 0#64) (hp : p.block ≠ 0) :
    Mem.free (some p) m = Outcome.ub .badFree := by
  have hn : p.same Ptr.null = false := by simp [Ptr.same, Ptr.null, hp]
  simp [Mem.free, hn, ha, ho]

/-- Freeing null does nothing, as C says. -/
theorem free_null : Mem.free (some Ptr.null) m = Outcome.ok ((), m) := by
  simp [Mem.free, Ptr.same]

/-! ### Null, poison and alignment -/

/-- Null points to allocation 0, which `Mem.empty` doesn't have. `alloca` and `malloc` number from `next`, which starts
at 1, and the emitter numbers globals from 1, but `Mem.addGlobal` would make allocation 0 if asked, so this assumes it
isn't there. -/
theorem load_null (h0 : m.allocs 0 = none) : m.loadInt w (some Ptr.null) align = Outcome.ub .badAccess :=
  load_gone h0

theorem empty_has_no_null (base : Nat → BitVec 64) : (Mem.empty base).allocs 0 = none := rfl

/-- A poison pointer. -/
theorem load_poison : m.loadInt w none align = Outcome.ub .poisonPointer := rfl

theorem store_poison (v : Val w) : m.storeInt none v align = Outcome.ub .poisonPointer := rfl

/-- An access whose address isn't a multiple of its alignment. -/
theorem load_misaligned (ha : m.allocs q.block = some a) (hin : q.offset.toNat + w / 8 ≤ a.size) (h1 : align ≠ 1)
    (hm : (m.addr q).toNat % align ≠ 0) : m.loadInt w (some q) align = Outcome.ub .misaligned := by
  have h1' : ¬ q.offset.toNat + w / 8 > a.size := by omega
  simp [Mem.loadInt, Mem.access, ha, h1', h1, hm, Outcome.ub]

/-! ### Copies -/

/-- `llvm.memcpy` between overlapping ranges that aren't the same. -/
theorem memcpy_overlap {k da ds : Nat} {t t' : List Tag} (ha : m.allocs q.block = some a) (hk : 0 < k)
    (hk' : k < 2 ^ 63) (hd : da + k ≤ a.size) (hs : ds + k ≤ a.size) (hsz : a.size < 2 ^ 63) (hne : da ≠ ds)
    (hover : da < ds + k ∧ ds < da + k) (hw : a.readonly = false) :
    m.memcpy (some ⟨q.block, BitVec.ofNat 64 da, t⟩) (some ⟨q.block, BitVec.ofNat 64 ds, t'⟩)
      (some (BitVec.ofNat 64 k)) = Outcome.ub .overlappingCopy := by
  have tk := Mem.toNat_ofNat_of_lt hk'
  have td := Mem.toNat_ofNat_of_lt (o := da) (by omega)
  have ts := Mem.toNat_ofNat_of_lt (o := ds) (by omega)
  have hk0 : (BitVec.ofNat 64 k == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [tk, BitVec.toNat_zero] at this
    omega
  have ad := Mem.access_ok (m := m) (q := ⟨q.block, BitVec.ofNat 64 da, t⟩) (n := k) (align := 1) ha
    (by simp only [td]; omega) (.inl rfl)
  have as := Mem.access_ok (m := m) (q := ⟨q.block, BitVec.ofNat 64 ds, t'⟩) (n := k) (align := 1) ha
    (by simp only [ts]; omega) (.inl rfl)
  simp only [Mem.memcpy, hk0, tk, Bool.false_eq_true, ite_false, ad, as, hw, td, ts, beq_self_eq_true,
    Bool.true_and]
  simp [hne, hover, Outcome.ub]

end MemoryModel
