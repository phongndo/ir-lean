import store_overwritten_right_ir
import store_forwarded_right_ir
import load_repeated_right_ir
import stored_value_refined_right_ir
import store_removed_wrong_ir
import stores_swapped_wrong_ir
import load_added_wrong_ir
import store_added_wrong_ir
import alloca_removed_no_claim_ir

/-! `Refines` for functions with memory, SEM-06, on what ir-lean emits: each rewrite in `tests/memory_refine`, with a
theorem of the case's name proving its verdict. A `_right` case refines, on every memory the model has an answer for,
and a `_wrong` one provably doesn't, at the pointer, values and memory given. `tests/memory_refine.sh` builds this
with warnings as errors, checks it rests on the standard axioms, replays it, and has Alive2 give each case's verdict
too.

**A claim says `Outcome.answered`.** A load or a store checks the promises of the calls that are running, and stops
the model where LangRef leaves one open, and `Mem` ranges over memories with any calls running. So no function that
touches memory refines itself on every memory, and a claim says where the source has an answer:
`Refines (fun p a m => (src p a m).answered) tgt`. `store_overwritten_right_answers` and
`store_forwarded_right_answers` say that isn't a small set: it's at least every memory no running call restricts.

**A target that allocates differently has no claim yet.** `alloca_removed_no_claim` is a rewrite that's right in LLVM
and that this relation doesn't hold of. Its theorem is about the relation, and a tool mustn't read it as a
counterexample. -/

open IRLean

namespace MemoryRefine

/-! ### Right -/

/-- Removing a store that's overwritten before anything reads it: `Mem.storeInt_overwritten`. -/
theorem store_overwritten_right :
    Refines (fun p a b m => (store_overwritten_right_ir.src p a b m).answered) store_overwritten_right_ir.tgt := by
  intro p a b m
  rw [Refine.answered_iff]
  simp only [store_overwritten_right_ir.src, store_overwritten_right_ir.tgt, run_eq,
    store_overwritten_right_ir.src.step, store_overwritten_right_ir.tgt.step, andThen_assoc, andThen_ret_run]
  rw [← andThen_assoc]
  exact Outcome.Sim.andThen (Mem.storeInt_overwritten m p a b 4) fun m₁ m₂ h => Outcome.Sim.ok ⟨trivial, h⟩

/-- The guard isn't hiding much: where no running call restricts memory, the source has an answer. -/
theorem store_overwritten_right_answers (p : PtrVal) (a b : Val 32) (m : Mem) (hu : m.Unrestricted) (s : ModelStop) :
    store_overwritten_right_ir.src p a b m ≠ Outcome.stop s := by
  simp only [store_overwritten_right_ir.src, run_eq, store_overwritten_right_ir.src.step, andThen_assoc,
    andThen_ret_run]
  refine andThen_ne_stop_of (Mem.storeInt_ne_stop hu p a 4 s) fun m₁ h₁ => ?_
  exact andThen_ne_stop (Mem.storeInt_ne_stop (Mem.unrestricted_storeInt hu h₁) p b 4 s) fun _ => nofun

/-- Forwarding a store to the load after it: `Mem.loadInt_of_storeInt`. -/
theorem store_forwarded_right :
    Refines (fun p a m => (store_forwarded_right_ir.src p a m).answered) store_forwarded_right_ir.tgt := by
  intro p a m
  rw [Refine.answered_iff]
  simp only [store_forwarded_right_ir.src, store_forwarded_right_ir.tgt, run_eq,
    store_forwarded_right_ir.src.step, store_forwarded_right_ir.tgt.step, andThen_assoc, andThen_ret_run]
  rcases Mem.storeInt_error_or_ok m p a 4 with ⟨e, he⟩ | ⟨m₁, h₁⟩
  · rw [he]; trivial
  · rw [h₁, andThen_ok, andThen_ok]
    rcases Mem.loadInt_of_storeInt h₁ (by decide) (by decide) with hl | ⟨e, hl⟩
    · rw [hl, andThen_ok]
      exact Outcome.Sim.ok ⟨Refine.refl_val a, Mem.le.refl m₁⟩
    · rw [hl]; trivial

/-- Where no running call restricts memory, the source has an answer: the load reads what the store wrote. -/
theorem store_forwarded_right_answers (p : PtrVal) (a : Val 32) (m : Mem) (hu : m.Unrestricted) (s : ModelStop) :
    store_forwarded_right_ir.src p a m ≠ Outcome.stop s := by
  simp only [store_forwarded_right_ir.src, run_eq, store_forwarded_right_ir.src.step, andThen_assoc,
    andThen_ret_run]
  refine andThen_ne_stop_of (Mem.storeInt_ne_stop hu p a 4 s) fun m₁ h₁ => ?_
  obtain ⟨q, a₀, rfl, hacc, _, _, rfl⟩ := Mem.storeInt_ok h₁
  rw [Mem.loadInt_write_self hacc (by decide) (by decide)]
  have hc := Mem.check_ne_model hu q a₀ false s
  revert hc
  cases m.check q a₀ false with
  | none => intro _; nofun
  | some e => intro hc h; exact hc (by simpa [andThen, Outcome.stop] using h)

/-- Two loads of the same bytes, to one: the memory is the same at both, so they give the same. -/
theorem load_repeated_right :
    Refines (fun p m => (load_repeated_right_ir.src p m).answered) load_repeated_right_ir.tgt := by
  intro p m
  rw [Refine.answered_iff]
  simp only [load_repeated_right_ir.src, load_repeated_right_ir.tgt, run_eq, load_repeated_right_ir.src.step,
    load_repeated_right_ir.tgt.step, andThen_assoc, andThen_ret_run]
  match m.loadInt 32 p 4 with
  | none => exact rfl
  | some (.error _) => trivial
  | some (.ok x) => exact Outcome.Sim.ok ⟨Refine.refl_val _, Mem.le.refl m⟩

/-- Storing a value where the source stored poison: the bytes written differ, and the source's allow the target's.
`Mem.le.storeInt`. -/
theorem stored_value_refined_right :
    Refines (fun p a m => (stored_value_refined_right_ir.src p a m).answered) stored_value_refined_right_ir.tgt := by
  intro p a m
  rw [Refine.answered_iff]
  simp only [stored_value_refined_right_ir.src, stored_value_refined_right_ir.tgt, run_eq,
    stored_value_refined_right_ir.src.step, stored_value_refined_right_ir.tgt.step, andThen_assoc, andThen_ret_run]
  refine Outcome.Sim.andThen (r := Refine.le)
    ((Mem.le.refl m).storeInt (Refine.Reflexive.refl p) ?_ 4) fun m₁ m₂ h => Outcome.Sim.ok ⟨trivial, h⟩
  cases a with
  | none => exact Refine.val_none _
  | some x =>
    simp only [Val.add]
    split
    · exact Refine.val_none _
    · simp [Refine.val_some]

/-! ### Wrong

Each is refuted at one input: a memory with one allocation and no call running, or with none. The source has an
answer there, so the guard doesn't excuse it. -/

/-- Four writable bytes, each zero. -/
def zeros : Alloc := { size := 4, readonly := false, bytes := fun _ => .val 0#8 }

/-- A memory with one allocation, number 1: `zeros`, at an address that's a multiple of 4, with no call running. -/
def cell : Mem :=
  { allocs := fun b => if b == 1 then some zeros else none
    next := 2, base := fun _ => 4096#64, frame := [] }

/-- The pointer to its first byte, with no tags. -/
def at1 : Ptr := ⟨1, 0#64, []⟩

theorem access_cell : cell.access (some at1) 4 4 = .ok (at1, zeros) :=
  Mem.access_ok_iff.2 ⟨rfl, rfl, by decide, .inr (by decide)⟩

theorem check_cell (wr : Bool) : cell.check at1 zeros wr = none := rfl

/-- A store to the cell returns, having written the value's bytes. -/
theorem store_cell (v : Val 32) :
    cell.storeInt (some at1) v 4 = Outcome.ok (cell.write at1 zeros 4 (Mem.intBytes v)) := by
  simp only [Mem.storeInt_eq, show (32 / 8) = 4 from rfl, access_cell, check_cell]
  rfl

/-- A load from the cell gives 0. -/
theorem load_cell : cell.loadInt 32 (some at1) 4 = Outcome.ok (some 0#32) := by rfl

/-- Two memories that differ in a byte of a value aren't related. -/
theorem not_le_of_byte {m m' : Mem} {a a' : Alloc} {x y : BitVec 8} (ha : m.allocs 1 = some a)
    (ha' : m'.allocs 1 = some a') (hx : a.bytes 0 = .val x) (hy : a'.bytes 0 = .val y) (hxy : x ≠ y) :
    ¬ Mem.le m m' := fun h => by
  obtain ⟨b, hb, hle⟩ := h.alloc ha
  rw [ha'] at hb
  cases hb
  have := hle.bytes 0
  rw [hx, hy] at this
  cases this
  exact hxy rfl

/-- Removing a store that a load reads: from a cell of zeros, the source stores 5 and returns it, and the target
returns the 0 that was there. -/
theorem store_removed_wrong :
    ¬ Refines (fun p a m => (store_removed_wrong_ir.src p a m).answered) store_removed_wrong_ir.tgt := fun h => by
  have h := (Refine.answered_iff _ _).1 (h (some at1) (some 5#32) cell)
  simp only [store_removed_wrong_ir.src, store_removed_wrong_ir.tgt, run_eq, store_removed_wrong_ir.src.step,
    store_removed_wrong_ir.tgt.step, andThen_assoc, andThen_ret_run] at h
  rw [store_cell, andThen_ok, Mem.loadInt_write_self access_cell (by decide) (by decide), check_cell, load_cell,
    andThen_ok, andThen_ok, Outcome.Sim.ok_iff] at h
  have h₁ : (some 0#32 : Val 32) = some 5#32 := h.1
  exact absurd h₁ (by decide)

/-- Swapping two stores through pointers that may be the same: with both the cell's, the source leaves the second
value, 2, and the target the first, 1. -/
theorem stores_swapped_wrong :
    ¬ Refines (fun p q a b m => (stores_swapped_wrong_ir.src p q a b m).answered) stores_swapped_wrong_ir.tgt :=
  fun h => by
    have h := (Refine.answered_iff _ _).1 (h (some at1) (some at1) (some 1#32) (some 2#32) cell)
    simp only [stores_swapped_wrong_ir.src, stores_swapped_wrong_ir.tgt, run_eq, stores_swapped_wrong_ir.src.step,
      stores_swapped_wrong_ir.tgt.step, andThen_assoc, andThen_ret_run] at h
    rw [store_cell, store_cell, andThen_ok, andThen_ok,
      Mem.storeInt_write_self access_cell rfl (check_cell true),
      Mem.storeInt_write_self access_cell rfl (check_cell true), andThen_ok, andThen_ok,
      Outcome.Sim.ok_iff] at h
    exact not_le_of_byte (x := 2#8) (y := 1#8) (Mem.write_allocs_self _ at1 _ 4 _) (Mem.write_allocs_self _ at1 _ 4 _)
      rfl rfl (by decide) h.2

/-- Adding a load from memory the source never touched: with nothing allocated, the source returns, and the target's
load is undefined. -/
theorem load_added_wrong :
    ¬ Refines (fun p a m => (load_added_wrong_ir.src p a m).answered) load_added_wrong_ir.tgt := fun h => by
  have h := (Refine.answered_iff _ _).1 (h (some at1) (some 0#32) (Mem.empty fun _ => 0#64))
  simp only [load_added_wrong_ir.src, load_added_wrong_ir.tgt, run_eq, load_added_wrong_ir.src.step,
    load_added_wrong_ir.tgt.step, andThen_assoc, andThen_ret_run] at h
  rw [show (Mem.empty fun _ => 0#64).loadInt 32 (some at1) 4 = Outcome.ub .badAccess from rfl] at h
  obtain ⟨_, h, _⟩ := h
  cases h

/-- Adding a store: the source leaves the cell's zeros, and the target a 5. -/
theorem store_added_wrong :
    ¬ Refines (fun p a m => (store_added_wrong_ir.src p a m).answered) store_added_wrong_ir.tgt := fun h => by
  have h := (Refine.answered_iff _ _).1 (h (some at1) (some 5#32) cell)
  simp only [store_added_wrong_ir.src, store_added_wrong_ir.tgt, run_eq, store_added_wrong_ir.src.step,
    store_added_wrong_ir.tgt.step, andThen_assoc, andThen_ret_run] at h
  rw [store_cell, andThen_ok, Outcome.Sim.ok_iff] at h
  exact not_le_of_byte (m := cell) (a := zeros) (x := 0#8) (y := 5#8) rfl (Mem.write_allocs_self cell at1 zeros 4 _)
    rfl rfl (by decide) h.2

/-! ### What the relation leaves out -/

/-- An empty memory once the source has made its `alloca`: allocation 1, four uninitialized bytes on the stack. -/
def fresh : Mem :=
  { allocs := fun b =>
      if b == 1 then some { size := 4, readonly := false, bytes := fun _ => .uninit, stack := true } else none
    next := 2, base := fun _ => 0#64, frame := [1] }

theorem alloca_empty :
    Mem.alloca { Mem.empty (fun _ => 0#64) with frame := [] } (some 4#64) = Outcome.ok (some ⟨1, 0#64, []⟩, fresh) := by
  simp only [Mem.alloca, Mem.empty, fresh]
  rfl

/-- **Removing an `alloca` nothing reads isn't a refinement under this relation,** though it's right in LLVM. From an
empty memory the source numbers an allocation, 1, and frees it when it returns, so its memory says the next one is 2.
The target allocates nothing, so its says 1, and `Mem.le` asks for the same. Nothing either memory holds differs:
what differs is which number a later allocation gets, and relating two runs that number them differently takes a
renaming of allocations that this relation doesn't have. -/
theorem alloca_removed_no_claim :
    ¬ Refines (fun a m => (alloca_removed_no_claim_ir.src a m).answered)
      (fun a => Mem.lift (alloca_removed_no_claim_ir.tgt a)) := fun h => by
  have h := (Refine.answered_iff _ _).1 (h (some 0#32) (Mem.empty fun _ => 0#64))
  simp only [alloca_removed_no_claim_ir.src, alloca_removed_no_claim_ir.tgt, Mem.withFrame, Mem.lift, run_eq,
    alloca_removed_no_claim_ir.src.step, alloca_removed_no_claim_ir.tgt.step, andThen_assoc, andThen_ret_run,
    alloca_empty, andThen_ok] at h
  have hacc : fresh.access (some ⟨1, 0#64, []⟩) (32 / 8) 4 = .ok (⟨1, 0#64, []⟩, _) :=
    Mem.access_ok_iff.2 ⟨rfl, rfl, by decide, .inr (by decide)⟩
  rw [Mem.storeInt_eq, hacc] at h
  simp only [show fresh.check ⟨1, 0#64, []⟩ _ true = none from rfl, Bool.false_eq_true, ite_false, andThen_ok,
    Outcome.Sim.ok_iff] at h
  exact absurd h.2.next (by decide)

/-- The cell, inside a call of a function marked `memory(none)`: LangRef only rules out accesses seen from outside
it, which the model can't tell, so any access stops the model. -/
def restricted : Mem :=
  { cell with calls := [{ id := 1, effects := { other := .none }, start := 2, tracked := false }], nextCall := 2 }

/-- **A claim without the guard is false,** even of a right rewrite: in a memory where a running call's promise
leaves an access open, the source's store stops the model, and a source that stops the model allows nothing. That's
on purpose, and it's why a claim about memory says `Outcome.answered`. -/
theorem unguarded_claim_is_false :
    ¬ Refines store_overwritten_right_ir.src store_overwritten_right_ir.tgt := fun h => by
  have h := h (some at1) (some 1#32) (some 2#32) restricted
  simp only [store_overwritten_right_ir.src, run_eq, store_overwritten_right_ir.src.step, andThen_assoc,
    andThen_ret_run] at h
  have hacc : restricted.access (some at1) (32 / 8) 4 = .ok (at1, zeros) :=
    Mem.access_ok_iff.2 ⟨rfl, rfl, by decide, .inr (by decide)⟩
  rw [Mem.storeInt_eq, hacc] at h
  exact h

end MemoryRefine
