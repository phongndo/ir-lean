import IRLean.LLVMHeap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! A heap built byte by byte that meets `IRLean.LLVMHeap.View`, so its hypotheses can hold: the type `i8`, the
`ConstantInt` 0 of it, an argument, and `sub i8 0, %arg`. Then `ConstantInt::get(i8, 7)`, done as the specification
says, keeps the view and adds 7. `tests/llvm_heap.sh` checks this with warnings as errors. -/

set_option linter.unusedSimpArgs false

namespace LLVMHeapExample

open IRLean IRLean.LLVMHeap

/-- The type `i8`: its word at offset 8, its ID 12 with the width 8 above. -/
def tyAlloc : Alloc :=
  { size := 24, readonly := false,
    bytes := fun j => if 8 ≤ j ∧ j < 12 then Mem.intByte (intTypeWord 8) (j - 8) else .uninit }

/-- The `ConstantInt` 0 of type `i8`. -/
def zeroAlloc : Alloc :=
  { size := 40, readonly := false,
    bytes := fun j =>
      if j = 0 then .val 5#8
      else if 8 ≤ j ∧ j < 16 then .ptr (ptrOf (1, 0)) (j - 8)
      else if 24 ≤ j ∧ j < 32 then Mem.intByte (0#64) (j - 24)
      else if 32 ≤ j ∧ j < 36 then Mem.intByte (8#32) (j - 32)
      else .uninit }

/-- An argument of type `i8`, value ID 23. -/
def argAlloc : Alloc :=
  { size := 24, readonly := false,
    bytes := fun j => if j = 0 then .val 23#8 else if 8 ≤ j ∧ j < 16 then .ptr (ptrOf (1, 0)) (j - 8) else .uninit }

/-- `sub i8 0, %arg`: two `Use`s, then the object at 64, value ID 46. -/
def subAlloc : Alloc :=
  { size := 136, readonly := false,
    bytes := fun j =>
      if j < 8 then .ptr (ptrOf (2, 0)) j
      else if 32 ≤ j ∧ j < 40 then .ptr (ptrOf (3, 0)) (j - 32)
      else if j = 64 then .val 46#8
      else if 72 ≤ j ∧ j < 80 then .ptr (ptrOf (1, 0)) (j - 72)
      else .uninit }

def heap : Mem :=
  { allocs := fun b =>
      if b = 1 then some tyAlloc else if b = 2 then some zeroAlloc else if b = 3 then some argAlloc
      else if b = 4 then some subAlloc else none
    next := 5
    base := fun b => BitVec.ofNat 64 (b * 4096)
    frame := [] }

def graph : Graph where
  objs l :=
    if l = (2, 0) then some (.constInt 8 0#8, (1, 0))
    else if l = (3, 0) then some (.other 23, (1, 0))
    else if l = (4, 64) then some (.binOp .sub (2, 0) (3, 0), (1, 0))
    else none
  tys l := if l = (1, 0) then some (.int 8) else none

theorem placed (b : Nat) (a : Alloc) (h : heap.allocs b = some a) (h0 : b ≠ 0) (hb : b < 5) (hs : a.size ≤ 136) :
    Placed heap b a := by
  refine ⟨h, h0, ?_, ?_, ?_, by omega⟩ <;> simp [heap, BitVec.toNat_ofNat] <;> omega

theorem objs_cases {l : Loc} {e : Obj × Loc} (h : graph.objs l = some e) :
    (l = (2, 0) ∧ e = (.constInt 8 0#8, (1, 0))) ∨ (l = (3, 0) ∧ e = (.other 23, (1, 0))) ∨
      (l = (4, 64) ∧ e = (.binOp .sub (2, 0) (3, 0), (1, 0))) := by
  simp only [graph] at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · split at h
      · simp_all
      · cases h

theorem tys_cases {t : Loc} {ty : Ty} (h : graph.tys t = some ty) : t = (1, 0) ∧ ty = .int 8 := by
  simp only [graph] at h
  split at h <;> simp_all

theorem view : View heap graph where
  objs l e h := by
    rcases objs_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨zeroAlloc, placed 2 _ (by simp [heap]) (by decide) (by decide) (by decide), by decide,
        by simp [Obj.hi, zeroAlloc], by simp [zeroAlloc, Obj.id], fun i hi => ?_, by decide, by decide,
        fun i hi => ?_, fun i hi => ?_⟩
      · simp [zeroAlloc, show 8 + i ≠ 0 by omega, show 8 + i < 16 by omega]
      · simp [zeroAlloc, show 24 + i ≠ 0 by omega, show ¬ (8 ≤ 24 + i ∧ 24 + i < 16) by omega,
          show 24 + i < 32 by omega]
      · simp [zeroAlloc, show 32 + i ≠ 0 by omega, show ¬ (8 ≤ 32 + i ∧ 32 + i < 16) by omega,
          show ¬ (24 ≤ 32 + i ∧ 32 + i < 32) by omega, show 32 + i < 36 by omega]
    · refine ⟨argAlloc, placed 3 _ (by simp [heap]) (by decide) (by decide) (by decide), by decide,
        by simp [Obj.hi, argAlloc], by simp [argAlloc, Obj.id], fun i hi => ?_, by simp [Obj.bytes]; llvm_layout; omega⟩
      simp [argAlloc, show 8 + i ≠ 0 by omega, show 8 + i < 16 by omega]
    · refine ⟨subAlloc, placed 4 _ (by simp [heap]) (by decide) (by decide) (by decide), by decide,
        by simp [Obj.hi, subAlloc]; llvm_layout; omega, by simp [subAlloc, Obj.id, BinOp.opcode], fun i hi => ?_,
        by decide, fun i hi => ?_, fun i hi => ?_⟩ <;> llvm_layout
      · simp [subAlloc, show ¬ 72 + i < 8 by omega, show ¬ (32 ≤ 72 + i ∧ 72 + i < 40) by omega,
          show 72 + i ≠ 64 by omega, show 72 + i < 80 by omega]
      · simp [subAlloc, hi]
      · simp [subAlloc, show ¬ 32 + i < 8 by omega, show 32 + i < 40 by omega]
  tys t ty h := by
    obtain ⟨rfl, rfl⟩ := tys_cases h
    refine ⟨tyAlloc, placed 1 _ (by simp [heap]) (by decide) (by decide) (by decide), by decide,
      by simp [tyAlloc], by decide, by decide, fun i hi => ?_⟩
    simp [tyAlloc, show 8 + i < 12 by omega]
  typed l e h := by rcases objs_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [graph]
  ints l w v t h := by
    rcases objs_cases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all [graph]
  operands l op x y t h := by
    rcases objs_cases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all [graph]
  one l := by
    by_cases h : l = (1, 0)
    · left; subst h; simp [graph]
    · right; simp [graph, h]
  apart l lo hi l' lo' hi' hs hs' hne hb := by
    have blk : ∀ l lo hi, graph.Spans l lo hi → l = (1, 0) ∨ l = (2, 0) ∨ l = (3, 0) ∨ l = (4, 64) := by
      rintro l lo hi (⟨e, he, -, -⟩ | ⟨ty, ht, -, -⟩)
      · rcases objs_cases he with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      · obtain ⟨rfl, -⟩ := tys_cases ht; simp
    rcases blk l lo hi hs with rfl | rfl | rfl | rfl <;> rcases blk l' lo' hi' hs' with rfl | rfl | rfl | rfl <;>
      simp_all
  distinct l e l' e' h h' ha := by
    rcases objs_cases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      rcases objs_cases h' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all [Mem.addr, heap] <;> contradiction
  calls := rfl

/-- `ConstantInt::get(i8, 7)`, as the specification says it acts: a new allocation, 5, holding the constant. -/
def sevenAlloc : Alloc :=
  { size := 40, readonly := false,
    bytes := fun j =>
      if j = 0 then .val 5#8
      else if 8 ≤ j ∧ j < 16 then .ptr (ptrOf (1, 0)) (j - 8)
      else if 24 ≤ j ∧ j < 32 then Mem.intByte (7#64) (j - 24)
      else if 32 ≤ j ∧ j < 36 then Mem.intByte (8#32) (j - 32)
      else .uninit }

def heap' : Mem := { heap with allocs := fun b => if b = 5 then some sevenAlloc else heap.allocs b, next := 6 }

theorem get_seven : ConstantIntGet graph heap heap' (fun _ => False) (1, 0) 8 7#64 (5, 0) where
  keeps := ⟨fun b a h => ⟨a, by simp [heap', show b ≠ 5 by rintro rfl; simp [heap] at h, h], rfl, fun _ _ => rfl⟩,
    rfl, rfl⟩
  made := by
    refine ⟨sevenAlloc, ⟨by simp [heap'], by decide, ?_, ?_, ?_, by decide⟩, by decide, by simp [sevenAlloc],
      by simp [sevenAlloc], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · simp [heap', heap, BitVec.toNat_ofNat]
    · simp [heap', heap, BitVec.toNat_ofNat]
    · simp [heap', heap, sevenAlloc, BitVec.toNat_ofNat]
    · simp [sevenAlloc, show 8 + i < 16 by omega]
    · simp [sevenAlloc, show ¬ (8 ≤ 24 + i ∧ 24 + i < 16) by omega, show 24 + i < 32 by omega]
    · simp [sevenAlloc, show ¬ (8 ≤ 32 + i ∧ 32 + i < 16) by omega, show ¬ (24 ≤ 32 + i ∧ 32 + i < 32) by omega,
        show 32 + i < 36 by omega]
  found_or_alone := by
    refine .inr fun l lo hi hs => ?_
    rcases hs with ⟨e, he, -, -⟩ | ⟨ty, ht, -, -⟩
    · rcases objs_cases he with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    · obtain ⟨rfl, -⟩ := tys_cases ht; simp
  addr _ l e h := by
    rcases objs_cases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Mem.addr, heap', heap]

/-- So the view of the heap after it holds 7 too. -/
theorem view' : View heap' (graph.addObj (5, 0) (.constInt 8 ((7#64).setWidth 8), (1, 0))) :=
  view.constantIntGet get_seven (fun _ _ _ h => h) (by simp [graph]) (by decide) (by decide) (by decide)

/-- And `ConstantInt::get(i1, 7)` as the pinned release build does it, with the word 7, is no `ConstantInt` the
view describes, whatever its value. -/
theorem dirty (a : Alloc) (h : IntAt a 24 (7#64) 8) (v : BitVec 1) : ¬ IntAt a 24 (v.setWidth 64) 8 :=
  dirty_not_constInt (by decide) h v

end LLVMHeapExample

/-! Every theorem above and the library's own rest on the standard axioms only. -/

open Lean Elab Command in
run_cmd do
  let names := [``IRLean.LLVMHeap.View.keep, ``IRLean.LLVMHeap.View.constantIntGet,
    ``IRLean.LLVMHeap.View.poisonGet, ``IRLean.LLVMHeap.View.binOpCreate, ``IRLean.LLVMHeap.View.load_id,
    ``IRLean.LLVMHeap.View.load_type, ``IRLean.LLVMHeap.View.load_word, ``IRLean.LLVMHeap.View.load_width,
    ``IRLean.LLVMHeap.View.load_op0, ``IRLean.LLVMHeap.View.load_op1, ``IRLean.LLVMHeap.View.load_intType,
    ``IRLean.LLVMHeap.dirty_not_constInt, ``LLVMHeapExample.view, ``LLVMHeapExample.view', ``LLVMHeapExample.dirty]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    if let some a := axs.find? (![``propext, ``Classical.choice, ``Quot.sound].contains ·) then
      throwError "{n} rests on {a}"
