import bitcast_fneg_right_ir
import copysign_dropped_wrong_ir
import copysign_fabs_sign_right_ir
import fabs_fneg_right_ir
import fcmp_fabs_olt_zero_right_ir
import fcmp_fneg_both_right_ir
import fcmp_oeq_negzero_right_ir
import fcmp_oeq_self_true_wrong_ir
import fcmp_oeq_zero_to_icmp_wrong_ir
import fcmp_olt_to_ult_wrong_ir
import fcmp_swap_right_ir
import fcmp_uno_self_right_ir
import fcmp_uno_to_fpclass_right_ir
import fneg_fneg_right_ir
import fneg_nnan_added_wrong_ir
import fneg_nnan_dropped_right_ir
import fpclass_snan_wrong_ir
import select_zero_wrong_ir

import fadd_negzero_right_ir
import fmul_one_right_ir
import fdiv_two_right_ir
import fsub_negzero_to_fneg_right_ir
import fadd_comm_right_ir
import fpext_fptrunc_right_ir
import sitofp_fptosi_right_ir
import fadd_zero_wrong_ir
import fneg_to_fsub_wrong_ir
import fmul_zero_wrong_ir
import fdiv_self_wrong_ir
import fadd_fsub_wrong_ir
import fptosi_narrowed_wrong_ir
import uitofp_nneg_added_wrong_ir

import fadd_nsz_zero_right_ir
import fsub_nsz_zero_to_fneg_right_ir
import fneg_nsz_dropped_right_ir
import select_nsz_zero_right_ir
import fneg_nsz_added_wrong_ir
import select_nnan_arm_wrong_ir
import select_nnan_added_wrong_ir
import fabs_nsz_negzero_wrong_ir
/-! Floating point's bit-level operations in the model, SEM-05's first slice: each rewrite in `tests/float`, as ir-lean
emits it, with a theorem of the case's name proving its verdict. A `_right` case refines, for every input, poison
included, and a `_wrong` one provably doesn't, at the input given. `tests/float.sh` builds this with warnings as
errors, checks its axioms, replays it, and has Alive2 give each case's verdict too. See `docs/float.md`.

Each proof unfolds both functions with `simp`, which reads `IRLean/Float.lean` through the `llvm` set, and closes what's
left with `bv_decide`, for each argument poison or a value. `simp [llvm]` leaves the arithmetic's circuits whole, which
`bv_decide` unfolds itself.

A function with an operation that can give a NaN returns `Outcomes`, an outcome for each way it chooses, and one with
none returns `Outcome`, which a claim lifts with `Outcomes.det`. A right rewrite whose source chooses names the
source's choice, as a function of the inputs and of the target's choice: `keep x` returns `x` unchanged where it's a
NaN, and `swapPick` takes a NaN from the other operand. A wrong one is refuted for every way the source chooses. -/

open IRLean

-- Every proof unfolds with the same set, whatever each one needs of it.
set_option linter.unusedSimpArgs false

/-- Moves `some` out of an `if`, so that what `simp` leaves of a result is about bit vectors, which `bv_decide` reads. -/
theorem ite_some {α : Type} {c : Prop} [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

/-- The NaN choice that returns the first operand unchanged, with its own sign: `FP.nan3`'s bits 1 and 2. -/
def keep (x : Val w) : Nat :=
  match x with
  | some v => ((BitVec.ofBool v.msb).setWidth 8 ||| 6#8).toNat
  | none => 0

/-- The NaN choice that returns the second operand unchanged, with the first operand's sign flipped. -/
def flipSecond (x : Val w) : Nat :=
  match x with
  | some v => ((BitVec.ofBool !v.msb).setWidth 8 ||| 10#8).toNat
  | none => 0

/-- The choice `k` with the two operands of a binary operation swapped. Its third operand is its second, so 3 names the
second operand too. -/
def swapBV (k : BitVec 8) : BitVec 8 :=
  (k &&& ~~~12#8) |||
    (if k.extractLsb' 2 2 == 1#2 then 8#8 else if k.extractLsb' 2 2 == 0#2 then 0#8 else 4#8)

def swapPick (n : Nat) : Nat := (swapBV (BitVec.ofNat 8 n)).toNat

/-! What the choices are as the bits `FP` reads, so that `bv_decide` sees bit vectors. -/

theorem ofNat_keep (v : BitVec w) : BitVec.ofNat 8 (keep (some v)) = (BitVec.ofBool v.msb).setWidth 8 ||| 6#8 := by
  simp only [keep]; cases v.msb <;> decide

theorem ofNat_flipSecond (v : BitVec w) :
    BitVec.ofNat 8 (flipSecond (some v)) = (BitVec.ofBool !v.msb).setWidth 8 ||| 10#8 := by
  simp only [flipSecond]; cases v.msb <;> decide

theorem ofNat_swapPick (n : Nat) : BitVec.ofNat 8 (swapPick n) = swapBV (BitVec.ofNat 8 n) := by
  simp [swapPick]

/-! Under `nsz`, bit `4 + i` of the choice flips operand `i`'s sign where it's a zero, and on `select` bit 4 the
result's. -/

/-- `keep`, with the second operand's sign flipped where it's a zero. -/
def keepNsz (x : Val w) : Nat :=
  match x with
  | some v => ((BitVec.ofBool v.msb).setWidth 8 ||| 38#8).toNat
  | none => 0

/-- `flipSecond`, with the first operand's sign flipped where it's a zero. -/
def flipSecondNsz (x : Val w) : Nat :=
  match x with
  | some v => ((BitVec.ofBool !v.msb).setWidth 8 ||| 26#8).toNat
  | none => 0

/-- A zero result with `x`'s sign. -/
def zeroSign (x : Val w) : Nat :=
  match x with
  | some v => ((BitVec.ofBool v.msb).setWidth 8 <<< 4).toNat
  | none => 0

theorem ofNat_keepNsz (v : BitVec w) :
    BitVec.ofNat 8 (keepNsz (some v)) = (BitVec.ofBool v.msb).setWidth 8 ||| 38#8 := by
  simp only [keepNsz]; cases v.msb <;> decide

theorem ofNat_flipSecondNsz (v : BitVec w) :
    BitVec.ofNat 8 (flipSecondNsz (some v)) = (BitVec.ofBool !v.msb).setWidth 8 ||| 26#8 := by
  simp only [flipSecondNsz]; cases v.msb <;> decide

theorem ofNat_zeroSign (v : BitVec w) :
    BitVec.ofNat 8 (zeroSign (some v)) = (BitVec.ofBool v.msb).setWidth 8 <<< 4 := by
  simp only [zeroSign]; cases v.msb <;> decide

/-! ### Right -/

/-- `bitcast (fneg x)` to `xor (bitcast x), sign`: fneg flips the sign bit and keeps every NaN as it was. -/
theorem bitcast_fneg_right : Refines bitcast_fneg_right_ir.src bitcast_fneg_right_ir.tgt := by
  intro x0
  simp only [bitcast_fneg_right_ir.src, bitcast_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `copysign(x, fabs y)` to `fabs x`: the sign it copies is clear. -/
theorem copysign_fabs_sign_right : Refines copysign_fabs_sign_right_ir.src copysign_fabs_sign_right_ir.tgt := by
  intro x0 x1
  simp only [copysign_fabs_sign_right_ir.src, copysign_fabs_sign_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> cases x1 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fabs (fneg x)` to `fabs x`, as fabs.ll folds it. -/
theorem fabs_fneg_right : Refines fabs_fneg_right_ir.src fabs_fneg_right_ir.tgt := by
  intro x0
  simp only [fabs_fneg_right_ir.src, fabs_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt (fabs x), 0.0` to `false`: no magnitude is below zero. -/
theorem fcmp_fabs_olt_zero_right : Refines fcmp_fabs_olt_zero_right_ir.src fcmp_fabs_olt_zero_right_ir.tgt := by
  intro x0
  simp only [fcmp_fabs_olt_zero_right_ir.src, fcmp_fabs_olt_zero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt (fneg x), (fneg y)` to `fcmp ogt x, y`, as fcmp.ll folds it, NaNs and zeros included. -/
theorem fcmp_fneg_both_right : Refines fcmp_fneg_both_right_ir.src fcmp_fneg_both_right_ir.tgt := by
  intro x0 x1
  simp only [fcmp_fneg_both_right_ir.src, fcmp_fneg_both_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> cases x1 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp oeq x, -0.0` to `fcmp oeq x, 0.0`: zeros of either sign are equal. -/
theorem fcmp_oeq_negzero_right : Refines fcmp_oeq_negzero_right_ir.src fcmp_oeq_negzero_right_ir.tgt := by
  intro x0
  simp only [fcmp_oeq_negzero_right_ir.src, fcmp_oeq_negzero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp olt 1.0, x` to `fcmp ogt x, 1.0`, the constant moved right, as InstCombine canonicalizes. -/
theorem fcmp_swap_right : Refines fcmp_swap_right_ir.src fcmp_swap_right_ir.tgt := by
  intro x0
  simp only [fcmp_swap_right_ir.src, fcmp_swap_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp uno x, x` to `fcmp uno x, 0.0`, as InstCombine canonicalizes: both say whether x is a NaN. -/
theorem fcmp_uno_self_right : Refines fcmp_uno_self_right_ir.src fcmp_uno_self_right_ir.tgt := by
  intro x0
  simp only [fcmp_uno_self_right_ir.src, fcmp_uno_self_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fcmp uno x, 0.0` to `is.fpclass(x, nan)`, where 3 names both kinds of NaN. -/
theorem fcmp_uno_to_fpclass_right : Refines fcmp_uno_to_fpclass_right_ir.src fcmp_uno_to_fpclass_right_ir.tgt := by
  intro x0
  simp only [fcmp_uno_to_fpclass_right_ir.src, fcmp_uno_to_fpclass_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fneg (fneg x)` to `x`, as InstCombine's fneg.ll folds it: both flip the sign bit and nothing else. -/
theorem fneg_fneg_right : Refines fneg_fneg_right_ir.src fneg_fneg_right_ir.tgt := by
  intro x0
  simp only [fneg_fneg_right_ir.src, fneg_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fneg nnan x` to `fneg x`: dropping a flag only takes poison away. -/
theorem fneg_nnan_dropped_right : Refines fneg_nnan_dropped_right_ir.src fneg_nnan_dropped_right_ir.tgt := by
  intro x0
  simp only [fneg_nnan_dropped_right_ir.src, fneg_nnan_dropped_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x0 <;> simp [llvm, ite_some, HasPoison.poison] <;> bv_decide

/-- `fadd x, -0.0` to `x`, as InstSimplify folds it: where x is a NaN, the source may return it unchanged. -/
theorem fadd_negzero_right : Refines fadd_negzero_right_ir.src
    (fun x => Outcomes.det (fadd_negzero_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => keep x, ?_⟩
  simp only [fadd_negzero_right_ir.src, fadd_negzero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-- `fmul x, 1.0` to `x`, NaNs and subnormals included. -/
theorem fmul_one_right : Refines fmul_one_right_ir.src
    (fun x => Outcomes.det (fmul_one_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => keep x, ?_⟩
  simp only [fmul_one_right_ir.src, fmul_one_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-- `fsub -0.0, x` to `fneg x`, as InstCombine folds it: where x is a NaN, the source may return it unchanged with its
sign flipped. -/
theorem fsub_negzero_to_fneg_right : Refines fsub_negzero_to_fneg_right_ir.src
    (fun x => Outcomes.det (fsub_negzero_to_fneg_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => flipSecond x, ?_⟩
  simp only [fsub_negzero_to_fneg_right_ir.src, fsub_negzero_to_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-- `fptrunc (fpext x)` to `x`: widening is exact, and a NaN payload comes back as it went. -/
theorem fpext_fptrunc_right : Refines fpext_fptrunc_right_ir.src
    (fun x => Outcomes.det (fpext_fptrunc_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => keep x, ?_⟩
  simp only [fpext_fptrunc_right_ir.src, fpext_fptrunc_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-- `fdiv x, 2.0` to `fmul x, 0.5`: both choose the same. -/
theorem fdiv_two_right : Refines fdiv_two_right_ir.src fdiv_two_right_ir.tgt := by
  intro x
  refine Refine.outcomes_of_same fun c => ?_
  simp only [fdiv_two_right_ir.src, fdiv_two_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-- `fadd x, y` to `fadd y, x`: where the target takes a NaN from one operand, the source takes it from the other. -/
theorem fadd_comm_right : Refines fadd_comm_right_ir.src fadd_comm_right_ir.tgt := by
  intro x y ct
  refine ⟨fun p => swapPick (ct p), ?_⟩
  simp only [fadd_comm_right_ir.src, fadd_comm_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> cases y <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide (config := { timeout := 120 })

/-- `fptosi (sitofp x)` to `x` for an i16, which a float holds exactly. -/
theorem sitofp_fptosi_right : Refines sitofp_fptosi_right_ir.src sitofp_fptosi_right_ir.tgt := by
  intro x
  simp only [sitofp_fptosi_right_ir.src, sitofp_fptosi_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] <;> bv_decide

/-! #### Fast-math flags -/

/-- `fadd nsz x, 0.0` to `x`: the source may flip the 0.0 to -0.0, and keep a NaN x as it is. -/
theorem fadd_nsz_zero_right : Refines fadd_nsz_zero_right_ir.src
    (fun x => Outcomes.det (fadd_nsz_zero_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => keepNsz x, ?_⟩
  simp only [fadd_nsz_zero_right_ir.src, fadd_nsz_zero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keepNsz] <;> bv_decide

/-- `fsub nsz 0.0, x` to `fneg x`: the source may flip the 0.0 to -0.0, and return a NaN x with its sign flipped. -/
theorem fsub_nsz_zero_to_fneg_right : Refines fsub_nsz_zero_to_fneg_right_ir.src
    (fun x => Outcomes.det (fsub_nsz_zero_to_fneg_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => flipSecondNsz x, ?_⟩
  simp only [fsub_nsz_zero_to_fneg_right_ir.src, fsub_nsz_zero_to_fneg_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_flipSecondNsz] <;> bv_decide

/-- `fneg nsz x` to `fneg x`: the source may leave every zero's sign as it is. -/
theorem fneg_nsz_dropped_right : Refines fneg_nsz_dropped_right_ir.src
    (fun x => Outcomes.det (fneg_nsz_dropped_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => 0, ?_⟩
  simp only [fneg_nsz_dropped_right_ir.src, fneg_nsz_dropped_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick] <;> bv_decide

/-- `select nsz (fcmp oeq x, 0.0), 0.0, x` to `x`: where x is -0.0, the source may give -0.0. -/
theorem select_nsz_zero_right : Refines select_nsz_zero_right_ir.src
    (fun x => Outcomes.det (select_nsz_zero_right_ir.tgt x)) := by
  intro x
  refine (Refine.outcomes_det_right _ _).2 ⟨fun _ => zeroSign x, ?_⟩
  simp only [select_nsz_zero_right_ir.src, select_nsz_zero_right_ir.tgt]
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff]
  cases x <;> simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_zeroSign] <;> bv_decide

/-! ### Wrong -/

/-- `copysign(x, y)` to `x`: the sign comes from y. -/
theorem copysign_dropped_wrong : ¬ Refines copysign_dropped_wrong_ir.src copysign_dropped_wrong_ir.tgt := fun h => by
  have hc := h (some 0x3C00#16) (some 0x8000#16)
  simp only [copysign_dropped_wrong_ir.src, copysign_dropped_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp oeq x, x` to `true`: a NaN isn't equal to itself. -/
theorem fcmp_oeq_self_true_wrong : ¬ Refines fcmp_oeq_self_true_wrong_ir.src fcmp_oeq_self_true_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FF8000000000000#64)
  simp only [fcmp_oeq_self_true_wrong_ir.src, fcmp_oeq_self_true_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp oeq x, 0.0` to `icmp eq (bitcast x), 0`: -0.0 equals 0.0, but its bits are not zero. -/
theorem fcmp_oeq_zero_to_icmp_wrong : ¬ Refines fcmp_oeq_zero_to_icmp_wrong_ir.src fcmp_oeq_zero_to_icmp_wrong_ir.tgt := fun h => by
  have hc := h (some 0x80000000#32)
  simp only [fcmp_oeq_zero_to_icmp_wrong_ir.src, fcmp_oeq_zero_to_icmp_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fcmp olt x, y` to `fcmp ult x, y`: at a NaN the source is false and the target true. -/
theorem fcmp_olt_to_ult_wrong : ¬ Refines fcmp_olt_to_ult_wrong_ir.src fcmp_olt_to_ult_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32) (some 0#32)
  simp only [fcmp_olt_to_ult_wrong_ir.src, fcmp_olt_to_ult_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fneg x` to `fneg nnan x`: the target is poison at a NaN, where the source has a value. -/
theorem fneg_nnan_added_wrong : ¬ Refines fneg_nnan_added_wrong_ir.src fneg_nnan_added_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32)
  simp only [fneg_nnan_added_wrong_ir.src, fneg_nnan_added_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `is.fpclass(x, snan)` to `fcmp uno x, 0.0`: a quiet NaN is unordered but not signaling. -/
theorem fpclass_snan_wrong : ¬ Refines fpclass_snan_wrong_ir.src fpclass_snan_wrong_ir.tgt := fun h => by
  have hc := h (some 0x7FC00000#32)
  simp only [fpclass_snan_wrong_ir.src, fpclass_snan_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `select (fcmp oeq x, 0.0), 0.0, x` to `x`: at -0.0 the source gives 0.0 and the target -0.0. -/
theorem select_zero_wrong : ¬ Refines select_zero_wrong_ir.src select_zero_wrong_ir.tgt := fun h => by
  have hc := h (some 0x80000000#32)
  simp only [select_zero_wrong_ir.src, select_zero_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fadd x, 0.0` to `x`: -0.0 + 0.0 is 0.0, not -0.0. -/
theorem fadd_zero_wrong : ¬ Refines fadd_zero_wrong_ir.src
    (fun x0 => Outcomes.det (fadd_zero_wrong_ir.tgt x0)) := fun h => by
  obtain ⟨cs, hc⟩ := (Refine.outcomes_det_right _ _).1 (h (some 0x80000000#32))
  simp only [fadd_zero_wrong_ir.src, fadd_zero_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-- `fmul x, 0.0` to `0.0`: -1.0 times 0.0 is -0.0. -/
theorem fmul_zero_wrong : ¬ Refines fmul_zero_wrong_ir.src
    (fun x0 => Outcomes.det (fmul_zero_wrong_ir.tgt x0)) := fun h => by
  obtain ⟨cs, hc⟩ := (Refine.outcomes_det_right _ _).1 (h (some 0xBC00#16))
  simp only [fmul_zero_wrong_ir.src, fmul_zero_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-- `fdiv x, x` to `1.0`: 0.0 / 0.0 is a NaN. -/
theorem fdiv_self_wrong : ¬ Refines fdiv_self_wrong_ir.src
    (fun x0 => Outcomes.det (fdiv_self_wrong_ir.tgt x0)) := fun h => by
  obtain ⟨cs, hc⟩ := (Refine.outcomes_det_right _ _).1 (h (some 0#32))
  simp only [fdiv_self_wrong_ir.src, fdiv_self_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-- `fsub (fadd x, y), y` to `x`: 1.0 + 2^24 rounds to 2^24 in a float, and taking 2^24 away leaves 0.0. -/
theorem fadd_fsub_wrong : ¬ Refines fadd_fsub_wrong_ir.src
    (fun x0 x1 => Outcomes.det (fadd_fsub_wrong_ir.tgt x0 x1)) := fun h => by
  obtain ⟨cs, hc⟩ := (Refine.outcomes_det_right _ _).1 (h (some 0x3F800000#32) (some 0x4B800000#32))
  simp only [fadd_fsub_wrong_ir.src, fadd_fsub_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-- `fneg x` to `fsub -0.0, x`: where x is a NaN, the target may return the preferred NaN, and the source keeps x's The target chooses the preferred NaN. -/
theorem fneg_to_fsub_wrong : ¬ Refines (fun x => Outcomes.det (fneg_to_fsub_wrong_ir.src x))
    fneg_to_fsub_wrong_ir.tgt := fun h => by
  have hc := (Refine.outcomes_det_left _ _).1 (h (some 0x7FC00001#32)) (fun _ => 0)
  simp only [fneg_to_fsub_wrong_ir.src, fneg_to_fsub_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-- `trunc (fptosi x to i32) to i8` to `fptosi x to i8`: 200.0 doesn't fit in an i8, so the target is poison. -/
theorem fptosi_narrowed_wrong : ¬ Refines fptosi_narrowed_wrong_ir.src fptosi_narrowed_wrong_ir.tgt := fun h => by
  have hc := h (some 0x43480000#32)
  simp only [fptosi_narrowed_wrong_ir.src, fptosi_narrowed_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals (revert hc; decide)

/-- `uitofp x` to `uitofp nneg x`: the target is poison where x's sign bit is set. -/
theorem uitofp_nneg_added_wrong : ¬ Refines uitofp_nneg_added_wrong_ir.src uitofp_nneg_added_wrong_ir.tgt := fun h => by
  have hc := h (some 0xFFFFFFFF#32)
  simp only [uitofp_nneg_added_wrong_ir.src, uitofp_nneg_added_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick, ofNat_keep, ofNat_flipSecond, ofNat_swapPick, swapBV] at hc
  all_goals bv_decide

/-! #### Fast-math flags -/

/-- `fneg x` to `fneg nsz x`: at 0.0 the target may give 0.0, where the source gives -0.0. -/
theorem fneg_nsz_added_wrong : ¬ Refines (fun x0 => Outcomes.det (fneg_nsz_added_wrong_ir.src x0))
    fneg_nsz_added_wrong_ir.tgt := fun h => by
  have hc := (Refine.outcomes_det_left _ _).1 (h (some 0#32)) (fun _ => 16)
  simp only [fneg_nsz_added_wrong_ir.src, fneg_nsz_added_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison, Choice.pick] at hc
  all_goals (revert hc; decide)

/-- `select nnan c, x, NaN` to poison: where c is true and x is 1.0, the source gives 1.0. -/
theorem select_nnan_arm_wrong : ¬ Refines select_nnan_arm_wrong_ir.src select_nnan_arm_wrong_ir.tgt := fun h => by
  have hc := h (some 1#1) (some 0x3F800000#32)
  simp only [select_nnan_arm_wrong_ir.src, select_nnan_arm_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `select c, x, y` to `select nnan c, x, y`: where it selects a NaN, the target is poison and the source isn't. -/
theorem select_nnan_added_wrong : ¬ Refines select_nnan_added_wrong_ir.src select_nnan_added_wrong_ir.tgt :=
    fun h => by
  have hc := h (some 1#1) (some 0x7FC00000#32) (some 0#32)
  simp only [select_nnan_added_wrong_ir.src, select_nnan_added_wrong_ir.tgt] at hc
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at hc
  simp [llvm, ite_some, HasPoison.poison] at hc
  all_goals (revert hc; decide)

/-- `fabs nsz -0.0` to `-0.0`, as InstSimplify folds it for `fp128`, reading `nsz` as reaching the result's sign:
LangRef lets it flip only the operand's, and `fabs` of either zero is 0.0. Alive2 agrees. -/
theorem fabs_nsz_negzero_wrong : ¬ Refines fabs_nsz_negzero_wrong_ir.src fabs_nsz_negzero_wrong_ir.tgt := fun h => by
  simp only [Refines, fabs_nsz_negzero_wrong_ir.src, fabs_nsz_negzero_wrong_ir.tgt] at h
  rw [run_ret _ (by rfl), run_ret _ (by rfl), Refine.outcome_ok_ok, Refine.val_iff] at h
  simp [llvm, ite_some, HasPoison.poison] at h
  all_goals (revert h; decide)
