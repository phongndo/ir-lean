import Rules.Mono
import Rules.Statements
import IRLean.Generic.Arith
import IRLean.Generic.Bitwise
import Peephole.Lemmas.Add
import Peephole.Lemmas.Arith
import Peephole.Lemmas.Intrinsic
import Peephole.Lemmas.Logic
import Peephole.Lemmas.Shift

/-! # The imported rules' proofs

Written by `tools/rules/import_peephole.py`, one line a rule: the lemma the rule was read from
proves the statement `tools/rules/rules.py gen` generates for it. Do not edit:
`import_peephole.py --check` fails if this isn't what it writes. -/

namespace Rules

theorem add_of_sum : Stmt.add_of_sum := by rule_from Peephole.Lemmas.add_refines_of_sum
theorem add_sub_cancel : Stmt.add_sub_cancel := by rule_from Peephole.Lemmas.add_sub_cancel_refines
theorem add_sub_sub : Stmt.add_sub_sub := by rule_from Peephole.Lemmas.add_sub_sub_refines
theorem add_not_left : Stmt.add_not_left := by rule_from Peephole.Lemmas.add_not_left_refines
theorem add_not_right : Stmt.add_not_right := by rule_from Peephole.Lemmas.add_not_right_refines
theorem add_xor_signMask : Stmt.add_xor_signMask := by rule_from Peephole.Lemmas.add_xor_signMask_refines
theorem add_nuw_allOnes : Stmt.add_nuw_allOnes := by rule_from Peephole.Lemmas.add_nuw_allOnes_refines
theorem sub_zero_left_nuw : Stmt.sub_zero_left_nuw := by rule_from Peephole.Lemmas.sub_zero_left_nuw_refines
theorem sub_zero_left_nsw : Stmt.sub_zero_left_nsw := by rule_from Peephole.Lemmas.sub_zero_left_nsw_refines
theorem sub_zero_left_self : Stmt.sub_zero_left_self := by rule_from Peephole.Lemmas.sub_zero_left_refines_self
theorem sub_mask_xor_nuw : Stmt.sub_mask_xor_nuw := by rule_from Peephole.Lemmas.sub_mask_xor_nuw_refines
theorem mul_udiv_exact : Stmt.mul_udiv_exact := by rule_from Peephole.Lemmas.mul_udiv_exact_refines
theorem mul_sdiv_exact : Stmt.mul_sdiv_exact := by rule_from Peephole.Lemmas.mul_sdiv_exact_refines
theorem mul_nsw_one_bit : Stmt.mul_nsw_one_bit := by rule_from Peephole.Lemmas.mul_nsw_one_bit_refines
theorem udiv_self : Stmt.udiv_self := by rule_from Peephole.Lemmas.udiv_self_refines
theorem urem_self : Stmt.urem_self := by rule_from Peephole.Lemmas.urem_self_refines
theorem sdiv_self : Stmt.sdiv_self := by rule_from Peephole.Lemmas.sdiv_self_refines
theorem srem_self : Stmt.srem_self := by rule_from Peephole.Lemmas.srem_self_refines
theorem udiv_zero_left : Stmt.udiv_zero_left := by rule_from Peephole.Lemmas.udiv_zero_left_refines
theorem urem_zero_left : Stmt.urem_zero_left := by rule_from Peephole.Lemmas.urem_zero_left_refines
theorem sdiv_zero_left : Stmt.sdiv_zero_left := by rule_from Peephole.Lemmas.sdiv_zero_left_refines
theorem srem_zero_left : Stmt.srem_zero_left := by rule_from Peephole.Lemmas.srem_zero_left_refines
theorem udiv_mul_nuw : Stmt.udiv_mul_nuw := by rule_from Peephole.Lemmas.udiv_mul_nuw_refines
theorem urem_mul_nuw : Stmt.urem_mul_nuw := by rule_from Peephole.Lemmas.urem_mul_nuw_refines
theorem sdiv_mul_nsw : Stmt.sdiv_mul_nsw := by rule_from Peephole.Lemmas.sdiv_mul_nsw_refines
theorem srem_mul_nsw : Stmt.srem_mul_nsw := by rule_from Peephole.Lemmas.srem_mul_nsw_refines
theorem udiv_mul_udiv : Stmt.udiv_mul_udiv := by rule_from Peephole.Lemmas.udiv_mul_udiv_refines
theorem urem_mul_udiv : Stmt.urem_mul_udiv := by rule_from Peephole.Lemmas.urem_mul_udiv_refines
theorem sdiv_mul_sdiv : Stmt.sdiv_mul_sdiv := by rule_from Peephole.Lemmas.sdiv_mul_sdiv_refines
theorem srem_mul_sdiv : Stmt.srem_mul_sdiv := by rule_from Peephole.Lemmas.srem_mul_sdiv_refines
theorem udiv_of_lt : Stmt.udiv_of_lt := by rule_from Peephole.Lemmas.udiv_of_lt_refines
theorem urem_of_lt : Stmt.urem_of_lt := by rule_from Peephole.Lemmas.urem_of_lt_refines
theorem udiv_exact_mul_nsw : Stmt.udiv_exact_mul_nsw := by rule_from Peephole.Lemmas.udiv_exact_mul_nsw_refines
theorem sdiv_exact_mul_nuw : Stmt.sdiv_exact_mul_nuw := by rule_from Peephole.Lemmas.sdiv_exact_mul_nuw_refines
theorem urem_shl_nuw : Stmt.urem_shl_nuw := by rule_from Peephole.Lemmas.urem_shl_nuw_refines
theorem srem_shl_nsw : Stmt.srem_shl_nsw := by rule_from Peephole.Lemmas.srem_shl_nsw_refines
theorem urem_mul_nuw_of_umod : Stmt.urem_mul_nuw_of_umod := by rule_from Peephole.Lemmas.urem_mul_nuw_of_umod_refines
theorem srem_mul_nsw_of_srem : Stmt.srem_mul_nsw_of_srem := by rule_from Peephole.Lemmas.srem_mul_nsw_of_srem_refines
theorem sdiv_neg_nsw_left : Stmt.sdiv_neg_nsw_left := by rule_from Peephole.Lemmas.sdiv_neg_nsw_left_refines
theorem sdiv_neg_nsw_right : Stmt.sdiv_neg_nsw_right := by rule_from Peephole.Lemmas.sdiv_neg_nsw_right_refines
theorem sdiv_sub_nsw_swap : Stmt.sdiv_sub_nsw_swap := by rule_from Peephole.Lemmas.sdiv_sub_nsw_swap_refines
theorem srem_sext_one_bit : Stmt.srem_sext_one_bit := by rule_from Peephole.Lemmas.srem_sext_one_bit_refines
theorem srem_neg_left : Stmt.srem_neg_left := by rule_from Peephole.Lemmas.srem_neg_left_refines
theorem srem_neg_right : Stmt.srem_neg_right := by rule_from Peephole.Lemmas.srem_neg_right_refines
theorem srem_sub_swap : Stmt.srem_sub_swap := by rule_from Peephole.Lemmas.srem_sub_swap_refines
theorem cttz_shl_one : Stmt.cttz_shl_one := by rule_from Peephole.Lemmas.cttz_shl_one_refines
theorem ctlz_lshr_negative : Stmt.ctlz_lshr_negative := by rule_from Peephole.Lemmas.ctlz_lshr_negative_refines
theorem ctlz_ashr_negative : Stmt.ctlz_ashr_negative := by rule_from Peephole.Lemmas.ctlz_ashr_negative_refines
theorem ctpop_of_isPowerOfTwo : Stmt.ctpop_of_isPowerOfTwo := by rule_from_eq Peephole.Lemmas.ctpop_of_isPowerOfTwo
theorem abs_abs : Stmt.abs_abs := by rule_from Peephole.Lemmas.abs_abs_refines
theorem bitreverse_bitreverse : Stmt.bitreverse_bitreverse := by rule_from_eq Peephole.Lemmas.bitreverse_bitreverse
theorem umax_self : Stmt.umax_self := by rule_from_eq Peephole.Lemmas.umax_self
theorem umin_self : Stmt.umin_self := by rule_from_eq Peephole.Lemmas.umin_self
theorem smax_self : Stmt.smax_self := by rule_from_eq Peephole.Lemmas.smax_self
theorem smin_self : Stmt.smin_self := by rule_from_eq Peephole.Lemmas.smin_self
theorem umax_comm : Stmt.umax_comm := by rule_from_eq Peephole.Lemmas.umax_comm
theorem umin_comm : Stmt.umin_comm := by rule_from_eq Peephole.Lemmas.umin_comm
theorem smax_comm : Stmt.smax_comm := by rule_from_eq Peephole.Lemmas.smax_comm
theorem smin_comm : Stmt.smin_comm := by rule_from_eq Peephole.Lemmas.smin_comm
theorem umax_allOnes : Stmt.umax_allOnes := by rule_from Peephole.Lemmas.umax_allOnes_refines
theorem umin_zero : Stmt.umin_zero := by rule_from Peephole.Lemmas.umin_zero_refines
theorem smax_intMax : Stmt.smax_intMax := by rule_from Peephole.Lemmas.smax_intMax_refines
theorem smin_intMin : Stmt.smin_intMin := by rule_from Peephole.Lemmas.smin_intMin_refines
theorem umax_zero : Stmt.umax_zero := by rule_from_eq Peephole.Lemmas.umax_zero
theorem umin_allOnes : Stmt.umin_allOnes := by rule_from_eq Peephole.Lemmas.umin_allOnes
theorem smax_intMin : Stmt.smax_intMin := by rule_from_eq Peephole.Lemmas.smax_intMin
theorem smin_intMax : Stmt.smin_intMax := by rule_from_eq Peephole.Lemmas.smin_intMax
theorem umax_umax_of_ule : Stmt.umax_umax_of_ule := by rule_from_eq Peephole.Lemmas.umax_umax_of_ule
theorem umin_umin_of_ule : Stmt.umin_umin_of_ule := by rule_from_eq Peephole.Lemmas.umin_umin_of_ule
theorem smax_smax_of_sle : Stmt.smax_smax_of_sle := by rule_from_eq Peephole.Lemmas.smax_smax_of_sle
theorem smin_smin_of_sle : Stmt.smin_smin_of_sle := by rule_from_eq Peephole.Lemmas.smin_smin_of_sle
theorem umax_umax_left : Stmt.umax_umax_left := by rule_from_eq Peephole.Lemmas.umax_umax_left
theorem umax_umax_right : Stmt.umax_umax_right := by rule_from_eq Peephole.Lemmas.umax_umax_right
theorem umin_umin_left : Stmt.umin_umin_left := by rule_from_eq Peephole.Lemmas.umin_umin_left
theorem umin_umin_right : Stmt.umin_umin_right := by rule_from_eq Peephole.Lemmas.umin_umin_right
theorem smax_smax_left : Stmt.smax_smax_left := by rule_from_eq Peephole.Lemmas.smax_smax_left
theorem smax_smax_right : Stmt.smax_smax_right := by rule_from_eq Peephole.Lemmas.smax_smax_right
theorem smin_smin_left : Stmt.smin_smin_left := by rule_from_eq Peephole.Lemmas.smin_smin_left
theorem smin_smin_right : Stmt.smin_smin_right := by rule_from_eq Peephole.Lemmas.smin_smin_right
theorem umax_umin_left : Stmt.umax_umin_left := by rule_from Peephole.Lemmas.umax_umin_left_refines
theorem umax_umin_right : Stmt.umax_umin_right := by rule_from Peephole.Lemmas.umax_umin_right_refines
theorem umin_umax_left : Stmt.umin_umax_left := by rule_from Peephole.Lemmas.umin_umax_left_refines
theorem umin_umax_right : Stmt.umin_umax_right := by rule_from Peephole.Lemmas.umin_umax_right_refines
theorem smax_smin_left : Stmt.smax_smin_left := by rule_from Peephole.Lemmas.smax_smin_left_refines
theorem smax_smin_right : Stmt.smax_smin_right := by rule_from Peephole.Lemmas.smax_smin_right_refines
theorem smin_smax_left : Stmt.smin_smax_left := by rule_from Peephole.Lemmas.smin_smax_left_refines
theorem smin_smax_right : Stmt.smin_smax_right := by rule_from Peephole.Lemmas.smin_smax_right_refines
theorem umax_some_of_ule : Stmt.umax_some_of_ule := by rule_from_eq Peephole.Lemmas.umax_some_of_ule
theorem umin_some_of_ule : Stmt.umin_some_of_ule := by rule_from_eq Peephole.Lemmas.umin_some_of_ule
theorem smax_some_of_sle : Stmt.smax_some_of_sle := by rule_from_eq Peephole.Lemmas.smax_some_of_sle
theorem smin_some_of_sle : Stmt.smin_some_of_sle := by rule_from_eq Peephole.Lemmas.smin_some_of_sle
theorem uaddSat_allOnes_left : Stmt.uaddSat_allOnes_left := by rule_from Peephole.Lemmas.uaddSat_allOnes_left_refines
theorem uaddSat_allOnes_right : Stmt.uaddSat_allOnes_right := by rule_from Peephole.Lemmas.uaddSat_allOnes_right_refines
theorem uaddSat_zero : Stmt.uaddSat_zero := by rule_from_eq Peephole.Lemmas.uaddSat_zero
theorem zero_uaddSat : Stmt.zero_uaddSat := by rule_from_eq Peephole.Lemmas.zero_uaddSat
theorem saddSat_zero : Stmt.saddSat_zero := by rule_from_eq Peephole.Lemmas.saddSat_zero
theorem zero_saddSat : Stmt.zero_saddSat := by rule_from_eq Peephole.Lemmas.zero_saddSat
theorem zero_usubSat : Stmt.zero_usubSat := by rule_from Peephole.Lemmas.zero_usubSat_refines
theorem usubSat_allOnes : Stmt.usubSat_allOnes := by rule_from Peephole.Lemmas.usubSat_allOnes_refines
theorem usubSat_self : Stmt.usubSat_self := by rule_from Peephole.Lemmas.usubSat_self_refines
theorem ssubSat_self : Stmt.ssubSat_self := by rule_from Peephole.Lemmas.ssubSat_self_refines
theorem usubSat_zero : Stmt.usubSat_zero := by rule_from_eq Peephole.Lemmas.usubSat_zero
theorem ssubSat_zero : Stmt.ssubSat_zero := by rule_from_eq Peephole.Lemmas.ssubSat_zero
theorem fshl_zero_zero : Stmt.fshl_zero_zero := by rule_from Peephole.Lemmas.fshl_zero_zero_refines
theorem fshr_zero_zero : Stmt.fshr_zero_zero := by rule_from Peephole.Lemmas.fshr_zero_zero_refines
theorem fshl_allOnes_allOnes : Stmt.fshl_allOnes_allOnes := by rule_from Peephole.Lemmas.fshl_allOnes_allOnes_refines
theorem fshr_allOnes_allOnes : Stmt.fshr_allOnes_allOnes := by rule_from Peephole.Lemmas.fshr_allOnes_allOnes_refines
theorem and_some : Stmt.and_some := by rule_from_eq Peephole.Lemmas.Logic.and_some
theorem xor_some : Stmt.xor_some := by rule_from_eq Peephole.Lemmas.Logic.xor_some
theorem and_comm : Stmt.and_comm := by rule_from_eq Peephole.Lemmas.Logic.and_comm
theorem xor_comm : Stmt.xor_comm := by rule_from_eq Peephole.Lemmas.Logic.xor_comm
theorem and_not_self : Stmt.and_not_self := by rule_from Peephole.Lemmas.and_not_self_refines
theorem and_or_not_or : Stmt.and_or_not_or := by rule_from Peephole.Lemmas.and_or_not_or_refines
theorem and_xor_or_xor_or : Stmt.and_xor_or_xor_or := by rule_from Peephole.Lemmas.and_xor_or_xor_or_refines
theorem and_xor_xor_not : Stmt.and_xor_xor_not := by rule_from Peephole.Lemmas.and_xor_xor_not_refines
theorem and_add_sub_not : Stmt.and_add_sub_not := by rule_from Peephole.Lemmas.and_add_sub_not_refines
theorem or_add_sub_not : Stmt.or_add_sub_not := by rule_from Peephole.Lemmas.or_add_sub_not_refines
theorem xor_add_sub_not : Stmt.xor_add_sub_not := by rule_from Peephole.Lemmas.xor_add_sub_not_refines
theorem and_select : Stmt.and_select := by rule_from Peephole.Lemmas.and_select_refines
theorem or_select : Stmt.or_select := by rule_from Peephole.Lemmas.or_select_refines
theorem or_not_self : Stmt.or_not_self := by rule_from Peephole.Lemmas.or_not_self_refines
theorem or_not_and : Stmt.or_not_and := by rule_from Peephole.Lemmas.or_not_and_refines
theorem or_and_absorb : Stmt.or_and_absorb := by rule_from Peephole.Lemmas.or_and_absorb_refines
theorem or_xor_or : Stmt.or_xor_or := by rule_from Peephole.Lemmas.or_xor_or_refines
theorem or_not_xor_or : Stmt.or_not_xor_or := by rule_from Peephole.Lemmas.or_not_xor_or_refines
theorem or_and_not_xor : Stmt.or_and_not_xor := by rule_from Peephole.Lemmas.or_and_not_xor_refines
theorem or_xor_not_and : Stmt.or_xor_not_and := by rule_from Peephole.Lemmas.or_xor_not_and_refines
theorem or_or_not_xor : Stmt.or_or_not_xor := by rule_from Peephole.Lemmas.or_or_not_xor_refines
theorem or_and_not_not_or : Stmt.or_and_not_not_or := by rule_from Peephole.Lemmas.or_and_not_not_or_refines
theorem or_not_xor_and : Stmt.or_not_xor_and := by rule_from Peephole.Lemmas.or_not_xor_and_refines
theorem or_not_and_xor : Stmt.or_not_and_xor := by rule_from Peephole.Lemmas.or_not_and_xor_refines
theorem or_fshl_shl : Stmt.or_fshl_shl := by rule_from Peephole.Lemmas.or_fshl_shl_refines
theorem or_fshr_lshr : Stmt.or_fshr_lshr := by rule_from Peephole.Lemmas.or_fshr_lshr_refines
theorem or_xor_xor_not : Stmt.or_xor_xor_not := by rule_from Peephole.Lemmas.or_xor_xor_not_refines
theorem xor_not_self : Stmt.xor_not_self := by rule_from Peephole.Lemmas.xor_not_self_refines
theorem xor_and_not_or : Stmt.xor_and_not_or := by rule_from Peephole.Lemmas.xor_and_not_or_refines
theorem xor_or_not_and : Stmt.xor_or_not_and := by rule_from Peephole.Lemmas.xor_or_not_and_refines
theorem xor_sub_nuw_lowMask : Stmt.xor_sub_nuw_lowMask := by rule_from Peephole.Lemmas.xor_sub_nuw_lowMask_refines
theorem shl_zero_left : Stmt.shl_zero_left := by rule_from Peephole.Lemmas.shl_zero_left_refines
theorem lshr_zero_left : Stmt.lshr_zero_left := by rule_from Peephole.Lemmas.lshr_zero_left_refines
theorem ashr_zero_left : Stmt.ashr_zero_left := by rule_from Peephole.Lemmas.ashr_zero_left_refines
theorem lshr_self : Stmt.lshr_self := by rule_from Peephole.Lemmas.lshr_self_refines
theorem ashr_self : Stmt.ashr_self := by rule_from Peephole.Lemmas.ashr_self_refines
theorem lshr_exact_of_getLsbD : Stmt.lshr_exact_of_getLsbD := by rule_from Peephole.Lemmas.lshr_exact_of_getLsbD_refines
theorem ashr_exact_of_getLsbD : Stmt.ashr_exact_of_getLsbD := by rule_from Peephole.Lemmas.ashr_exact_of_getLsbD_refines
theorem shl_nuw_of_msb : Stmt.shl_nuw_of_msb := by rule_from Peephole.Lemmas.shl_nuw_of_msb_refines
theorem ashr_allOnes : Stmt.ashr_allOnes := by rule_from Peephole.Lemmas.ashr_allOnes_refines
theorem ashr_shl_allOnes : Stmt.ashr_shl_allOnes := by rule_from Peephole.Lemmas.ashr_shl_allOnes_refines
theorem trunc_zext : Stmt.trunc_zext := by rule_from Peephole.Lemmas.trunc_zext_refines
theorem trunc_sext : Stmt.trunc_sext := by rule_from Peephole.Lemmas.trunc_sext_refines
theorem zext_trunc_nuw : Stmt.zext_trunc_nuw := by rule_from Peephole.Lemmas.zext_trunc_nuw_refines
theorem sext_trunc_nsw : Stmt.sext_trunc_nsw := by rule_from Peephole.Lemmas.sext_trunc_nsw_refines
theorem add_zero : Stmt.add_zero := by rule_from_eq IRLean.Generic.add_zero
theorem sub_zero : Stmt.sub_zero := by rule_from_eq IRLean.Generic.sub_zero
theorem mul_one : Stmt.mul_one := by rule_from IRLean.Generic.mul_one_refines
theorem sub_self : Stmt.sub_self := by rule_from IRLean.Generic.sub_self_refines
theorem mul_zero : Stmt.mul_zero := by rule_from IRLean.Generic.mul_zero_refines
theorem or_disjoint_add : Stmt.or_disjoint_add := by rule_from IRLean.Generic.or_disjoint_refines_add
theorem udiv_one : Stmt.udiv_one := by rule_from_eq IRLean.Generic.udiv_one
theorem urem_one : Stmt.urem_one := by rule_from IRLean.Generic.urem_one_refines
theorem sdiv_one : Stmt.sdiv_one := by rule_from_eq IRLean.Generic.sdiv_one
theorem sdiv_one_refines : Stmt.sdiv_one_refines := by rule_from IRLean.Generic.sdiv_one_refines
theorem srem_one : Stmt.srem_one := by rule_from IRLean.Generic.srem_one_refines
theorem and_self : Stmt.and_self := by rule_from_eq IRLean.Generic.and_self
theorem or_self_disjoint : Stmt.or_self_disjoint := by rule_from IRLean.Generic.or_self_disjoint_refines
theorem xor_self : Stmt.xor_self := by rule_from IRLean.Generic.xor_self_refines
theorem and_allOnes : Stmt.and_allOnes := by rule_from_eq IRLean.Generic.and_allOnes
theorem or_zero : Stmt.or_zero := by rule_from_eq IRLean.Generic.or_zero
theorem xor_zero : Stmt.xor_zero := by rule_from_eq IRLean.Generic.xor_zero
theorem and_zero : Stmt.and_zero := by rule_from IRLean.Generic.and_zero_refines
theorem or_allOnes : Stmt.or_allOnes := by rule_from IRLean.Generic.or_allOnes_refines
theorem not_and : Stmt.not_and := by rule_from_eq IRLean.Generic.not_and
theorem not_or : Stmt.not_or := by rule_from IRLean.Generic.not_or_refines
theorem xor_xor_cancel : Stmt.xor_xor_cancel := by rule_from IRLean.Generic.xor_xor_cancel_refines
theorem and_or_absorb : Stmt.and_or_absorb := by rule_from IRLean.Generic.and_or_absorb_refines
theorem shl_zero : Stmt.shl_zero := by rule_from_eq IRLean.Generic.shl_zero
theorem lshr_zero : Stmt.lshr_zero := by rule_from_eq IRLean.Generic.lshr_zero
theorem ashr_zero : Stmt.ashr_zero := by rule_from_eq IRLean.Generic.ashr_zero
theorem lshr_shl_nuw : Stmt.lshr_shl_nuw := by rule_from IRLean.Generic.lshr_shl_nuw_refines
theorem ashr_shl_nsw : Stmt.ashr_shl_nsw := by rule_from IRLean.Generic.ashr_shl_nsw_refines
theorem shl_lshr_exact : Stmt.shl_lshr_exact := by rule_from IRLean.Generic.shl_lshr_exact_refines
theorem shl_ashr_exact : Stmt.shl_ashr_exact := by rule_from IRLean.Generic.shl_ashr_exact_refines

end Rules
