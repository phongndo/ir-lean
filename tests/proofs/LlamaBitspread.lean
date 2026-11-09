import LlamaBitspreadIR

/-! A local certificate for the integer bit-spreading slice in llama.cpp's q5_0 dot product.
`tests/llama-bitspread.sh` regenerates the imported module from the exact LLVM fixture, audits every
axiom, and checks that using the wrong bit makes the proof fail. No float, memory, inference, matcher,
or backend correctness is claimed here. -/

open IRLean
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace LlamaBitspread

/-- The actual optimized integer DAG and its replacement agree, including poison input. -/
theorem same (x : Val 32) : LlamaBitspreadIR.src x = LlamaBitspreadIR.tgt x := by
  unfold LlamaBitspreadIR.src
  rw [run]
  simp only [LlamaBitspreadIR.src.step, ret, Outcome.ok]
  unfold LlamaBitspreadIR.tgt
  rw [run]
  simp only [LlamaBitspreadIR.tgt.step, ret, Outcome.ok]
  apply congrArg some
  apply congrArg Except.ok
  apply Vector.ext
  intro i hi
  have hidx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
  rcases hidx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;>
    cases x <;>
      simp [Vec.map2, Vec.split, Vec.lane, Vec.insert, Vec.shuffle, Vec.select,
        IRLean.select, Val.or, Val.icmpEq, Val.icmp, HasPoison.poison,
        Vector.getElem_set] <;> congr 1 <;> bv_decide

/-- Both executions return successfully, with identical values in all lanes. -/
theorem same_successful (x : Val 32) :
    ∃ r : Vec 32 8, LlamaBitspreadIR.src x = Outcome.ok r ∧ LlamaBitspreadIR.tgt x = Outcome.ok r := by
  have hs : ∃ r : Vec 32 8, LlamaBitspreadIR.src x = Outcome.ok r := by
    unfold LlamaBitspreadIR.src
    rw [run]
    exact ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hs
  exact ⟨r, hr, (same x).symm.trans hr⟩

private theorem select_byte (b : Bool) : IRLean.select (some (BitVec.ofBool b)) (some 0#8) (some 240#8) =
    some (if b then 0#8 else 240#8) := by
  cases b <;> rfl

private theorem cast_lane (x : BitVec 32) (i : Nat) (hi : i < 32) :
    (Vec.split 32 1 32 #v[some x])[i] = some (BitVec.ofBool (x.getLsbD i)) := by
  simp [Vec.split, Vec.lane, Nat.mod_eq_of_lt hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : j = 0 := by omega
  subst this
  simp

private theorem target_result (x : Val 32) : LlamaBitspreadIR.tgt x =
    Outcome.ok (Vec.select (Vec.split 32 1 32 #v[x])
      (Vector.replicate 32 (some 0#8)) (Vector.replicate 32 (some 240#8))) := by
  unfold LlamaBitspreadIR.tgt
  rw [run]
  rfl

def expected (x : BitVec 32) : Vec 32 8 :=
  Vector.ofFn fun i => some (if x.getLsbD i.val then 0#8 else 240#8)

theorem target_defined (x : BitVec 32) : LlamaBitspreadIR.tgt (some x) = Outcome.ok (expected x) := by
  rw [target_result]
  apply congrArg Outcome.ok
  apply Vector.ext
  intro i hi
  simp only [Vec.select, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_replicate, cast_lane, select_byte,
    expected]

/-- Each bit produces exactly one defined byte: 0 for a set bit, 240 otherwise. -/
theorem defined_certificate (x : BitVec 32) :
    LlamaBitspreadIR.src (some x) = Outcome.ok (expected x) ∧
    LlamaBitspreadIR.tgt (some x) = Outcome.ok (expected x) := by
  exact ⟨(same (some x)).trans (target_defined x), target_defined x⟩
end LlamaBitspread
