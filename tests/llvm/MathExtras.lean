import LlvmMathExtras
import Kit

/-! Functions from LLVM's `llvm/Support/MathExtras.h`, each compiled through a wrapper that only calls it. -/

namespace Llvm.MathExtras

open IRLean LlvmMathExtras

/-- `llvm::Hi_32`: the top half. -/
theorem hi32_correct (v : BitVec 64) : hi32 (some v) = Outcome.ok (some (v.extractLsb' 32 32)) := by
  simp only [Outcome.ok]; llvm_exec hi32; all_goals llvm_close

/-- `llvm::Lo_32`: the bottom half. -/
theorem lo32_correct (v : BitVec 64) : lo32 (some v) = Outcome.ok (some (v.extractLsb' 0 32)) := by
  simp only [Outcome.ok]; llvm_exec lo32; all_goals llvm_close

/-- `llvm::Make_64`: two halves put together. -/
theorem make64_correct (h l : BitVec 32) : make64 (some h) (some l) = Outcome.ok (some (h ++ l)) := by
  simp only [Outcome.ok]; llvm_exec make64; all_goals llvm_close

/-- `llvm::isMask_64`: whether the value is some number of ones, starting from the lowest bit, and at least one. -/
theorem ismask64_correct (v : BitVec 64) :
    ismask64 (some v) = Outcome.ok (some (BitVec.ofBool (v != 0#64 && v == BitVec.allOnes 64 >>> v.clz))) := by
  simp only [Outcome.ok]; llvm_exec ismask64; all_goals llvm_close

/-- `llvm::isShiftedMask_64`: whether the value's set bits are one run, and there's at least one. -/
theorem isshiftedmask64_correct (v : BitVec 64) :
    isshiftedmask64 (some v) = Outcome.ok (some (BitVec.ofBool
      (v != 0#64 && (v >>> v.ctz) == BitVec.allOnes 64 >>> (v >>> v.ctz).clz))) := by
  simp only [Outcome.ok]; llvm_exec isshiftedmask64; all_goals llvm_close

/-- `llvm::isPowerOf2_64`: whether exactly one bit is set. -/
theorem ispowerof2_64_correct (v : BitVec 64) :
    ispowerof2_64 (some v) = Outcome.ok (some (BitVec.ofBool (v.cpop == 1#64))) := by
  simp only [Outcome.ok]; llvm_exec ispowerof2_64; all_goals llvm_close

/-- `llvm::Log2_64`: for a value that isn't zero, the position of its highest set bit. -/
theorem log2_64_correct (v : BitVec 64) (h : v ≠ 0#64) :
    ∃ r : BitVec 32, log2_64 (some v) = Outcome.ok (some r) ∧ r < 64#32 ∧ v >>> r = 1#64 := by
  refine ⟨(63#64 - v.clz).setWidth 32, ?_, by bv_decide, by bv_decide⟩
  simp only [Outcome.ok]; llvm_exec log2_64; all_goals llvm_close

/-- `llvm::Log2_64_Ceil`: for a value that isn't zero, the smallest `r` with `v ≤ 2 ^ r`. -/
theorem log2_64_ceil_correct (v : BitVec 64) (h : v ≠ 0#64) :
    ∃ r : BitVec 32, log2_64_ceil (some v) = Outcome.ok (some r) ∧ r ≤ 64#32 ∧
      v.setWidth 65 ≤ 1#65 <<< r ∧ (r = 0#32 ∨ 1#65 <<< (r - 1#32) < v.setWidth 65) := by
  refine ⟨(64#64 - (v - 1#64).clz).setWidth 32, ?_, by bv_decide, by bv_decide, by bv_decide⟩
  simp only [Outcome.ok]; llvm_exec log2_64_ceil; all_goals llvm_close

/-- `llvm::MinAlign`: the lowest set bit of either value, which is the largest power of 2 dividing both. -/
theorem minalign_correct (a b : BitVec 64) :
    minalign (some a) (some b) =
      Outcome.ok (some (if a ||| b = 0#64 then 0#64 else 1#64 <<< (a ||| b).ctz)) := by
  simp only [Outcome.ok]; llvm_exec minalign; all_goals llvm_close

/-- `llvm::NextPowerOf2`: the smallest power of 2 above `a`, or 0 if none fits. -/
theorem nextpowerof2_correct (a : BitVec 64) :
    nextpowerof2 (some a) = Outcome.ok (some (if a.msb then 0#64 else 1#64 <<< (64#64 - a.clz))) := by
  simp only [Outcome.ok]; llvm_exec nextpowerof2; all_goals llvm_close

/-- `llvm::PowerOf2Ceil`: the smallest power of 2 that's at least `a`, if `a` is below `2 ^ 63`. It gives 0 for 0, and also
for `2 ^ 63`, which is a power of 2 that fits, and for anything above that, which doesn't. -/
theorem powerof2ceil_correct (a : BitVec 64) :
    ∃ r : BitVec 64, powerof2ceil (some a) = Outcome.ok (some r) ∧
      (a = 0#64 ∨ a.msb = true → r = 0#64) ∧
      (a ≠ 0#64 → a.msb = false → r.cpop = 1#64 ∧ a ≤ r ∧ r >>> 1#64 < a) := by
  refine ⟨if a = 0#64 ∨ a.msb = true then 0#64 else 1#64 <<< (64#64 - (a - 1#64).clz), ?_, by bv_decide, ?_⟩
  · simp only [Outcome.ok]; llvm_exec powerof2ceil; all_goals llvm_close
  · intro h0 h1
    refine ⟨by bv_decide, by bv_decide, by bv_decide⟩

/-- `llvm::isUIntN`: whether `x` fits in `n` bits. -/
theorem isuintn_correct (n : BitVec 32) (x : BitVec 64) :
    isuintn (some n) (some x) =
      Outcome.ok (some (BitVec.ofBool (x.setWidth 128 < 1#128 <<< n.setWidth 128 || 64#32 ≤ n))) := by
  simp only [Outcome.ok]; llvm_exec isuintn; all_goals llvm_close

/-- `llvm::maxUIntN`: for `n` from 1 to 64, one less than `2 ^ n`. -/
theorem maxuintn_correct (n : BitVec 64) (h0 : 0#64 < n) (h : n ≤ 64#64) :
    ∃ r : BitVec 64, maxuintn (some n) = Outcome.ok (some r) ∧ r.setWidth 65 + 1#65 = 1#65 <<< n := by
  refine ⟨BitVec.allOnes 64 >>> (64#64 - n), ?_, by bv_decide⟩
  simp only [Outcome.ok]; llvm_exec maxuintn; all_goals llvm_close

/-- `llvm::minIntN`: for `n` from 1 to 64, `-2 ^ (n - 1)`. -/
theorem minintn_correct (n : BitVec 64) (h0 : 0#64 < n) (h : n ≤ 64#64) :
    minintn (some n) = Outcome.ok (some (-(1#64 <<< (n - 1#64)))) := by
  simp only [Outcome.ok]; llvm_exec minintn; all_goals llvm_close

/-- `llvm::maxIntN`: for `n` from 1 to 64, `2 ^ (n - 1) - 1`. -/
theorem maxintn_correct (n : BitVec 64) (h0 : 0#64 < n) (h : n ≤ 64#64) :
    maxintn (some n) = Outcome.ok (some ((1#64 <<< (n - 1#64)) - 1#64)) := by
  simp only [Outcome.ok]; llvm_exec maxintn; all_goals llvm_close

/-- `llvm::isIntN`: for `n` from 1 up, whether `x` is between `-2 ^ (n - 1)` and `2 ^ (n - 1) - 1`, which is to say
whether everything from bit `n - 1` up is the same. -/
theorem isintn_correct (n : BitVec 32) (x : BitVec 64) (h0 : 0#32 < n) :
    isintn (some n) (some x) = Outcome.ok (some (BitVec.ofBool
      (64#32 ≤ n || x.sshiftRight' (n - 1#32) == 0#64 || x.sshiftRight' (n - 1#32) == BitVec.allOnes 64))) := by
  simp only [Outcome.ok]; llvm_exec isintn; all_goals llvm_close

/-- `llvm::SignExtend64`: for `b` from 1 to 64, what comes back has the low `b` bits of `x`, and bit `b - 1` of `x` in all
the bits above. -/
theorem signextend64_correct (x : BitVec 64) (b : BitVec 32) (h0 : 0#32 < b) (h : b ≤ 64#32) :
    ∃ r : BitVec 64, signextend64 (some x) (some b) = Outcome.ok (some r) ∧
      r <<< (64#32 - b) = x <<< (64#32 - b) ∧
      (r.sshiftRight' (b - 1#32) = 0#64 ∨ r.sshiftRight' (b - 1#32) = BitVec.allOnes 64) := by
  refine ⟨(x <<< (64#32 - b).setWidth 64).sshiftRight' ((64#32 - b).setWidth 64), ?_, by bv_decide, by bv_decide⟩
  simp only [Outcome.ok]; llvm_exec signextend64; all_goals llvm_close

/-- `llvm::AbsoluteDifference`. -/
theorem abs_diff_correct (a b : BitVec 64) :
    abs_diff (some a) (some b) = Outcome.ok (some (if b ≤ a then a - b else b - a)) := by
  simp only [Outcome.ok]; llvm_exec abs_diff; all_goals llvm_close

/-- `llvm::maskTrailingOnes<uint32_t>`: `n` ones at the bottom. -/
theorem masktrailingones32_correct (n : BitVec 32) (h : n ≤ 32#32) :
    masktrailingones32 (some n) =
      Outcome.ok (some (if n = 0#32 then 0#32 else BitVec.allOnes 32 >>> (32#32 - n))) := by
  simp only [Outcome.ok]; llvm_exec masktrailingones32; all_goals llvm_close

/-- `llvm::maskTrailingOnes<uint64_t>`: `n` ones at the bottom. -/
theorem masktrailingones64_correct (n : BitVec 32) (h : n ≤ 64#32) :
    masktrailingones64 (some n) =
      Outcome.ok (some (if n = 0#32 then 0#64 else BitVec.allOnes 64 >>> (64#32 - n))) := by
  simp only [Outcome.ok]; llvm_exec masktrailingones64; all_goals llvm_close

/-- `llvm::maskLeadingOnes<uint64_t>`: `n` ones at the top. -/
theorem maskleadingones64_correct (n : BitVec 32) (h : n ≤ 64#32) :
    maskleadingones64 (some n) =
      Outcome.ok (some (if n = 64#32 then BitVec.allOnes 64 else ~~~(BitVec.allOnes 64 >>> n))) := by
  simp only [Outcome.ok]; llvm_exec maskleadingones64; all_goals llvm_close

/-- `llvm::reverseBits<uint32_t>`. -/
theorem reversebits32_correct (v : BitVec 32) :
    reversebits32 (some v) = Outcome.ok (some v.reverse) := by
  simp only [Outcome.ok]; llvm_exec reversebits32; all_goals llvm_close

/-- `llvm::reverseBits<uint64_t>`. -/
theorem reversebits64_correct (v : BitVec 64) :
    reversebits64 (some v) = Outcome.ok (some v.reverse) := by
  simp only [Outcome.ok]; llvm_exec reversebits64; all_goals llvm_close

end Llvm.MathExtras
