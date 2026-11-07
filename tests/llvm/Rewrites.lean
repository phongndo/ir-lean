import Clzsi2
import Ctzsi2
import Popcountsi2
import Paritysi2
import RwClzsi2
import RwCtzsi2
import RwPopcountsi2
import RwParitysi2

set_option linter.unusedSimpArgs false

/-! What `tests/superopt.py` found, proved to do what clang's `-O3` output does on every input. Neither side is poison or undefined
on any input, so each is a refinement of the other. -/

namespace Llvm.Rewrites

open IRLean

theorem clzsi2_same (a : BitVec 32) : RwClzsi2._clzsi2 (some a) = CrtClzsi2._clzsi2 (some a) := by
  rw [clzsi2_correct]
  simp only [Outcome.ok]
  llvm_exec RwClzsi2._clzsi2
  all_goals llvm_close

theorem ctzsi2_same (a : BitVec 32) : RwCtzsi2._ctzsi2 (some a) = CrtCtzsi2._ctzsi2 (some a) := by
  rw [ctzsi2_correct]
  simp only [Outcome.ok]
  llvm_exec RwCtzsi2._ctzsi2
  all_goals llvm_close

theorem popcountsi2_same (a : BitVec 32) : RwPopcountsi2._popcountsi2 (some a) = CrtPopcountsi2._popcountsi2 (some a) := by
  rw [popcountsi2_correct]
  simp only [Outcome.ok]
  llvm_exec RwPopcountsi2._popcountsi2
  all_goals llvm_close

theorem paritysi2_same (a : BitVec 32) : RwParitysi2._paritysi2 (some a) = CrtParitysi2._paritysi2 (some a) := by
  rw [paritysi2_correct]
  simp only [Outcome.ok]
  llvm_exec RwParitysi2._paritysi2
  all_goals llvm_close

end Llvm.Rewrites
