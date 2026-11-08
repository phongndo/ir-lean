import CrtPopcountsi2
import RwPopcountsi2
import Kit
import Count
import Lemma_layer_15cdd830e1
import Lemma_split_91f21dc64e
import Lemma_step_baa1347fcb
import Lemma_step_81f8a11ca6
import Lemma_step_b7ebfec089

namespace LemmaReuse

theorem popcountsi2_same (a : BitVec 32) :
    RwPopcountsi2._popcountsi2 (some a) = CrtPopcountsi2._popcountsi2 (some a) := by
  llvm_exec RwPopcountsi2._popcountsi2
  llvm_exec CrtPopcountsi2._popcountsi2
  apply IRLean.result_congr
  rw [LemmaReuse.Store.layer_15cdd830e1 a]
  rw [LemmaReuse.Store.split_91f21dc64e a]
  have h0 := LemmaReuse.field_le a 8 0
  have h1 := LemmaReuse.field_le a 8 1
  have h2 := LemmaReuse.field_le a 8 2
  have h3 := LemmaReuse.field_le a 8 3
  generalize LemmaReuse.field a 8 0 = c0 at *
  generalize LemmaReuse.field a 8 1 = c1 at *
  generalize LemmaReuse.field a 8 2 = c2 at *
  generalize LemmaReuse.field a 8 3 = c3 at *
  rw [LemmaReuse.Store.step_baa1347fcb (x0 := c0) (x1 := c1) (x2 := c2) (x3 := c3) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_81f8a11ca6 (x0 := (c2 + c0)) (x1 := (c3 + c1)) (x2 := c2) (x3 := c3) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_b7ebfec089 (x0 := ((c3 + c1) + (c2 + c0))) (x1 := (c2 + (c3 + c1))) (x2 := (c3 + c2)) (x3 := c3) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  congr 1
  ac_rfl

end LemmaReuse
