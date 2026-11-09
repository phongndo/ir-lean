import CrtPopcountdi2
import RwPopcountdi2
import Kit
import Count
import Lemma_layer_d9d842756f
import Lemma_split_66a2d682f9
import Lemma_step_6934d83747
import Lemma_step_baa1347fcb
import Lemma_step_81f8a11ca6
import Lemma_step_344daa4124

namespace LemmaReuse

theorem popcountdi2_same (a : BitVec 64) :
    RwPopcountdi2._popcountdi2 (some a) = CrtPopcountdi2._popcountdi2 (some a) := by
  llvm_exec RwPopcountdi2._popcountdi2
  llvm_exec CrtPopcountdi2._popcountdi2
  apply IRLean.result_congr
  rw [LemmaReuse.Store.layer_d9d842756f a]
  rw [LemmaReuse.Store.split_66a2d682f9 a]
  have h0 := LemmaReuse.field_le a 8 0
  have h1 := LemmaReuse.field_le a 8 1
  have h2 := LemmaReuse.field_le a 8 2
  have h3 := LemmaReuse.field_le a 8 3
  have h4 := LemmaReuse.field_le a 8 4
  have h5 := LemmaReuse.field_le a 8 5
  have h6 := LemmaReuse.field_le a 8 6
  have h7 := LemmaReuse.field_le a 8 7
  generalize LemmaReuse.field a 8 0 = c0 at *
  generalize LemmaReuse.field a 8 1 = c1 at *
  generalize LemmaReuse.field a 8 2 = c2 at *
  generalize LemmaReuse.field a 8 3 = c3 at *
  generalize LemmaReuse.field a 8 4 = c4 at *
  generalize LemmaReuse.field a 8 5 = c5 at *
  generalize LemmaReuse.field a 8 6 = c6 at *
  generalize LemmaReuse.field a 8 7 = c7 at *
  rw [LemmaReuse.Store.step_6934d83747 (x0 := c0) (x1 := c1) (x2 := c2) (x3 := c3) (x4 := c4) (x5 := c5) (x6 := c6) (x7 := c7) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_baa1347fcb (x0 := (c4 + c0)) (x1 := (c5 + c1)) (x2 := (c6 + c2)) (x3 := (c7 + c3)) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_81f8a11ca6 (x0 := ((c6 + c2) + (c4 + c0))) (x1 := ((c7 + c3) + (c5 + c1))) (x2 := (c6 + c2)) (x3 := (c7 + c3)) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_344daa4124 (x0 := (((c7 + c3) + (c5 + c1)) + ((c6 + c2) + (c4 + c0)))) (x1 := ((c6 + c2) + ((c7 + c3) + (c5 + c1)))) (x2 := ((c7 + c3) + (c6 + c2))) (x3 := (c7 + c3)) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  congr 1
  ac_rfl

end LemmaReuse
