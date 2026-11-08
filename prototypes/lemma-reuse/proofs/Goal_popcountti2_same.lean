import CrtPopcountti2
import RwPopcountti2
import Kit
import Count
import Lemma_layer_0ff6fe9e15
import Lemma_split_b78ac5f9a3
import Lemma_step_3d395ad3fc
import Lemma_step_6934d83747
import Lemma_step_baa1347fcb
import Lemma_step_81f8a11ca6
import Lemma_step_b4f1aa7047

namespace LemmaReuse

theorem popcountti2_same (a : BitVec 128) :
    RwPopcountti2._popcountti2 (some a) = CrtPopcountti2._popcountti2 (some a) := by
  llvm_exec RwPopcountti2._popcountti2
  llvm_exec CrtPopcountti2._popcountti2
  apply IRLean.result_congr
  rw [LemmaReuse.Store.layer_0ff6fe9e15 a]
  rw [LemmaReuse.Store.split_b78ac5f9a3 a]
  have h0 := LemmaReuse.field_le a 8 0
  have h1 := LemmaReuse.field_le a 8 1
  have h2 := LemmaReuse.field_le a 8 2
  have h3 := LemmaReuse.field_le a 8 3
  have h4 := LemmaReuse.field_le a 8 4
  have h5 := LemmaReuse.field_le a 8 5
  have h6 := LemmaReuse.field_le a 8 6
  have h7 := LemmaReuse.field_le a 8 7
  have h8 := LemmaReuse.field_le a 8 8
  have h9 := LemmaReuse.field_le a 8 9
  have h10 := LemmaReuse.field_le a 8 10
  have h11 := LemmaReuse.field_le a 8 11
  have h12 := LemmaReuse.field_le a 8 12
  have h13 := LemmaReuse.field_le a 8 13
  have h14 := LemmaReuse.field_le a 8 14
  have h15 := LemmaReuse.field_le a 8 15
  generalize LemmaReuse.field a 8 0 = c0 at *
  generalize LemmaReuse.field a 8 1 = c1 at *
  generalize LemmaReuse.field a 8 2 = c2 at *
  generalize LemmaReuse.field a 8 3 = c3 at *
  generalize LemmaReuse.field a 8 4 = c4 at *
  generalize LemmaReuse.field a 8 5 = c5 at *
  generalize LemmaReuse.field a 8 6 = c6 at *
  generalize LemmaReuse.field a 8 7 = c7 at *
  generalize LemmaReuse.field a 8 8 = c8 at *
  generalize LemmaReuse.field a 8 9 = c9 at *
  generalize LemmaReuse.field a 8 10 = c10 at *
  generalize LemmaReuse.field a 8 11 = c11 at *
  generalize LemmaReuse.field a 8 12 = c12 at *
  generalize LemmaReuse.field a 8 13 = c13 at *
  generalize LemmaReuse.field a 8 14 = c14 at *
  generalize LemmaReuse.field a 8 15 = c15 at *
  rw [LemmaReuse.Store.step_3d395ad3fc (x0 := c0) (x1 := c1) (x2 := c2) (x3 := c3) (x4 := c4) (x5 := c5) (x6 := c6) (x7 := c7) (x8 := c8) (x9 := c9) (x10 := c10) (x11 := c11) (x12 := c12) (x13 := c13) (x14 := c14) (x15 := c15) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_6934d83747 (x0 := (c8 + c0)) (x1 := (c9 + c1)) (x2 := (c10 + c2)) (x3 := (c11 + c3)) (x4 := (c12 + c4)) (x5 := (c13 + c5)) (x6 := (c14 + c6)) (x7 := (c15 + c7)) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_baa1347fcb (x0 := ((c12 + c4) + (c8 + c0))) (x1 := ((c13 + c5) + (c9 + c1))) (x2 := ((c14 + c6) + (c10 + c2))) (x3 := ((c15 + c7) + (c11 + c3))) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_81f8a11ca6 (x0 := (((c14 + c6) + (c10 + c2)) + ((c12 + c4) + (c8 + c0)))) (x1 := (((c15 + c7) + (c11 + c3)) + ((c13 + c5) + (c9 + c1)))) (x2 := ((c14 + c6) + (c10 + c2))) (x3 := ((c15 + c7) + (c11 + c3))) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  rw [LemmaReuse.Store.step_b4f1aa7047 (x0 := ((((c15 + c7) + (c11 + c3)) + ((c13 + c5) + (c9 + c1))) + (((c14 + c6) + (c10 + c2)) + ((c12 + c4) + (c8 + c0))))) (x1 := (((c14 + c6) + (c10 + c2)) + (((c15 + c7) + (c11 + c3)) + ((c13 + c5) + (c9 + c1))))) (x2 := (((c15 + c7) + (c11 + c3)) + ((c14 + c6) + (c10 + c2)))) (x3 := ((c15 + c7) + (c11 + c3))) (by bv_decide) (by bv_decide) (by bv_decide) (by bv_decide)]
  congr 1
  ac_rfl

end LemmaReuse
