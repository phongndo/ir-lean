import IRLean.Generic.Arith

/-! A false lemma: `add x, x` to `shl x, 1` at every width, which is wrong in `i1`, where `shl x, 1` is poison. Its
proof fails, and `store.py add` has to refuse it with `does_not_check`, for an error of its own rather than a limit. -/

namespace LemmaStore.Test

open IRLean

theorem add_self_every_width {w : Nat} (a : Val w) (nuw nsw : Bool) :
    Val.add a a nuw nsw = Val.shl a (some 1#w) nuw nsw := by
  cases a with
  | none => rfl
  | some x =>
    simp only [Val.add, Val.shl]
    split <;> simp_all

end LemmaStore.Test
