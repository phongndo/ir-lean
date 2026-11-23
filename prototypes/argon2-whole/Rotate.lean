import IRLean

/-! Lanes of the vector operations the Argon2 round's slices use, and the tactic that proves two slices give
the same vector: lane by lane, both sides are the same scalar expression of the parameters' lanes. -/

open IRLean

namespace Argon2Rotate

theorem lane_ofFn {f : Fin n → Val w} {i : Nat} :
    Vec.lane (Vector.ofFn f) i = if h : i < n then f ⟨i, h⟩ else none := by
  unfold Vec.lane
  split <;> simp_all

theorem lane_map2 {f : Val w → Val u → Val v} {a : Vec n w} {b : Vec n u} {i : Nat} :
    (Vec.map2 f a b).lane i = if i < n then f (a.lane i) (b.lane i) else none := by
  unfold Vec.map2
  rw [lane_ofFn]
  unfold Vec.lane
  split <;> simp_all

theorem lane_map3 {f : Val w → Val w → Val w → Val v} {a b c : Vec n w} {i : Nat} :
    (Vec.map3 f a b c).lane i = if i < n then f (a.lane i) (b.lane i) (c.lane i) else none := by
  unfold Vec.map3
  rw [lane_ofFn]
  unfold Vec.lane
  split <;> simp_all

theorem lane_shuffle {a b : Vec n w} {mask : Array (Option Nat)} {i : Nat} :
    (Vec.shuffle k a b mask).lane i =
      if i < k then
        (match mask[i]? with
          | some (some j) => if j < n then a.lane j else b.lane (j - n)
          | _ => none)
      else none := by
  unfold Vec.shuffle
  rw [lane_ofFn]
  split <;> rfl

/-- Two vectors with the same lanes are the same vector. -/
theorem ext_lanes {a b : Vec n w} (h : ∀ i, i < n → a.lane i = b.lane i) : a = b := by
  apply Vector.ext
  intro i hi
  have := h i hi
  simpa [Vec.lane, hi] using this

/-- For eight lanes, one goal a lane. -/
theorem ext_lanes8 {a b : Vec 8 w} (h0 : a.lane 0 = b.lane 0) (h1 : a.lane 1 = b.lane 1)
    (h2 : a.lane 2 = b.lane 2) (h3 : a.lane 3 = b.lane 3) (h4 : a.lane 4 = b.lane 4)
    (h5 : a.lane 5 = b.lane 5) (h6 : a.lane 6 = b.lane 6) (h7 : a.lane 7 = b.lane 7) : a = b := by
  apply ext_lanes
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Proves a rewritten slice equal to clang's: runs both blocks, and compares the two vectors lane by lane. -/
syntax "rotate_slice " ident ident ident ident : tactic
macro_rules
  | `(tactic| rotate_slice $tgt $src $tgtStep $srcStep) =>
    `(tactic| (
      unfold $tgt:ident $src:ident
      rw [run, run]
      simp only [$tgtStep:ident, $srcStep:ident, ret, Outcome.ok]
      refine congrArg (fun x => some (Except.ok x)) ?_
      refine ext_lanes8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        (simp [lane_shuffle, lane_map2, lane_map3]; try simp [Vec.lane])))

end Argon2Rotate
