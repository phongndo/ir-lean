import IRLean

/-! Why `tests/llama/vnni.py`'s rewrite of llama.cpp's q4_K kernels gives the same values as clang's `-O3` IR.

Clang leaves, for each block of quantized weights,

  pmaddwd(p0 + p1 + ... + p7, c)    where p_k = pmaddubsw(a_k, b_k)

and the rewrite computes

  vpdpbusd(... vpdpbusd(vpdpbusd(0, a_0, b_0), a_1, b_1) ..., a_7, b_7) * sext(low half of each lane of c).

These agree on every input where every byte of every `a_k` is below 16, which holds because clang's IR masks
them with `0x0F0F0F0F`, and the two 16-bit halves of each 32-bit lane of `c` are equal, which holds because it
builds `c` by repeating each scale twice. Then no `pmaddubsw` saturates, no 16-bit sum wraps, and the scale
factors out. `base`, `step` and `final` say this lane by lane, poison included, and the lemmas before them show
the two facts hold of the values clang's IR computes, from its own instructions. `vnni_slice` puts it together for
each place, which `tests/llama.py` cuts out of the kernels. -/

namespace Llama.Vnni

open IRLean

/-! ### Lanes -/

theorem lane_ofFn {f : Fin n → Val w} {i : Nat} :
    Vec.lane (Vector.ofFn f) i = if h : i < n then f ⟨i, h⟩ else none := by
  unfold Vec.lane
  split <;> simp_all

theorem lane_map {f : Val w → Val v} {a : Vec n w} {i : Nat} :
    (Vec.map f a).lane i = if i < n then f (a.lane i) else none := by
  unfold Vec.map Vec.lane
  split <;> simp_all

theorem lane_map2 {f : Val w → Val u → Val v} {a : Vec n w} {b : Vec n u} {i : Nat} :
    (Vec.map2 f a b).lane i = if i < n then f (a.lane i) (b.lane i) else none := by
  unfold Vec.map2
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

theorem lane_split {a : Vec n w} {i : Nat} :
    (Vec.split m v k a).lane i =
      if i < m then (a.lane (i / k)).map (fun x => x.extractLsb' (v * (i % k)) v) else none := by
  unfold Vec.split
  rw [lane_ofFn]
  split
  · simp only
    split <;> simp_all
  · rfl

theorem lane_join2 {a : Vec n w} {i : Nat} :
    (Vec.join m v 2 a).lane i =
      if i < m then
        (match a.lane (2 * i), a.lane (2 * i + 1) with
          | some x0, some x1 => some ((((0#v <<< w) ||| x1.setWidth v) <<< w) ||| x0.setWidth v)
          | _, _ => none)
      else none := by
  unfold Vec.join
  rw [lane_ofFn]
  split
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldr_cons,
      List.foldr_nil, Nat.add_zero]
    cases a.lane (2 * i) <;> cases a.lane (2 * i + 1) <;> rfl
  · rfl

/-- A property of every lane survives a shuffle, if poison has it. -/
theorem shuffle_all {P : Val w → Prop} (hn : P none) {a b : Vec n w} (ha : ∀ i, P (a.lane i))
    (hb : ∀ i, P (b.lane i)) (mask : Array (Option Nat)) : ∀ i, P ((Vec.shuffle k a b mask).lane i) := by
  intro i
  rw [lane_shuffle]
  split
  · split
    · split
      · exact ha _
      · exact hb _
    · exact hn
  · exact hn

theorem lane_replicate {c : Val w} {i : Nat} (h : i < n) : Vec.lane (Vector.replicate n c) i = c := by
  unfold Vec.lane
  simp [h]

/-! ### Nibbles: what masking with `0x0F0F0F0F` leaves, through shuffles and bitcasts -/

/-- A byte that's poison or below 16. -/
def Nib (v : Val 8) : Prop := ∀ x, v = some x → x.toNat < 16

/-- Every byte of a vector is poison or below 16. -/
def Nibbles (a : Vec n 8) : Prop := ∀ i, Nib (a.lane i)

/-- A 32-bit lane that's poison or has nothing in the high nibble of any byte. -/
def Low (v : Val 32) : Prop := ∀ x, v = some x → x &&& 0xF0F0F0F0#32 = 0#32

theorem lows_and {x M : Vec n 32} (hM : M = Vector.replicate n (some 252645135#32)) :
    ∀ i, Low ((Vec.map2 (fun a b => Val.and a b) x M).lane i) := by
  intro i y h
  rw [lane_map2] at h
  split at h
  · rw [hM, lane_replicate (by assumption)] at h
    cases hx : x.lane i with
    | none => simp [hx, Val.and, Val.map₂] at h
    | some z =>
      simp only [hx, Val.and, Val.map₂, Option.some.injEq] at h
      subst h
      bv_decide
  · cases h

theorem nib_of_low {x : BitVec 32} (h : x &&& 0xF0F0F0F0#32 = 0#32) {r : Nat} (hr : r < 4) :
    (x.extractLsb' (8 * r) 8).toNat < 16 := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · have : x.extractLsb' 0 8 < 16#8 := by bv_decide
    simpa [BitVec.lt_def] using this
  · have : x.extractLsb' 8 8 < 16#8 := by bv_decide
    simpa [BitVec.lt_def] using this
  · have : x.extractLsb' 16 8 < 16#8 := by bv_decide
    simpa [BitVec.lt_def] using this
  · have : x.extractLsb' 24 8 < 16#8 := by bv_decide
    simpa [BitVec.lt_def] using this

theorem nibbles_split {a : Vec n 32} (ha : ∀ i, Low (a.lane i)) : Nibbles (Vec.split m 8 4 a) := by
  intro i x h
  rw [lane_split] at h
  split at h
  · cases hl : a.lane (i / 4) with
    | none => simp [hl] at h
    | some y =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      subst h
      exact nib_of_low (ha _ y hl) (Nat.mod_lt _ (by decide))
  · cases h

theorem lows_shuffle {a b : Vec n 32} (ha : ∀ i, Low (a.lane i)) (hb : ∀ i, Low (b.lane i))
    (mask : Array (Option Nat)) : ∀ i, Low ((Vec.shuffle k a b mask).lane i) :=
  shuffle_all (fun _ h => by cases h) ha hb mask

theorem nibbles_shuffle {a b : Vec n 8} (ha : Nibbles a) (hb : Nibbles b) (mask : Array (Option Nat)) :
    Nibbles (Vec.shuffle k a b mask) :=
  shuffle_all (fun _ h => by cases h) ha hb mask

theorem nibbles_poison : Nibbles (HasPoison.poison : Vec n 8) := by
  intro i x h
  unfold Vec.lane at h
  split at h <;> simp_all [HasPoison.poison]

theorem lows_poison : ∀ i, Low ((HasPoison.poison : Vec n 32).lane i) := by
  intro i x h
  unfold Vec.lane at h
  split at h <;> simp_all [HasPoison.poison]

/-- A 16-bit lane that's poison or has nothing in the high nibble of either byte, for code that masks with
`0x0F0F` in 16-bit lanes. -/
def Low16 (v : Val 16) : Prop := ∀ x, v = some x → x &&& 0xF0F0#16 = 0#16

theorem lows16_and {x M : Vec n 16} (hM : M = Vector.replicate n (some 3855#16)) :
    ∀ i, Low16 ((Vec.map2 (fun a b => Val.and a b) x M).lane i) := by
  intro i y h
  rw [lane_map2] at h
  split at h
  · rw [hM, lane_replicate (by assumption)] at h
    cases hx : x.lane i with
    | none => simp [hx, Val.and, Val.map₂] at h
    | some z =>
      simp only [hx, Val.and, Val.map₂, Option.some.injEq] at h
      subst h
      bv_decide
  · cases h

theorem nibbles_split2 {a : Vec n 16} (ha : ∀ i, Low16 (a.lane i)) : Nibbles (Vec.split m 8 2 a) := by
  intro i x h
  rw [lane_split] at h
  split at h
  · cases hl : a.lane (i / 2) with
    | none => simp [hl] at h
    | some y =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      subst h
      have hy := ha _ y hl
      have : i % 2 = 0 ∨ i % 2 = 1 := by omega
      rcases this with e | e <;> rw [e]
      · have : y.extractLsb' 0 8 < 16#8 := by bv_decide
        simpa [BitVec.lt_def] using this
      · have : y.extractLsb' 8 8 < 16#8 := by bv_decide
        simpa [BitVec.lt_def] using this
  · cases h

theorem lows16_shuffle {a b : Vec n 16} (ha : ∀ i, Low16 (a.lane i)) (hb : ∀ i, Low16 (b.lane i))
    (mask : Array (Option Nat)) : ∀ i, Low16 ((Vec.shuffle k a b mask).lane i) :=
  shuffle_all (fun _ h => by cases h) ha hb mask

/-! ### Paired scales: each scale repeated in both halves of a 32-bit lane -/

/-- Lanes `2j` and `2j + 1` are the same, poison or not. -/
def Pairs (a : Vec n w) : Prop := ∀ j, a.lane (2 * j) = a.lane (2 * j + 1)

/-- Whether a shuffle mask repeats each entry twice: `j` and `j + 1` agree for even `j`. -/
def pairMask (mask : Array (Option Nat)) : Bool :=
  (List.range mask.size).all fun i => i % 2 == 1 || mask[i]? == mask[i + 1]?

theorem pairMask_spec {mask : Array (Option Nat)} (h : pairMask mask = true) (j : Nat) :
    mask[2 * j]? = mask[2 * j + 1]? := by
  by_cases hj : 2 * j < mask.size
  · unfold pairMask at h
    rw [List.all_eq_true] at h
    have := h (2 * j) (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h1 | h1
    · omega
    · exact h1
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

theorem pairs_shuffle {a b : Vec n w} {mask : Array (Option Nat)} (hm : pairMask mask = true)
    (hk : mask.size = k) : Pairs (Vec.shuffle k a b mask) := by
  intro j
  rw [lane_shuffle, lane_shuffle, ← pairMask_spec hm j]
  by_cases h1 : 2 * j + 1 < k
  · simp [show 2 * j < k by omega, h1]
  · have : mask[2 * j]? = none := by
      rw [pairMask_spec hm j, Array.getElem?_eq_none (by omega)]
    simp [h1, this]

theorem pairs_map {f : Val w → Val v} (hf : f none = none) {a : Vec n w} (ha : Pairs a) :
    Pairs (Vec.map f a) := by
  intro j
  rw [lane_map, lane_map, ha j]
  by_cases h1 : 2 * j + 1 < n
  · simp [show 2 * j < n by omega, h1]
  · have : a.lane (2 * j + 1) = none := by unfold Vec.lane; simp [h1]
    simp [h1, this, hf]

/-- A 32-bit lane that's poison or has the same two halves. -/
def Same (v : Val 32) : Prop := ∀ x, v = some x → x.extractLsb' 0 16 = x.extractLsb' 16 16

theorem same_join {c : Vec n 16} (hc : Pairs c) : ∀ i, Same ((Vec.join m 32 2 c).lane i) := by
  intro i x h
  rw [lane_join2, hc i] at h
  split at h
  · split at h
    · next x0 x1 h0 h1 =>
      simp only [Option.some.injEq] at h
      rw [h0] at h1
      cases h1
      subst h
      bv_decide
    · cases h
  · cases h

theorem sames_shuffle {a b : Vec n 32} (ha : ∀ i, Same (a.lane i)) (hb : ∀ i, Same (b.lane i))
    (mask : Array (Option Nat)) : ∀ i, Same ((Vec.shuffle k a b mask).lane i) :=
  shuffle_all (fun _ h => by cases h) ha hb mask

theorem sames_poison : ∀ i, Same ((HasPoison.poison : Vec n 32).lane i) := by
  intro i x h
  unfold Vec.lane at h
  split at h <;> simp_all [HasPoison.poison]

theorem pairs_split {a : Vec n 32} (ha : ∀ i, Same (a.lane i)) (hm : m % 2 = 0) :
    Pairs (Vec.split m 16 2 a) := by
  intro j
  rw [lane_split, lane_split]
  have e1 : 2 * j / 2 = j := by omega
  have e2 : (2 * j + 1) / 2 = j := by omega
  have e3 : 2 * j % 2 = 0 := by omega
  have e4 : (2 * j + 1) % 2 = 1 := by omega
  rw [e1, e2, e3, e4]
  by_cases h1 : 2 * j + 1 < m
  · simp only [show 2 * j < m by omega, h1, ite_true]
    cases hl : a.lane j with
    | none => rfl
    | some x => simp only [Option.map_some, Option.some.injEq]; exact ha j x hl
  · simp [show ¬ 2 * j < m by omega, h1]

/-! ### The arithmetic, on each lane -/

theorem if_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} {a b : α} : (if c then a else b) = a := by
  simp [h]

/-- Addition when neither side is poison. -/
def addO : Option Int → Option Int → Option Int
  | some x, some y => some (x + y)
  | _, _ => none

/-- The two products `pmaddubsw` adds for lane `i`, before it saturates. -/
def pp (a b : Vec m 8) (i : Nat) : Option Int :=
  match a.lane (2 * i), a.lane (2 * i + 1), b.lane (2 * i), b.lane (2 * i + 1) with
  | some x0, some x1, some y0, some y1 => some (x0.toNat * y0.toInt + x1.toNat * y1.toInt)
  | _, _, _, _ => none

theorem lane_pmaddubsw {a b : Vec m 8} {i : Nat} :
    (X86.pmaddubsw p a b).lane i = if i < p then (pp a b i).map X86.ssat16 else none := by
  unfold X86.pmaddubsw
  rw [lane_ofFn]
  split
  · simp only [pp]
    split <;> simp_all
  · rfl

theorem lane_pmaddwd {s c : Vec m 16} {j : Nat} :
    (X86.pmaddwd n s c).lane j =
      if j < n then
        (match s.lane (2 * j), s.lane (2 * j + 1), c.lane (2 * j), c.lane (2 * j + 1) with
          | some x0, some x1, some y0, some y1 =>
            some (BitVec.ofInt 32 (x0.toInt * y0.toInt + x1.toInt * y1.toInt))
          | _, _, _, _ => none)
      else none := by
  unfold X86.pmaddwd
  rw [lane_ofFn]
  split <;> rfl

theorem lane_vpdpbusd {acc : Vec n 32} {a b : Vec m 8} {j : Nat} :
    (X86.vpdpbusd acc a b).lane j =
      if j < n then
        (match acc.lane j, X86.dot4 a b j with
          | some s, some d => some (s + BitVec.ofInt 32 d)
          | _, _ => none)
      else none := by
  unfold X86.vpdpbusd
  rw [lane_ofFn]
  split
  · next h =>
    have : acc[(⟨j, h⟩ : Fin n)] = acc.lane j := by unfold Vec.lane; simp [h]
    rw [this]
    rfl
  · rfl

/-- `dot4` is `pp` of two neighboring lanes. -/
theorem dot4_pp {a b : Vec m 8} {j : Nat} : X86.dot4 a b j = addO (pp a b (2 * j)) (pp a b (2 * j + 1)) := by
  unfold X86.dot4 pp
  have e0 : 2 * (2 * j) = 4 * j := by omega
  have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by omega
  have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by omega
  have e3 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by omega
  rw [e1, e0, e3, e2]
  cases a.lane (4 * j) <;> cases a.lane (4 * j + 1) <;> cases a.lane (4 * j + 2) <;>
    cases a.lane (4 * j + 3) <;> cases b.lane (4 * j) <;> cases b.lane (4 * j + 1) <;>
    cases b.lane (4 * j + 2) <;> cases b.lane (4 * j + 3) <;> simp [addO] <;> omega

/-- `o` is poison or at most `k` times the most `pmaddubsw` can give without saturating, either way. -/
def Bounded (k : Nat) (o : Option Int) : Prop := ∀ v, o = some v → -(3840 * k : Int) ≤ v ∧ v ≤ 3840 * k

theorem prod_bound {x y : BitVec 8} (hx : x.toNat < 16) :
    -1920 ≤ (x.toNat : Int) * y.toInt ∧ (x.toNat : Int) * y.toInt ≤ 1920 := by
  have h1 := BitVec.le_toInt y
  have h2 := BitVec.toInt_lt (x := y)
  have l := Int.mul_le_mul_of_nonneg_left (show y.toInt ≤ 127 by simp at h2; omega)
    (show (0 : Int) ≤ x.toNat by omega)
  have r := Int.mul_le_mul_of_nonneg_left (show -128 ≤ y.toInt by simp at h1; omega)
    (show (0 : Int) ≤ x.toNat by omega)
  omega

theorem pp_bounded {a b : Vec m 8} (ha : Nibbles a) (i : Nat) : Bounded 1 (pp a b i) := by
  intro v h
  unfold pp at h
  split at h
  · next x0 x1 y0 y1 h0 h1 _ _ =>
    simp only [Option.some.injEq] at h
    have b0 := prod_bound (y := y0) (ha _ x0 h0)
    have b1 := prod_bound (y := y1) (ha _ x1 h1)
    omega
  · cases h

theorem ssat_of_bounded {v : Int} (h : -(32768 : Int) ≤ v ∧ v ≤ 32767) : X86.ssat16 v = BitVec.ofInt 16 v := by
  unfold X86.ssat16
  congr 1
  omega

/-- What the two sides have computed so far, for `k` of the eight products. For each 32-bit lane `j`, there's
a sum for each of the two 16-bit lanes under it. The left side holds each in 16 bits, and the right side holds
their total in 32. -/
def Inv (k : Nat) (s : Vec p 16) (acc : Vec n 32) : Prop :=
  ∀ j < n, ∃ x y : Option Int, Bounded k x ∧ Bounded k y ∧
    s.lane (2 * j) = x.map (BitVec.ofInt 16) ∧ s.lane (2 * j + 1) = y.map (BitVec.ofInt 16) ∧
    acc.lane j = (addO x y).map (BitVec.ofInt 32)

theorem pmaddubsw_lane_eq {a b : Vec m 8} (ha : Nibbles a) {i : Nat} (hi : i < p) :
    (X86.pmaddubsw p a b).lane i = (pp a b i).map (BitVec.ofInt 16) := by
  rw [lane_pmaddubsw, if_pos' hi]
  cases h : pp a b i with
  | none => rfl
  | some v =>
    have := pp_bounded ha i v h
    simp only [Option.map_some, Option.some.injEq]
    exact ssat_of_bounded (by omega)

theorem base {a b : Vec m 8} {Z : Vec n 32} (ha : Nibbles a) (hZ : Z = Vector.replicate n (some 0#32))
    (hp : p = 2 * n) : Inv 1 (X86.pmaddubsw p a b) (X86.vpdpbusd Z a b) := by
  intro j hj
  refine ⟨pp a b (2 * j), pp a b (2 * j + 1), pp_bounded ha _, pp_bounded ha _,
    pmaddubsw_lane_eq ha (by omega), pmaddubsw_lane_eq ha (by omega), ?_⟩
  rw [lane_vpdpbusd, if_pos' hj, hZ, lane_replicate hj, dot4_pp]
  cases pp a b (2 * j) <;> cases pp a b (2 * j + 1) <;> simp [addO]

theorem addO_swap (a b c d : Option Int) : addO (addO a b) (addO c d) = addO (addO a c) (addO b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [addO] <;> omega

theorem step {s : Vec p 16} {acc : Vec n 32} {a b : Vec m 8} (h : Inv k s acc) (ha : Nibbles a)
    (hp : p = 2 * n) :
    Inv (k + 1) (Vec.map2 (fun a b => Val.add a b) s (X86.pmaddubsw p a b)) (X86.vpdpbusd acc a b) := by
  intro j hj
  obtain ⟨x, y, bx, byy, hx, hy, hacc⟩ := h j hj
  have add16 : ∀ (o q : Option Int),
      Val.add (o.map (BitVec.ofInt 16)) (q.map (BitVec.ofInt 16)) = (addO o q).map (BitVec.ofInt 16) := by
    intro o q
    cases o <;> cases q <;> simp [Val.add, addO, BitVec.ofInt_add]
  have bound : ∀ (o q : Option Int), Bounded k o → Bounded 1 q → Bounded (k + 1) (addO o q) := by
    intro o q ho hq v hv
    cases o <;> cases q <;> simp [addO] at hv
    next u w =>
      have := ho u rfl
      have := hq w rfl
      subst hv
      push_cast
      omega
  refine ⟨addO x (pp a b (2 * j)), addO y (pp a b (2 * j + 1)), bound _ _ bx (pp_bounded ha _),
    bound _ _ byy (pp_bounded ha _), ?_, ?_, ?_⟩
  · rw [lane_map2, if_pos' (by omega), hx, pmaddubsw_lane_eq ha (by omega), add16]
  · rw [lane_map2, if_pos' (by omega), hy, pmaddubsw_lane_eq ha (by omega), add16]
  · rw [lane_vpdpbusd, if_pos' hj, hacc, dot4_pp, addO_swap]
    cases addO x y <;> cases addO (pp a b (2 * j)) (pp a b (2 * j + 1)) <;>
      simp [addO, BitVec.ofInt_add]

theorem scale_lane (x : BitVec 16) :
    Val.ashr (Val.shl (some ((((0#32 <<< 16) ||| x.setWidth 32) <<< 16) ||| x.setWidth 32)) (some 16#32))
      (some 16#32) = some (BitVec.ofInt 32 x.toInt) := by
  have e : ((((((0#32 <<< 16) ||| x.setWidth 32) <<< 16) ||| x.setWidth 32) <<< 16#32).sshiftRight' 16#32) =
      x.signExtend 32 := by bv_decide
  have s : BitVec.ofInt 32 x.toInt = x.signExtend 32 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt]
    have := BitVec.le_toInt x
    have := BitVec.toInt_lt (x := x)
    simp at *
    exact Int.bmod_eq_of_le (by omega) (by omega)
  simp only [Val.ashr, Val.shl, show Val.shiftOk 16#32 = true by decide, Bool.not_true, Bool.false_eq_true,
    ite_false, Bool.false_and, e, s]

theorem final {s : Vec p 16} {acc : Vec n 32} {c : Vec p 16} {S : Vec n 32} (h : Inv k s acc) (hk : k ≤ 8)
    (hc : Pairs c) (hS : S = Vector.replicate n (some 16#32)) :
    Vec.map2 (fun a b => Val.mul a b) acc
        (Vec.map2 (fun a b => Val.ashr a b) (Vec.map2 (fun a b => Val.shl a b) (Vec.join n 32 2 c) S) S) =
      X86.pmaddwd n s c := by
  apply Vector.ext
  intro j hj
  have l : ∀ (v : Vec n 32), v[j] = v.lane j := fun v => by unfold Vec.lane; simp [hj]
  rw [l, l, lane_map2, if_pos' hj, lane_map2, if_pos' hj, lane_map2, if_pos' hj, hS, lane_replicate hj,
    lane_join2, if_pos' hj, lane_pmaddwd, if_pos' hj, ← hc j]
  obtain ⟨x, y, bx, byy, hx, hy, hacc⟩ := h j hj
  rw [hx, hy, hacc]
  cases hcl : c.lane (2 * j) with
  | none => cases x <;> cases y <;> simp [addO, Val.mul, Val.shl, Val.ashr]
  | some z =>
    simp only [scale_lane]
    cases x with
    | none => simp [addO, Val.mul]
    | some u =>
      cases y with
      | none => simp [addO, Val.mul]
      | some w =>
        have hu := bx u rfl
        have hw := byy w rfl
        have tu : (BitVec.ofInt 16 u).toInt = u := by
          rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
        have tw : (BitVec.ofInt 16 w).toInt = w := by
          rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
        simp only [addO, Option.map_some, Val.mul, Bool.false_and, Bool.or_false, Bool.false_eq_true,
          ite_false, tu, tw, Option.some.injEq]
        rw [← BitVec.ofInt_mul, Int.add_mul]

/-! ### Tactics for each place the rewrite changed -/

/-- Closes what the rewrite needs of its operands, from the instructions that compute them: bytes below 16, and
scales repeated in pairs. Each lemma is tried only where its conclusion matches without unfolding, so a wrong
guess fails at once. -/
syntax "vnni_facts" : tactic
macro_rules
  | `(tactic| vnni_facts) =>
    `(tactic| repeat' (first
      | with_reducible exact nibbles_poison
      | with_reducible exact lows_poison
      | with_reducible exact sames_poison
      | with_reducible apply nibbles_split
      | with_reducible apply nibbles_split2
      | with_reducible apply nibbles_shuffle
      | with_reducible apply lows_shuffle
      | with_reducible apply lows16_shuffle
      | with_reducible apply lows_and
      | with_reducible apply lows16_and
      | with_reducible apply sames_shuffle
      | with_reducible apply same_join
      | with_reducible apply pairs_split
      | with_reducible apply pairs_map
      | with_reducible apply pairs_shuffle
      | with_reducible rfl
      | decide))

/-- The chain of `step`s down to `base`, leaving what each needs of its operands as goals. -/
syntax "vnni_inv" : tactic
macro_rules
  | `(tactic| vnni_inv) => `(tactic| first | (refine base ?_ ?_ ?_) | (refine step ?_ ?_ ?_; vnni_inv))

/-- Proves a rewritten slice equal to clang's: runs both blocks, then `final`, the chain, and the facts. -/
syntax "vnni_slice " ident ident ident ident : tactic
macro_rules
  | `(tactic| vnni_slice $tgt $src $tgtStep $srcStep) =>
    `(tactic| (
      unfold $tgt:ident $src:ident
      rw [run, run]
      simp only [$tgtStep:ident, $srcStep:ident, ret, Outcome.ok]
      refine congrArg (fun x => some (Except.ok x)) ?_
      refine final (k := 8) ?_ (by decide) ?_ ?_
      vnni_inv
      all_goals vnni_facts))

end Llama.Vnni
