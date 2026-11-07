import LlvmLEB128
import Kit

/-! LLVM's LEB128 decoder and encoder, from `llvm/Support/LEB128.h`, which read DWARF, wasm, and bitcode-adjacent formats. -/

set_option linter.unusedSimpArgs false

namespace Llvm.LEB128

open IRLean LlvmLEB128

/-- The low 7 bits of each byte, least significant first: what the first `i` bytes of an encoding are worth. -/
def sum (d : Nat → BitVec 8) : Nat → Nat
  | 0 => 0
  | i + 1 => sum d i + (d i &&& 127#8).toNat * 2 ^ (7 * i)

/-- An encoding with its last byte at `k`: that byte's top bit is clear, and all those before it have it set. -/
structure Encoded (d : Nat → BitVec 8) (k : Nat) : Prop where
  more : ∀ i, i < k → (d i).msb = true
  last : (d k).msb = false

abbrev effects : Effects := { other := .none, arg := .read, inaccessible := .none, errno := .none }

abbrev tag (m : Mem) : Tag := { call := m.nextCall, readonly := true, nofree := true, expires := true }

theorem slice_lt (b : BitVec 8) : (b &&& 127#8).toNat < 128 := by
  have h : b &&& 127#8 ≤ 127#8 := by bv_decide
  have h' : (b &&& 127#8).toNat ≤ 127 := h
  omega

variable {d : Nat → BitVec 8} {k : Nat}

theorem pow7 (i : Nat) : 2 ^ (7 * (i + 1)) = 128 * 2 ^ (7 * i) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- What's been added is below `2 ^ (7 * i)`. -/
theorem sum_lt (i : Nat) : sum d i < 2 ^ (7 * i) := by
  induction i with
  | zero => simp [sum]
  | succ i ih =>
    have hs := slice_lt (d i)
    rw [pow7]
    simp only [sum]
    have : (d i &&& 127#8).toNat * 2 ^ (7 * i) + 2 ^ (7 * i) ≤ 128 * 2 ^ (7 * i) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hs
    omega

/-- Later bytes can only add. -/
theorem sum_mono {i : Nat} (n : Nat) : sum d i ≤ sum d (i + n) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have : sum d (i + (n + 1)) = sum d (i + n) + (d (i + n) &&& 127#8).toNat * 2 ^ (7 * (i + n)) := rfl
    omega

section Run

variable {m : Mem} {t : List Tag} {block o N : Nat}

theorem value_toNat {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hx

/-- Adding a byte's slice in, while its shift is in range and nothing overflows. -/
theorem add_in_range {i : Nat} (hi : 7 * i < 64) {b : BitVec 8} {S : BitVec 32} (hS : S = BitVec.ofNat 32 (7 * i))
    (hfit : sum d i + (b &&& 127#8).toNat * 2 ^ (7 * i) < 2 ^ 64) :
    ((b &&& 127#8).setWidth 64 <<< BitVec.setWidth 64 S) + BitVec.ofNat 64 (sum d i) =
      BitVec.ofNat 64 (sum d i + (b &&& 127#8).toNat * 2 ^ (7 * i)) := by
  have hs := slice_lt b
  have hshift : (BitVec.setWidth 64 S).toNat = 7 * i := by
    subst hS
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hlow : ((b &&& 127#8).setWidth 64).toNat = (b &&& 127#8).toNat := by
    simp only [BitVec.toNat_setWidth, Nat.reducePow]
    exact Nat.mod_eq_of_lt (by omega)
  have hmul : (b &&& 127#8).toNat * 2 ^ (7 * i) < 2 ^ 64 := by omega
  have hsumlt : sum d i < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, value_toNat hsumlt, value_toNat hfit]
  show (((b &&& 127#8).setWidth 64 <<< (BitVec.setWidth 64 S).toNat).toNat + sum d i) % 2 ^ 64 = _
  rw [hshift, BitVec.toNat_shiftLeft, hlow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hmul, Nat.add_comm]
  exact Nat.mod_eq_of_lt hfit

/-- What a byte with a shift of at least 63 does, which is either nothing or an error. -/
theorem big_slice_ge {i : Nat} (hi : 9 ≤ i) {b : BitVec 8} (hb : i = 9 → 1#8 < b &&& 127#8) (hb' : i ≠ 9 → b &&& 127#8 ≠ 0#8) :
    2 ^ 64 ≤ (b &&& 127#8).toNat * 2 ^ (7 * i) := by
  have hpos : 2 ^ 63 ≤ 2 ^ (7 * i) := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases h9 : i = 9
  · subst h9
    have h2 : 1#8 < b &&& 127#8 := hb rfl
    have h2 : 2 ≤ (b &&& 127#8).toNat := h2
    calc 2 ^ 64 = 2 * 2 ^ 63 := by rfl
      _ ≤ (b &&& 127#8).toNat * 2 ^ (7 * 9) := Nat.mul_le_mul h2 (Nat.le_refl _)
  · have h1 : 1 ≤ (b &&& 127#8).toNat := by
      have h0 := hb' h9
      rcases Nat.eq_zero_or_pos (b &&& 127#8).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
      · exact h
    have : 2 ^ 64 ≤ 2 ^ (7 * i) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 2 ^ 64 ≤ 1 * 2 ^ (7 * i) := by omega
      _ ≤ _ := Nat.mul_le_mul h1 (Nat.le_refl _)

/-- Taking one more byte, and what comes of it. -/
theorem do_cond_run {P : Ptr} {S : BitVec 32} {W W1 : BitVec 64} {v : BitVec 8} {R : Val 64 × Mem}
    (hval : (if S.ult 64#32 = true then (v &&& 127#8).setWidth 64 <<< S.setWidth 64 else 0#64) + W = W1)
    (hmore : v.msb = true →
      run decodeuleb128.step (.do_body_i m (some P) (some S) (some W1)) = Outcome.ok R)
    (hdone : v.msb = false → R = (some W1, m)) :
    run decodeuleb128.step (.do_cond_i m (some P) (some S) (some W) (some v)
      (some ((v &&& 127#8).setWidth 64))) = Outcome.ok R := by
  have hs : v.slt 0#8 = v.msb := by bv_decide
  have finish : v.msb = false → run decodeuleb128.step
      (.do_cond_i__ZN4llvm13decodeULEB128EPKhPjS1_PPKc_exit_crit_edge m (some W1)) = Outcome.ok R := by
    intro hm
    rw [hdone hm]
    llvm_step decodeuleb128.step
    llvm_step decodeuleb128.step
  llvm_step decodeuleb128.step
  rw [hs, hval]
  apply ite_cases <;> intro hm'
  · exact hmore hm'
  · exact finish (by simpa using hm')

/-- Going on to the next byte. -/
theorem do_body_run {i : Nat} (B : Readable m t block o N d) (hi : i + 1 ≤ N) {W : BitVec 64} :
    run decodeuleb128.step (.do_body_i m (some (bufPtr t block o i)) (some (BitVec.ofNat 32 (7 * i))) (some W)) =
      run decodeuleb128.step (.if_end3_i m (some (bufPtr t block o (i + 1))) (some (BitVec.ofNat 32 (7 * (i + 1))))
        (some W)) := by
  have hS : BitVec.ofNat 32 (7 * i) + 7#32 = BitVec.ofNat 32 (7 * (i + 1)) := by
    rw [Nat.mul_succ, BitVec.ofNat_add]
  rw [run]
  simp only [decodeuleb128.step, B.gep hi, Val.add_some, hS, jump, Outcome.ok]

theorem result_big {i : Nat} (hi : i ≤ k) (h : 2 ^ 64 ≤ (d i &&& 127#8).toNat * 2 ^ (7 * i)) : ¬ sum d (k + 1) < 2 ^ 64 := by
  have h1 : sum d (i + 1) ≤ sum d (i + 1 + (k - i)) := sum_mono _
  have e : i + 1 + (k - i) = k + 1 := by omega
  rw [e] at h1
  have : sum d (i + 1) = sum d i + (d i &&& 127#8).toNat * 2 ^ (7 * i) := rfl
  omega

/-- The value after a byte that's in range: `Value + (slice << Shift)`. -/
theorem value_next {i : Nat} (hi : i ≤ 8 ∨ (i = 9 ∧ d i &&& 127#8 ≤ 1#8)) :
    sum d (i + 1) < 2 ^ 64 ∧
      (if (BitVec.ofNat 32 (7 * i)).ult 64#32 = true then
        (d i &&& 127#8).setWidth 64 <<< (BitVec.ofNat 32 (7 * i)).setWidth 64 else 0#64) + BitVec.ofNat 64 (sum d i) =
      BitVec.ofNat 64 (sum d (i + 1)) := by
  have hsl := slice_lt (d i)
  have hsum := sum_lt (d := d) i
  have hlt : sum d (i + 1) = sum d i + (d i &&& 127#8).toNat * 2 ^ (7 * i) := rfl
  have h7 : 7 * i < 64 := by omega
  have hfit : sum d (i + 1) < 2 ^ 64 := by
    rcases hi with hi | ⟨rfl, hs⟩
    · have hle : sum d (i + 1) < 2 ^ (7 * (i + 1)) := sum_lt (i + 1)
      have : 2 ^ (7 * (i + 1)) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · have hs' : (d 9 &&& 127#8).toNat ≤ 1 := hs
      have hm : (d 9 &&& 127#8).toNat * 2 ^ (7 * 9) ≤ 1 * 2 ^ (7 * 9) := Nat.mul_le_mul_right _ hs'
      have hsum' : sum d 9 < 2 ^ (7 * 9) := hsum
      rw [hlt]
      omega
  refine ⟨hfit, ?_⟩
  have hcond : (BitVec.ofNat 32 (7 * i)).ult 64#32 = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have := Nat.mod_eq_of_lt (show 7 * i < 4294967296 by omega)
    omega
  rw [hcond, ite_eq_left rfl, hlt]
  apply add_in_range h7 rfl
  rw [← hlt]
  exact hfit

/-- What a byte past a shift of 63 does, when it doesn't overflow: nothing. -/
theorem value_past {i : Nat} (hi : 10 ≤ i) (hb : d i &&& 127#8 = 0#8) (hi32 : 7 * i < 2 ^ 32) :
    (if (BitVec.ofNat 32 (7 * i)).ult 64#32 = true then
        (d i &&& 127#8).setWidth 64 <<< (BitVec.ofNat 32 (7 * i)).setWidth 64 else 0#64) + BitVec.ofNat 64 (sum d i) =
      BitVec.ofNat 64 (sum d (i + 1)) := by
  have hcond : ¬ (BitVec.ofNat 32 (7 * i)).ult 64#32 = true := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have := Nat.mod_eq_of_lt (show 7 * i < 4294967296 from hi32)
    omega
  have : sum d (i + 1) = sum d i := by
    show sum d i + (d i &&& 127#8).toNat * 2 ^ (7 * i) = _
    rw [hb]
    simp
  rw [ite_eq_right hcond, this]
  simp

/-- What the loop does from one byte, given what it does from the next. -/
theorem one_byte {i : Nat} (B : Readable m t block o N d) (E : Encoded d k) (hk : k < N) (hkbound : 7 * k < 2 ^ 32)
    (hik : i ≤ k) (hsum : sum d i < 2 ^ 64)
    (next : i < k → sum d (i + 1) < 2 ^ 64 →
      run decodeuleb128.step (.if_end3_i m (some (bufPtr t block o (i + 1))) (some (BitVec.ofNat 32 (7 * (i + 1))))
        (some (BitVec.ofNat 64 (sum d (i + 1))))) =
      Outcome.ok (some (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64), m)) :
    run decodeuleb128.step (.if_end3_i m (some (bufPtr t block o i)) (some (BitVec.ofNat 32 (7 * i)))
      (some (BitVec.ofNat 64 (sum d i)))) =
    Outcome.ok (some (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64), m) := by
  have hS : (BitVec.ofNat 32 (7 * i)).toNat = 7 * i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hload := B.load (i := i) (by omega)
  generalize hR : (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64) = R at *
  -- The next byte, or the end, once this one's value is in.
  have go : sum d (i + 1) < 2 ^ 64 →
      (if (BitVec.ofNat 32 (7 * i)).ult 64#32 = true then
        (d i &&& 127#8).setWidth 64 <<< (BitVec.ofNat 32 (7 * i)).setWidth 64 else 0#64) + BitVec.ofNat 64 (sum d i) =
        BitVec.ofNat 64 (sum d (i + 1)) →
      run decodeuleb128.step (.do_cond_i m (some (bufPtr t block o i)) (some (BitVec.ofNat 32 (7 * i)))
        (some (BitVec.ofNat 64 (sum d i))) (some (d i)) (some ((d i &&& 127#8).setWidth 64))) =
      Outcome.ok (some R, m) := by
    intro hfit hval
    apply do_cond_run hval
    · intro hm
      have hik' : i < k := by
        rcases Nat.lt_or_ge i k with h | h
        · exact h
        · have : i = k := by omega
          subst this
          rw [E.last] at hm
          contradiction
      rw [do_body_run B (by omega)]
      exact next hik' hfit
    · intro hm
      have hik' : i = k := by
        rcases Nat.lt_or_ge i k with h | h
        · rw [E.more i h] at hm
          contradiction
        · omega
      subst hik'
      rw [← hR, ite_eq_left hfit]
  by_cases hsmall : i ≤ 8
  · have hu : (62#32).ult (BitVec.ofNat 32 (7 * i)) = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      have := Nat.mod_eq_of_lt (show 7 * i < 4294967296 by omega)
      omega
    obtain ⟨hfit, hval⟩ := value_next (d := d) (i := i) (Or.inl hsmall)
    rw [run]
    simp (disch := first | bv_decide | omega) only [decodeuleb128.step, llvm_val, hload, hu, Val.icmpUgt, Val.icmp_ok,
      Val.zext_ok, jump, Outcome.ok, andThen_some, ite_false, Bool.false_eq_true]
    exact go hfit hval
  · have hu : (62#32).ult (BitVec.ofNat 32 (7 * i)) = true := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      have := Nat.mod_eq_of_lt (show 7 * i < 4294967296 by omega)
      omega
    rw [run]
    simp (disch := first | bv_decide | omega) only [decodeuleb128.step, llvm_val, hload, hu, Val.icmpUgt, Val.icmp_ok,
      Val.zext_ok, jump, Outcome.ok, andThen_some, ite_true]
    llvm_step decodeuleb128.step
    -- A value that doesn't fit: an error, so 0, whatever the rest of the encoding is.
    have hbad : 2 ^ 64 ≤ (d i &&& 127#8).toNat * 2 ^ (7 * i) →
        run decodeuleb128.step (._ZN4llvm13decodeULEB128EPKhPjS1_PPKc_exit m (some 0#64)) = Outcome.ok (some R, m) := by
      intro hb
      rw [← hR, ite_eq_right (result_big hik hb)]
      llvm_step decodeuleb128.step
    by_cases h9 : i = 9
    · subst h9
      have hS63 : (BitVec.ofNat 32 (7 * 9) == 63#32) = true := rfl
      simp only [hS63, br_ofBool, jump, Outcome.ok, ite_eq_left]
      rw [run_ite]
      apply ite_cases <;> intro hbig
      · have hlt : 1#8 < d 9 &&& 127#8 := by simpa [BitVec.lt_def, BitVec.ult] using hbig
        exact hbad (big_slice_ge (by omega) (fun _ => hlt) (fun h => absurd rfl h))
      · have hle : d 9 &&& 127#8 ≤ 1#8 := by bv_decide
        obtain ⟨hfit, hval⟩ := value_next (d := d) (i := 9) (Or.inr ⟨rfl, hle⟩)
        exact go hfit hval
    · have hS63 : (BitVec.ofNat 32 (7 * i) == 63#32) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e
        have := congrArg BitVec.toNat e
        simp only [hS] at this
        have h63 : (63#32).toNat = 63 := rfl
        omega
      simp only [hS63, Bool.false_eq_true, ite_false, br_ofBool, jump, Outcome.ok]
      rw [run_ite]
      apply ite_cases <;> intro hbig
      · have hne : d i &&& 127#8 ≠ 0#8 := by simpa using hbig
        exact hbad (big_slice_ge (by omega) (fun h => absurd h h9) (fun _ => hne))
      · have h0 : d i &&& 127#8 = 0#8 := by simpa using hbig
        have hsame : sum d (i + 1) = sum d i := by
          show sum d i + (d i &&& 127#8).toNat * 2 ^ (7 * i) = _
          rw [h0]
          simp
        exact go (by omega) (value_past (by omega) h0 (by omega))

/-- The loop, from byte `i` of an encoding whose last byte is `k`. -/
theorem loop (B : Readable m t block o N d) (E : Encoded d k) (hk : k < N) (hkbound : 7 * k < 2 ^ 32) :
    ∀ (n i : Nat), n = k - i → i ≤ k → sum d i < 2 ^ 64 →
      run decodeuleb128.step (.if_end3_i m (some (bufPtr t block o i)) (some (BitVec.ofNat 32 (7 * i)))
        (some (BitVec.ofNat 64 (sum d i)))) =
      Outcome.ok (some (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64), m) := by
  intro n
  induction n with
  | zero =>
    intro i hn hik hsum
    exact one_byte B E hk hkbound hik hsum (fun h => by omega)
  | succ n ih =>
    intro i hn hik hsum
    exact one_byte B E hk hkbound hik hsum (fun h h' => ih (i + 1) (by omega) (by omega) h')

end Run

/-- `llvm::decodeULEB128`, called with only a pointer. For an encoding in readable memory, ending at byte `k`, it gives what
the encoding is worth, or 0 if that doesn't fit in 64 bits. The shift counter is 32 bits, so this needs `7 * k < 2 ^ 32`. -/
theorem decodeuleb128_correct {m : Mem} {ts : List Tag} {block o N k : Nat} {d : Nat → BitVec 8}
    (B : Readable m ts block o N d) (E : Encoded d k) (hk : k < N) (hkbound : 7 * k < 2 ^ 32)
    (hnn : m.addr (bufPtr ts block o 0) ≠ 0#64) :
    decodeuleb128 (some (bufPtr ts block o 0)) m =
      Outcome.ok (some (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64), m.afterCall) := by
  have B' := B.enter (e := effects) (T := tag m) (Or.inl rfl) rfl rfl rfl rfl (Or.inl rfl)
  have hnn' : (m.inCall effects).addr (bufPtr (tag m :: ts) block o 0) ≠ 0#64 := hnn
  simp only [decodeuleb128, noundef_some, Mem.call, Mem.tag, Option.map]
  have hstart := loop B' E hk hkbound (k - 0) 0 rfl (by omega) (by simp [sum])
  simp only [Nat.mul_zero, sum] at hstart
  have hentry : run decodeuleb128.step (.entry (m.inCall effects) (some (bufPtr (tag m :: ts) block o 0))) =
      Outcome.ok (some (if sum d (k + 1) < 2 ^ 64 then BitVec.ofNat 64 (sum d (k + 1)) else 0#64), m.inCall effects) := by
    rw [run]
    simp only [decodeuleb128.step, B'.observeNull, Mem.toVal, Val.icmpEq_some, br_ofBool, jump, Outcome.ok]
    have hne : (Mem.addr (m.inCall effects) (bufPtr (tag m :: ts) block o 0) ==
        Mem.addr (m.inCall effects) Ptr.null) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e
      exact hnn' (e.trans rfl)
    simp only [hne, Bool.false_eq_true, ite_false]
    exact hstart
  rw [show run decodeuleb128.step _ = _ from hentry]
  rfl

/-- `llvm::decodeULEB128`'s hypotheses can all hold, on real bytes, and it gives the value LEB128's own example gives. -/
theorem decodeuleb128_check_value :
    let init : Array Nat := #[0xE5, 0x8E, 0x26]
    let m := LlvmLEB128.initial.addGlobal 100 init.size false init
    decodeuleb128 (some (bufPtr [] 100 0 0)) m = Outcome.ok (some 624485#64, m.afterCall) := by
  intro init m
  have B := Readable.ofGlobal LlvmLEB128.initial 100 init rfl (by decide) (by decide) (by decide)
  have E : Encoded (fun i => BitVec.ofNat 8 (init[i]?.getD 0)) 2 := by
    refine ⟨fun i hi => ?_, by decide⟩
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
  have hnn : m.addr (bufPtr [] 100 0 0) ≠ 0#64 := by decide
  rw [decodeuleb128_correct (k := 2) B E (by decide) (by decide) hnn]
  congr 3
  decide +kernel

end Llvm.LEB128
