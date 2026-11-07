import LlvmCRC
import Kit

/-! LLVM's own CRC-32 from `llvm/lib/Support/CRC.cpp`, as it's built without zlib, against RFC 1952's definition. -/

set_option linter.unusedSimpArgs false

namespace Llvm.CRC

open IRLean IRLean.Table LlvmCRC

/-- RFC 1952's inner loop: one bit of the reflected polynomial. -/
def bit (c : BitVec 32) : BitVec 32 :=
  if c &&& 1#32 = 1#32 then 0xEDB88320#32 ^^^ (c >>> 1#32) else c >>> 1#32

def steps : Nat → BitVec 32 → BitVec 32
  | 0, c => c
  | n + 1, c => steps n (bit c)

/-- RFC 1952's outer loop: a byte goes in, and eight bits come out. -/
def update (c : BitVec 32) (b : BitVec 8) : BitVec 32 := steps 8 (c ^^^ b.setWidth 32)

/-- The state after the first `i` bytes of `d`. -/
def spec (c0 : BitVec 32) (d : Nat → BitVec 8) : Nat → BitVec 32
  | 0 => c0
  | i + 1 => update (spec c0 d i) (d i)

/-! ### The table -/

/-- `bit` on natural numbers, which the kernel can run quickly. It's written with these functions because the kernel computes
them directly, and would otherwise work through their instances on every step. -/
def bitN (c : Nat) : Nat := Nat.xor (Nat.mul 3988292384 (Nat.mod c 2)) (Nat.div c 2)

def stepsN (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c) (fun _ ih c => ih (bitN c)) n

/-- Every byte of the table is what the bit steps give. -/
theorem table_bytes :
    g__ZL8CRCTable_init.toList = (List.range 256).flatMap fun e => bytes4 (stepsN 8 e) := by
  decide +kernel

theorem toNat_bit (c : BitVec 32) : (bit c).toNat = bitN c.toNat := by
  have hand : (c &&& 1#32 = 1#32) ↔ c.toNat % 2 = 1 := by
    rw [BitVec.toNat_eq, BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod c.toNat 1
    simp at this ⊢
    try omega
  have hb : bitN c.toNat = (3988292384 * (c.toNat % 2)) ^^^ (c.toNat / 2) := rfl
  by_cases h : c.toNat % 2 = 1
  · simp [bit, hb, hand, h, BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · have h0 : c.toNat % 2 = 0 := by omega
    simp [bit, hb, hand, h0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_steps (n : Nat) (c : BitVec 32) : (steps n c).toNat = stepsN n c.toNat := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    show (steps n (bit c)).toNat = stepsN n (bitN c.toNat)
    rw [ih, toNat_bit]

/-- Eight steps take in the low byte and shift the rest down, whatever the rest holds. -/
theorem round_word (x : BitVec 32) : (x >>> 8#32) ^^^ steps 8 (x &&& 255#32) = steps 8 x := by
  simp only [steps, bit]; bv_decide

/-- The table is in memory, untouched, where the code expects it. Every real layout meets the size limits: LangRef says no object
crosses the top of the address space, even one past its end. -/
structure Table (m : Mem) : Prop where
  here : m.allocs 1 = initial.allocs 1
  align : (m.base 1).toNat % 4 = 0
  fits : (m.base 1).toNat + 1024 < 2 ^ 64

variable {m : Mem} {t : List Tag} {block o : Nat} {d : Nat → BitVec 8}

/-- Reads the table entry for a state and a byte. -/
theorem table_read (T : Table m) (c : BitVec 32) (b : BitVec 8) :
    Mem.loadInt 32 m (Mem.gep m (some g__ZL8CRCTable)
        (some ((b ^^^ c.setWidth 8).setWidth 64 * 4#64)) (inbounds := true) (nuw := true)) 4 =
      Outcome.ok (some (steps 8 ((b ^^^ c.setWidth 8).setWidth 32))) := by
  generalize hz : b ^^^ c.setWidth 8 = z
  have hzN : (z.setWidth 64).toNat = z.toNat := by
    simp only [BitVec.toNat_setWidth, Nat.reducePow]; have := z.isLt; omega
  have hz32 : (z.setWidth 32).toNat = z.toNat := by
    simp only [BitVec.toNat_setWidth, Nat.reducePow]; have := z.isLt; omega
  have hmul : Val.mul (some (z.setWidth 64)) (some 4#64) (nuw := true) (nsw := true) = some (z.setWidth 64 * 4#64) := by
    apply Val.mul_ok
    bv_decide
  have hlt : stepsN 8 (z.setWidth 64).toNat < 4294967296 := by
    rw [hzN, ← hz32, ← toNat_steps]
    exact (steps 8 (z.setWidth 32)).isLt
  have hl : (g__ZL8CRCTable_init.toList.drop 0).take 1024 =
      (List.range 256).flatMap fun e => bytes4 (stepsN 8 e) := by
    rw [List.drop_zero, table_bytes]
    exact List.take_of_length_le (by rw [length_flatMap_range _ (fun e => length_bytes4 _)]; omega)
  have h := Table.load (m := m) (P := g__ZL8CRCTable) (s := 1024) (off := 0) (f := stepsN 8) (x := z.setWidth 64)
    T.here rfl rfl (by simp [g__ZL8CRCTable]) hl (by omega) (by omega) (by omega) T.align T.fits
    (by rw [hzN]; exact z.isLt) hlt
  rw [hmul] at h
  rw [h]
  congr 3
  apply BitVec.eq_of_toNat_eq
  rw [toNat_steps, hzN, hz32]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  rw [← hz32, ← toNat_steps]
  exact (steps 8 (z.setWidth 32)).isLt

/-- What a table read is for. -/
theorem table_step (c : BitVec 32) (b : BitVec 8) :
    steps 8 ((b ^^^ c.setWidth 8).setWidth 32) ^^^ (c >>> 8#32) = update c b := by
  have h := round_word (c ^^^ b.setWidth 32)
  have e1 : (c ^^^ b.setWidth 32) &&& 255#32 = (b ^^^ c.setWidth 8).setWidth 32 := by bv_decide
  have e2 : (c ^^^ b.setWidth 32) >>> 8#32 = c >>> 8#32 := by bv_decide
  rw [e1, e2, BitVec.xor_comm] at h
  exact h

/-- Two steps of the loop, which is where it compares pointers. -/
theorem body (B : Readable m t block o L d) (T : Table m) (hfree : ∀ x, x ∈ t → x.noAddress = false)
    {c0 : BitVec 32} {i : Nat} (hL : i + 2 ≤ L) :
    run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
      (.for_body m (some (spec c0 d i)) (some (bufPtr t block o i)) (some (bufPtr t block o L))) =
    if (m.addr (bufPtr t block o (i + 2)) == m.addr (bufPtr t block o L)) = true then
      run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step (.for_cond_cleanup_loopexit m (some (spec c0 d (i + 2))))
    else
      run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
        (.for_body m (some (spec c0 d (i + 2))) (some (bufPtr t block o (i + 2))) (some (bufPtr t block o L))) := by
  have e2 : ∀ c x, steps 8 ((x ^^^ c.setWidth 8).setWidth 32) ^^^ (c >>> 8#32) = update c x := table_step
  rw [run]
  llvm_simp [_ZN4llvm5crc32EjNS_8ArrayRefIhEE.step, B.load, B.gep, table_read T, e2, observe_free hfree, toVal_some, Val.icmp_ok]
  rfl

/-- What's left after the last two steps. -/
theorem body_end {c : BitVec 32} :
    run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step (.for_cond_cleanup_loopexit m (some c)) =
      Outcome.ok (some (c ^^^ 4294967295#32), m) := by
  llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
  llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step

/-- The loop, with `2 * n + 2` bytes to go. -/
theorem loop (B : Readable m t block o L d) (T : Table m) (hfree : ∀ x, x ∈ t → x.noAddress = false) (c0 : BitVec 32) (n : Nat) :
    ∀ i, L = i + 2 * (n + 1) →
      run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
        (.for_body m (some (spec c0 d i)) (some (bufPtr t block o i)) (some (bufPtr t block o L))) =
      Outcome.ok (some (spec c0 d L ^^^ 4294967295#32), m) := by
  induction n with
  | zero =>
    intro i hL
    rw [body B T hfree (by omega)]
    have hsame : L = i + 2 := by omega
    subst hsame
    simp [body_end]
  | succ n ih =>
    intro i hL
    rw [body B T hfree (by omega)]
    have hne : (m.addr (bufPtr t block o (i + 2)) == m.addr (bufPtr t block o L)) = false := by
      rw [beq_toNat, B.toNat_addr (i := i + 2) (by omega), B.toNat_addr (i := L) (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    simp only [hne, Bool.false_eq_true, ite_false]
    exact ih (i + 2) (by omega)

/-- How the code starts, for a buffer of `L` bytes: `spec` from the inverted CRC, and an odd byte first. -/
theorem from_start (B : Readable m t block o L d) (T : Table m) (hfree : ∀ x, x ∈ t → x.noAddress = false)
    (c : BitVec 32) (len : BitVec 64) (hlen : len.toNat = L) :
    run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step (.entry m (some c) (some (bufPtr t block o 0)) (some len)) =
      Outcome.ok (some (spec (c ^^^ 4294967295#32) d L ^^^ 4294967295#32), m) := by
  have hgep : Mem.gep m (some (bufPtr t block o 0)) (some len) (inbounds := true) (nuw := true) =
      some (bufPtr t block o L) := by
    have := B.gep (i := 0) (k := L) (by omega)
    rw [Nat.zero_add, ← hlen, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [← hlen]
    exact this
  have hmsb : len.msb = false := by
    obtain ⟨a, _, hsz, hmax, _⟩ := B.alloc
    have : len < 9223372036854775808#64 := by
      show len.toNat < _
      simp only [BitVec.toNat_ofNat]
      omega
    bv_decide
  have e2 : ∀ c x, steps 8 ((x ^^^ c.setWidth 8).setWidth 32) ^^^ (c >>> 8#32) = update c x := table_step
  by_cases h0 : len = 0#64
  · have hL0 : L = 0 := by rw [← hlen, h0]; rfl
    subst hL0
    subst h0
    llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
    have hc : spec (c ^^^ 4294967295#32) d 0 ^^^ 4294967295#32 = c := by
      show (c ^^^ 4294967295#32) ^^^ 4294967295#32 = c
      bv_decide
    rw [hc]
    llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
    simp only [beq_self_eq_true, ite_true]
  · have hLpos : 0 < L := by
      rw [← hlen]
      rcases Nat.eq_zero_or_pos len.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
      · exact h
    have hb0 : (len == 0#64) = false := by simpa using h0
    rw [run]
    llvm_simp [_ZN4llvm5crc32EjNS_8ArrayRefIhEE.step, hgep, hb0, Val.icmp_ok]
    have hand : (len &&& 1#64).toNat = len.toNat % 2 := by
      rw [BitVec.toNat_and]
      exact Nat.and_one_is_mod _
    llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
    apply ite_cases <;> intro heven
    · -- An even number of bytes: straight into the loop.
      have hL2 : L % 2 = 0 := by
        have h1 : len &&& 1#64 = 0#64 := by simpa using heven
        rw [h1] at hand
        rw [← hlen]
        simpa using hand.symm
      have hne : (len == 1#64) = false := by
        have h1 : len &&& 1#64 = 0#64 := by simpa using heven
        simp only [beq_eq_false_iff_ne, ne_eq]
        bv_decide
      llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
      simp only [hne, Bool.false_eq_true, ite_false]
      have := loop (d := d) B T hfree (c ^^^ 4294967295#32) (L / 2 - 1) 0 (by omega)
      exact this
    · -- An odd number: one byte first.
      have hL2 : L % 2 = 1 := by
        have h1 : len &&& 1#64 = 1#64 := by
          have : ¬ len &&& 1#64 = 0#64 := by simpa using heven
          bv_decide
        rw [h1] at hand
        rw [← hlen]
        simpa using hand.symm
      rw [run]
      llvm_simp [_ZN4llvm5crc32EjNS_8ArrayRefIhEE.step, B.load, B.gep, table_read T, e2, Val.icmp_ok]
      llvm_step _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step
      apply ite_cases <;> intro hone
      · have hL1 : L = 1 := by
          have h1 : len = 1#64 := by simpa using hone
          rw [← hlen, h1]
          rfl
        subst hL1
        exact body_end
      · have hL3 : 3 ≤ L := by
          have h1 : ¬ len = 1#64 := by simpa using hone
          have : L ≠ 1 := by
            intro e
            apply h1
            apply BitVec.eq_of_toNat_eq
            rw [hlen, e]
            rfl
          omega
        exact loop (d := d) B T hfree (c ^^^ 4294967295#32) ((L - 1) / 2 - 1) 1 (by omega)

abbrev effects : Effects := { other := .none, arg := .read, inaccessible := .none, errno := .none }

abbrev tag (m : Mem) : Tag := { call := m.nextCall, readonly := true, nofree := true, expires := true }

/-- `llvm::crc32(CRC, Data)`, for `len` readable bytes at any pointer whose address may be looked at: RFC 1952's CRC-32 of the
bytes, continuing from `crc`. -/
theorem crc32_correct {crc : BitVec 32} {len : BitVec 64} (B : Readable m t block o len.toNat d) (T : Table m)
    (hfree : ∀ x, x ∈ t → x.noAddress = false) :
    _ZN4llvm5crc32EjNS_8ArrayRefIhEE (some crc) (some (bufPtr t block o 0)) (some len) m =
      Outcome.ok (some (spec (crc ^^^ 4294967295#32) d len.toNat ^^^ 4294967295#32), m.afterCall) := by
  have B' := B.enter (e := effects) (T := tag m) (Or.inl rfl) rfl rfl rfl rfl (Or.inl rfl)
  have T' : Table (m.inCall effects) := ⟨T.here, T.align, T.fits⟩
  have hfree' : ∀ x, x ∈ tag m :: t → x.noAddress = false := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact hfree x hx
  have h := from_start (d := d) B' T' hfree' crc len rfl
  simp only [_ZN4llvm5crc32EjNS_8ArrayRefIhEE, noundef_some, Mem.call, Mem.tag, Option.map]
  rw [show run _ZN4llvm5crc32EjNS_8ArrayRefIhEE.step _ = _ from h]
  rfl

/-- The hypotheses can all hold at once, on real bytes, and it gives CRC-32's published check value for "123456789". -/
theorem crc32_check_value :
    let init : Array Nat := #[49, 50, 51, 52, 53, 54, 55, 56, 57]
    let m := LlvmCRC.initial.addGlobal 100 init.size false init
    _ZN4llvm5crc32EjNS_8ArrayRefIhEE (some 0#32) (some (bufPtr [] 100 0 0)) (some 9#64) m =
      Outcome.ok (some 0xCBF43926#32, m.afterCall) := by
  intro init m
  have B := Readable.ofGlobal LlvmCRC.initial 100 init rfl (by decide) (by decide) (by decide)
  have T : Table m := ⟨rfl, by decide, by decide⟩
  rw [crc32_correct (len := 9#64) B T (by simp)]
  congr 3
  decide +kernel

end Llvm.CRC
