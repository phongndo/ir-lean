import LLVMLean.Mem

/-! A kit for proofs about emitted code. `simp only [foo.step, llvm_val, ...]` runs a block on
values known not to be poison, leaving the arithmetic for `bv_decide` or `omega`. -/

namespace LLVMLean

namespace Val
variable {w v : Nat} (x y : BitVec w)

@[llvm_val] theorem add_some : add (some x) (some y) = some (x + y) := by simp [add]
@[llvm_val] theorem and_some : and (some x) (some y) = some (x &&& y) := rfl
@[llvm_val] theorem xor_some : xor (some x) (some y) = some (x ^^^ y) := rfl
@[llvm_val] theorem or_some : or (some x) (some y) = some (x ||| y) := by simp [or]
@[llvm_val] theorem zext_some : zext v (some x) = some (x.setWidth v) := by simp [zext]
@[llvm_val] theorem icmpEq_some : icmpEq (some x) (some y) = some (BitVec.ofBool (x == y)) := by
  simp [icmpEq, icmp]
@[llvm_val] theorem icmpNe_some : icmpNe (some x) (some y) = some (BitVec.ofBool (x != y)) := by
  simp [icmpNe, icmp]
@[llvm_val] theorem icmpUlt_some : icmpUlt (some x) (some y) = some (BitVec.ofBool (BitVec.ult x y)) := by
  simp [icmpUlt, icmp]
@[llvm_val] theorem icmpUgt_some : icmpUgt (some x) (some y) = some (BitVec.ofBool (BitVec.ult y x)) := by
  simp [icmpUgt, icmp]
@[llvm_val] theorem mul_some : mul (some x) (some y) = some (x * y) := by simp [mul]
@[llvm_val] theorem trunc_some : trunc v (some x) = some (x.setWidth v) := by simp [trunc]
@[llvm_val] theorem lshr_some (h : BitVec.ult y (BitVec.ofNat w w) = true) :
    lshr (some x) (some y) = some (x >>> y) := by
  simp only [lshr, shiftOk]
  simp [show (y < BitVec.ofNat w w) from by simpa [BitVec.ult, BitVec.lt_def] using h]

end Val

/-- A branch on a known condition. -/
@[llvm_val] theorem br_ofBool (p : Bool) (t e : β) :
    (br (some (BitVec.ofBool p)) t e : Outcome (Next β ρ)) = jump (if p = true then t else e) := by
  cases p <;> simp [br]

/-- A `select` on a known condition. -/
@[llvm_val] theorem select_ofBool [HasPoison α] (p : Bool) (t e : α) :
    select (some (BitVec.ofBool p)) t e = if p = true then t else e := by
  cases p <;> simp [select]

@[llvm_val] theorem andThen_ok (x : α) (k : α → Outcome β) : andThen (Outcome.ok x) k = k x := rfl

@[llvm_val] theorem noundef_some (x : τ) (k : Outcome α) : noundef (some x) k = k := rfl

/-- `select c x false`, which is how `&&` comes out of the optimizer. -/
theorem select_and (a b : Bool) :
    select (some (BitVec.ofBool a)) (some (BitVec.ofBool b)) (some 0#1) = some (BitVec.ofBool (a && b)) := by
  cases a <;> cases b <;> simp [select]

/-! ### Branch conditions, as facts about natural numbers that `omega` can use -/

theorem beq_toNat {w : Nat} (a b : BitVec w) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · simp [h]
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h, this]

theorem bne_toNat {w : Nat} (a b : BitVec w) : (a != b) = !decide (a.toNat = b.toNat) := by
  rw [bne, beq_toNat]

theorem ult_toNat {w : Nat} (a b : BitVec w) : BitVec.ult a b = decide (a.toNat < b.toNat) := rfl

/-- `L + c'`, where `c'` stands for `-c`. Keep `c'` a variable: given the literal, `omega` writes a
proof that the kernel runs out of memory checking. -/
theorem toNat_dec {L : BitVec 64} {c' : Nat} (c : Nat) (h : c' = 18446744073709551616 - c)
    (hc : c ≤ L.toNat) (hc0 : 0 < c) : (L + BitVec.ofNat 64 c').toNat = L.toNat - c := by
  have := L.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lshr_lit {x : BitVec 64} {k : Nat} (hk : k < 64) :
    Val.lshr (some x) (some (BitVec.ofNat 64 k)) = some (x >>> BitVec.ofNat 64 k) := by
  apply Val.lshr_some
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem run_jump (step : β → Outcome (Next β ρ)) {b b' : β} (h : step b = jump b') :
    run step b = run step b' := by
  rw [run, h]; rfl

theorem run_ret (step : β → Outcome (Next β ρ)) {b : β} {r : ρ} (h : step b = ret r) :
    run step b = Outcome.ok r := by
  rw [run, h]; rfl

/-! ### Reading a buffer -/

/-- `n` initialized bytes at offset `o` of allocation `block`, holding `data`. -/
structure Readable (m : Mem) (block o n : Nat) (data : Nat → BitVec 8) : Prop where
  alloc : ∃ a : Alloc, m.allocs block = some a ∧ o + n ≤ a.size ∧ a.size < 2 ^ 64 ∧
    ∀ i, i < n → a.bytes (o + i) = .val (data i)

/-- The pointer `i` bytes into a buffer. -/
abbrev bufPtr (block o i : Nat) : Ptr := ⟨block, BitVec.ofNat 64 (o + i)⟩

namespace Readable

variable {m : Mem} {block o n : Nat} {data : Nat → BitVec 8}

theorem load (B : Readable m block o n data) {i : Nat} (h : i < n) :
    Mem.loadInt 8 m (some (bufPtr block o i)) 1 = Outcome.ok (some (data i)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have hlt : o + i < 2 ^ 64 := by omega
  have hb := hd i h
  have off : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlt
  have fits : ¬ o + i + 8 / 8 > a.size := by omega
  simp [Mem.loadInt, Mem.access, ha, Mem.read, Mem.collect, bufPtr, off, fits, hb, Outcome.ok]

theorem gep (B : Readable m block o n data) {i k : Nat} (h : i + k ≤ n) :
    Mem.gep m (some (bufPtr block o i)) (some (BitVec.ofNat 64 k)) (inbounds := true) (nuw := true) =
      some (bufPtr block o (i + k)) := by
  obtain ⟨a, ha, hsz, hmax, hd⟩ := B.alloc
  have hlt : o + i + k < 2 ^ 64 := by omega
  have hoff : BitVec.ofNat 64 (o + i) + BitVec.ofNat 64 k = BitVec.ofNat 64 (o + (i + k)) := by
    rw [← Nat.add_assoc]; simp [BitVec.ofNat_add]
  have hno : BitVec.uaddOverflow (BitVec.ofNat 64 (o + i)) (BitVec.ofNat 64 k) = false := by
    have h1 : (BitVec.ofNat 64 (o + i)).toNat = o + i := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : (BitVec.ofNat 64 k).toNat = k := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    simp only [BitVec.uaddOverflow, h1, h2]
    simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
    omega
  have hin : (o + (i + k)) % 18446744073709551616 ≤ a.size := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [Mem.gep, hno, Bool.true_and]
  by_cases h0 : BitVec.ofNat 64 k = 0#64
  · have : k = 0 := by
      have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    subst this
    simp [bufPtr]
  · simp [h0, ha, bufPtr, hoff, hin]

/-- The same, for a `getelementptr` with no flags, which can't fail. -/
theorem gep_plain (m : Mem) (block o i k : Nat) :
    Mem.gep m (some (bufPtr block o i)) (some (BitVec.ofNat 64 k)) =
      some (bufPtr block o (i + k)) := by
  have hoff : BitVec.ofNat 64 (o + i) + BitVec.ofNat 64 k = BitVec.ofNat 64 (o + (i + k)) := by
    rw [← Nat.add_assoc]; simp [BitVec.ofNat_add]
  simp [Mem.gep, bufPtr, hoff]

end Readable

end LLVMLean
