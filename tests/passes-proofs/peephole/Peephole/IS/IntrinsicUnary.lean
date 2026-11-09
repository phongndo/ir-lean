import Peephole.IS.IntrinsicBase

/-! # InstSimplify's `simplifyUnaryIntrinsic`, and its rewrites of integer intrinsics for every input

`simplifyUnaryIntrinsic` is at `llvm/lib/Analysis/InstructionSimplify.cpp:6567-6679` at `llvmorg-23.1.3`.
`simplifyIntrinsic` calls it on an intrinsic of one operand. Of the intrinsics `Term` holds, those are `ctpop`,
`bitreverse` and `bswap`: `abs`, `ctlz` and `cttz` have their flag as a second operand, and go to
`simplifyBinaryIntrinsic`. This is its model on `Peephole.Term`, step by step in the C++'s order, for those three:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyUnaryIntrinsic.L6604` | `bswap(bswap(x))` to `x` |
| `IS.simplifyUnaryIntrinsic.L6609` | `bitreverse(bitreverse(x))` to `x` |
| `IS.simplifyUnaryIntrinsic.L6614` | `ctpop(x)` to 1, where `isKnownToBeAPowerOfTwo(x, OrZero = false)` |
| `IS.simplifyUnaryIntrinsic.L6620` | `ctpop(x)` to `x`, where every bit but the lowest is known zero |

The function's other statements that can end it are for floating-point intrinsics, `vector.reverse` and
`structured.gep`: `isIdempotent` and `removesFPFraction` hold of none of the three, and its `switch` reaches only their
cases. Its steps say so where the C++ asks. -/

namespace Peephole.IS

open IRLean Intrinsic

variable {w : Nat}

/-! ### Helpers it calls -/

/-- `MaskedValueIsZero(V, Mask, Q)`: every bit of `Mask` is known zero, `Mask.isSubsetOf(Known.Zero)`. -/
def Intrinsic.maskedValueIsZero (o : Oracle) (v : Term w) (m : BitVec w) : Bool :=
  m &&& ~~~(o.knownZero v) == 0#w

/-- `APInt::getHighBitsSet(numBits, hiBitsSet)`: the top `hiBitsSet` bits set. -/
def Intrinsic.highBitsSet (w n : Nat) : BitVec w := BitVec.allOnes w <<< (w - n)

/-! ### The model -/

/-- `simplifyUnaryIntrinsic(IID, Op0, FMF, Q)`, step by step, for `ctpop`, `bitreverse` and `bswap`. -/
def simplifyUnaryIntrinsic.steps (o : Oracle) (f : UnIntr) (op0 : Term w) : List (Step w) :=
  [ -- Idempotent functions return the same result when called repeatedly. `isIdempotent` holds of `fabs`, the
    -- rounding intrinsics, `canonicalize` and `arithmetic_fence` only.
    .next,
    -- `removesFPFraction(IID)`: the rounding intrinsics only.
    .next,
    -- bswap(bswap(x)) -> x
    match f, op0 with
    | .bswap, .un _ .bswap x => .fire "IS.simplifyUnaryIntrinsic.L6604" (.old x)
    | _, _ => .next,
    -- bitreverse(bitreverse(x)) -> x
    match f, op0 with
    | .bitreverse, .un _ .bitreverse x => .fire "IS.simplifyUnaryIntrinsic.L6609" (.old x)
    | _, _ => .next,
    -- ctpop(X) -> 1 iff X is non-zero power of 2.
    if f == .ctpop && o.powerOfTwo false op0 then .fire "IS.simplifyUnaryIntrinsic.L6614" (.const 1#w)
    else .next,
    -- If everything but the lowest bit is zero, that bit is the pop-count. Ex:
    -- ctpop(and X, 1) --> and X, 1
    if f == .ctpop && maskedValueIsZero o op0 (highBitsSet w (w - 1)) then
      .fire "IS.simplifyUnaryIntrinsic.L6620" (.old op0)
    else .next ]

/-! ### The rewrites, one theorem each -/

/-- `IS.simplifyUnaryIntrinsic.L6604`: `bswap(bswap(x))` to `x`, at a width of whole bytes. LLVM's verifier requires an
even number of bytes of `bswap`, and IRLean's `bswap` is one only there. -/
theorem simplifyUnaryIntrinsic.L6604 (ρ : Env) (id : Nat) (x : Term w) (c0 : (Term.un id .bswap x).Consistent ρ)
    (hw : w % 8 = 0) :
    Refines ((Repl.un .bswap (.old (Term.un id .bswap x))).eval ρ) ((Repl.old x).eval ρ) := by
  rw [un_eval, un_denote c0]
  simp only [UnIntr.eval, Lemmas.bswap_bswap hw]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyUnaryIntrinsic.L6609`: `bitreverse(bitreverse(x))` to `x`. -/
theorem simplifyUnaryIntrinsic.L6609 (ρ : Env) (id : Nat) (x : Term w)
    (c0 : (Term.un id .bitreverse x).Consistent ρ) :
    Refines ((Repl.un .bitreverse (.old (Term.un id .bitreverse x))).eval ρ) ((Repl.old x).eval ρ) := by
  rw [un_eval, un_denote c0]
  simp only [UnIntr.eval, Lemmas.bitreverse_bitreverse]
  exact refines_ok (Refine.refl_val _)

/-- `IS.simplifyUnaryIntrinsic.L6614`: `ctpop(x)` to 1, where the analysis knows `x` is a power of two. -/
theorem simplifyUnaryIntrinsic.L6614 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 : Term w)
    (h : o.powerOfTwo false op0 = true) :
    Refines ((Repl.un .ctpop (.old op0)).eval ρ) ((Repl.const 1#w).eval ρ) := by
  rw [un_eval]
  refine refines_ok ?_
  cases hd : op0.denote ρ with
  | none => exact Refine.val_none _
  | some x =>
    rcases ho.powerOfTwo false op0 x h hd with hp | ⟨hf, -⟩
    · simp only [UnIntr.eval, Lemmas.ctpop_of_isPowerOfTwo hp]
      exact Refine.refl_val _
    · cases hf

theorem maskedValueIsZero_highBits {ρ : Env} {o : Oracle} (ho : o.Sound ρ) {v : Term w} {x : BitVec w}
    (h : maskedValueIsZero o v (highBitsSet w (w - 1)) = true) (hx : v.denote ρ = some x) :
    x &&& (BitVec.allOnes w <<< 1) = 0#w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_of_zero_length])
  · have hk := ho.knownZero v x hx
    simp only [maskedValueIsZero, highBitsSet, show w - (w - 1) = 1 by omega, beq_iff_eq] at h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 := congrArg (·.getLsbD i) h
    have h2 := congrArg (·.getLsbD i) hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true,
      Bool.true_and] at h1 h2 ⊢
    cases hm : (BitVec.allOnes w <<< 1).getLsbD i <;> cases hz : (o.knownZero v).getLsbD i <;> simp_all

/-- `IS.simplifyUnaryIntrinsic.L6620`: `ctpop(x)` to `x`, where every bit of `x` but the lowest is known zero. -/
theorem simplifyUnaryIntrinsic.L6620 (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (op0 : Term w)
    (h : maskedValueIsZero o op0 (highBitsSet w (w - 1)) = true) :
    Refines ((Repl.un .ctpop (.old op0)).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [un_eval]
  refine refines_ok ?_
  cases hd : op0.denote ρ with
  | none => exact Refine.val_none _
  | some x =>
    simp only [UnIntr.eval, Lemmas.ctpop_of_and_eq_zero (maskedValueIsZero_highBits ho h hd)]
    exact Refine.refl_val _

/-! ### The fold -/

/-- Every step of `simplifyUnaryIntrinsic` that fires is right, for a `bswap` at a width of whole bytes. -/
theorem simplifyUnaryIntrinsic.steps_sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (f : UnIntr) (op0 : Term w)
    (c0 : op0.Consistent ρ) (hw : f = .bswap → w % 8 = 0) :
    ∀ s r, Step.fire s r ∈ simplifyUnaryIntrinsic.steps o f op0 →
      Refines ((Repl.un f (.old op0)).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyUnaryIntrinsic.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · cases h
  · cases h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyUnaryIntrinsic.L6604 ρ _ _ c0 (hw rfl)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyUnaryIntrinsic.L6609 ρ _ _ c0
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hp⟩ := hc
    exact simplifyUnaryIntrinsic.L6614 ρ o ho op0 hp
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hm⟩ := hc
    exact simplifyUnaryIntrinsic.L6620 ρ o ho op0 hm

/-- Theorem 1 for `simplifyUnaryIntrinsic` on `ctpop`, `bitreverse` and `bswap`: every value the model returns refines
the call, at every width, for every operand, poison included, given the analyses are sound. A `bswap`'s width is whole
bytes, as LLVM's verifier requires. -/
theorem simplifyUnaryIntrinsic.sound (ρ : Env) (o : Oracle) (ho : o.Sound ρ) (f : UnIntr) (op0 : Term w)
    (c0 : op0.Consistent ρ) (hw : f = .bswap → w % 8 = 0) {r : Repl w}
    (h : run (simplifyUnaryIntrinsic.steps o f op0) = .value r) :
    Refines ((Repl.un f (.old op0)).eval ρ) (r.eval ρ) :=
  run_sound (simplifyUnaryIntrinsic.steps_sound ρ o ho f op0 c0 hw) h

end Peephole.IS
