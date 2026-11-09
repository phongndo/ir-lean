import IRLean
import MultiIRExample

/-! # PROTOTYPE: one example, two compilers' IRs

Research only. This isn't part of the `IRLean` library, `lake build` doesn't build it, CI doesn't run it, and
nothing here is a claim in `docs/status.md`. `docs/multi-ir.md` says what it's for, and
`prototypes/multi-ir/check.sh` checks it.

`MultiIRExample` is what `build/ir-lean` prints for clang's `-O2` IR of `example.c`, so the LLVM side is
real emitter output. The GIMPLE side is transcribed by hand from GCC 16.2's `-fdump-tree-optimized-gimple`,
kept in `example.gimple`, because there's no GIMPLE reader. Nothing checks that transcription, so it's
trusted, and that's the gap a GIMPLE reader would close.

It asks two things of the existing design:

1. **What carries over.** Blocks as data, a `step` function, and a driver that loops over it. The GIMPLE
   functions below use `IRLean.Next` unchanged, and a copy of `IRLean.run` whose only change is that the
   reasons for stopping are a parameter.
2. **What doesn't.** `Val` and its poison. GIMPLE has no poison, and signed overflow there is undefined at
   the operation, so `Val.add (nsw := true)` would give GIMPLE less undefined behavior than it has.
-/

namespace MultiIR
open IRLean

/-! ## The part that carries over -/

/-- `IRLean.Outcome` with the reasons for stopping left open, so another IR can bring its own. -/
abbrev Result (ε α : Type) := Option (Except ε α)

/-- `IRLean.Outcome` is this at `IRLean.Stop`, so generalizing `run` this way wouldn't change any LLVM
statement. -/
example (α : Type) : Outcome α = Result Stop α := rfl

/-- `IRLean.run`, with the reasons for stopping as a parameter. The body is the same. -/
def runWith {ε β ρ : Type} (step : β → Result ε (Next β ρ)) (b : β) : Result ε ρ :=
  match step b with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok (.ret r)) => some (.ok r)
  | some (.ok (.jump next)) => runWith step next
partial_fixpoint

/-! `run_jump` and `run_ret` in `IRLean/Lemmas.lean`, once more, since those are stated at `IRLean.Stop`. -/

theorem runWith_jump {step : β → Result ε (Next β ρ)} (b b' : β) (h : step b = some (.ok (.jump b'))) :
    runWith step b = runWith step b' := by
  rw [runWith, h]

theorem runWith_ret {step : β → Result ε (Next β ρ)} (b : β) {r : ρ} (h : step b = some (.ok (.ret r))) :
    runWith step b = some (.ok r) := by
  rw [runWith, h]

theorem runWith_error {step : β → Result ε (Next β ρ)} (b : β) {e : ε} (h : step b = some (.error e)) :
    runWith step b = some (.error e) := by
  rw [runWith, h]

/-! ## A spec, shared by both

Copied from `tests/proofs/Popcount.lean`, which can't be imported here since it imports generated code. It
says nothing about either IR, which is the point: specs are the layer that's already reusable. -/

/-- The number of set bits, as a formula with no loop. -/
def pop (x : BitVec 32) : BitVec 32 :=
  let a := x - ((x >>> 1) &&& 0x55555555#32)
  let b := (a &&& 0x33333333#32) + ((a >>> 2) &&& 0x33333333#32)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f#32
  let d := c + (c >>> 8)
  (d + (d >>> 16)) &&& 0x3f#32

theorem pop_step (x : BitVec 32) : pop x = (x &&& 1#32) + pop (x >>> 1) := by
  simp only [pop]
  bv_decide

theorem pop_zero : pop 0#32 = 0#32 := by decide

theorem shift_lt {x : BitVec 32} (h : ¬x >>> 1 = 0#32) : (x >>> 1).toNat < x.toNat := by
  have : x ≠ 0#32 := by rintro rfl; simp at h
  have : 0 < x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) this
    · exact h0
  simp only [BitVec.toNat_ushiftRight]
  omega

/-! ## The part that doesn't: GIMPLE's own values and stops -/

namespace Gimple

/-- Why a GIMPLE run is undefined. Only what this example needs. -/
inductive UB where
  /-- `PLUS_EXPR` overflowing a type whose overflow is undefined (`TYPE_OVERFLOW_UNDEFINED`): a signed
  type, without `-fwrapv` or `-ftrapv`. -/
  | signedOverflow
  deriving DecidableEq, Repr

/-- Why the model stops instead of choosing. GCC hasn't settled these. -/
inductive ModelStop where
  /-- A shift by at least the precision. `tree.def` calls the result undefined, without saying whether
  that's undefined behavior. -/
  | wideShift
  deriving DecidableEq, Repr

/-- The same two kinds of stop as `IRLean.Stop`, with GIMPLE's reasons. -/
inductive Stop where
  | undefined (reason : UB)
  | model (reason : ModelStop)
  deriving DecidableEq, Repr

abbrev Outcome (α : Type) := Result Stop α

def ok (x : α) : Outcome α := some (.ok x)
def ub (reason : UB) : Outcome α := some (.error (.undefined reason))
def stop (reason : ModelStop) : Outcome α := some (.error (.model reason))

def andThen (x : Outcome α) (k : α → Outcome β) : Outcome β :=
  match x with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok a) => k a

def jump (b : β) : Outcome (Next β ρ) := ok (.jump b)
def ret (v : ρ) : Outcome (Next β ρ) := ok (.ret v)

/-- `if (c) goto t; else goto e;`. GIMPLE has no poison, so a condition is just a `Bool`. -/
def gotoIf (c : Bool) (t e : β) : Outcome (Next β ρ) := jump (if c then t else e)

/-- Signed `PLUS_EXPR`: undefined at the addition itself if it overflows. LLVM's `add nsw` would only give
poison here. -/
def plusSigned (a b : BitVec w) : Outcome (BitVec w) :=
  if a.saddOverflow b then ub .signedOverflow else ok (a + b)

/-- `RSHIFT_EXPR` on an unsigned type. Not used below, where the amount is the literal 1: a reader would
check a literal and print `>>>`. -/
def rshift (a n : BitVec w) : Outcome (BitVec w) :=
  if n.toNat < w then ok (a >>> n) else stop .wideShift

/-! ### `popcount`, from `example.gimple`

Blocks keep GCC's numbers. As in the LLVM emitter, each carries its PHI values and whatever it needs from
earlier blocks. GCC fed `x_4(D)` into `bb4`'s PHI on the edge where `x_4` is zero, where clang has 0. The
two are equal there, but not the same IR. -/

namespace popcount

inductive Block where
  | bb2 (x_4 : BitVec 32)
  | bb3 (x_10 c_11 : BitVec 32)
  | bb4 (c_12 : BitVec 32)

def step : Block → Outcome (Next Block (BitVec 32))
  | .bb2 x_4 => gotoIf (x_4 != 0#32) (.bb3 x_4 0#32) (.bb4 x_4)
  | .bb3 x_10 c_11 =>
    let _1 := x_10 &&& 1#32
    let c_6 := _1 + c_11
    let x_7 := x_10 >>> 1
    gotoIf (x_7 != 0#32) (.bb3 x_7 c_6) (.bb4 c_6)
  | .bb4 c_12 => ret c_12

end popcount

def popcount (x : BitVec 32) : Outcome (BitVec 32) := runWith popcount.step (.bb2 x)

/-! ### `pick`, from `example.gimple`, and two ways to hoist its addition -/

namespace pick

inductive Block where
  | bb2 (c_2 a_3 b_4 : BitVec 32)
  | bb3 (a_3 b_4 : BitVec 32)
  | bb4 (_1 : BitVec 32)

def step : Block → Outcome (Next Block (BitVec 32))
  | .bb2 c_2 a_3 b_4 => gotoIf (c_2 != 0#32) (.bb3 a_3 b_4) (.bb4 c_2)
  | .bb3 a_3 b_4 => andThen (plusSigned a_3 b_4) fun _5 => jump (.bb4 _5)
  | .bb4 _1 => ret _1

end pick

def pick (c a b : BitVec 32) : Outcome (BitVec 32) := runWith pick.step (.bb2 c a b)

/-- `pick` with its addition moved above the branch and left signed. GCC doesn't do this, since it isn't
valid in GIMPLE. -/
def pickHoistedSigned (c a b : BitVec 32) : Outcome (BitVec 32) :=
  andThen (plusSigned a b) fun s => ok (if c != 0#32 then s else 0#32)

/-- What GCC does when it hoists signed arithmetic (`rewrite_to_defined_unconditional`): the addition in
the unsigned type, converted back. The conversions don't change the bits, so that's a plain `+`. -/
def pickHoistedUnsigned (c a b : BitVec 32) : Outcome (BitVec 32) :=
  ok (if c != 0#32 then a + b else 0#32)

end Gimple

/-! ## Theorems -/

section Popcount

/-- The loop block, from any state. The proof follows `popcount_loop` in `tests/proofs/Popcount.lean`. -/
theorem gimple_popcount_loop (n : Nat) : ∀ (x c : BitVec 32), x.toNat = n →
    runWith Gimple.popcount.step (.bb3 x c) = Gimple.ok (c + pop x) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x c hx
    have hstep := pop_step x
    by_cases h : x >>> 1 = 0#32
    · have e : x &&& 1#32 = pop x := by rw [hstep, h, pop_zero]; simp
      rw [runWith_jump _ (Gimple.popcount.Block.bb4 ((x &&& 1#32) + c))
          (by simp [Gimple.popcount.step, Gimple.gotoIf, Gimple.jump, Gimple.ok, h]),
        runWith_ret (Gimple.popcount.Block.bb4 ((x &&& 1#32) + c)) rfl, e, BitVec.add_comm]
      rfl
    · have lt : (x >>> 1).toNat < n := by rw [← hx]; exact shift_lt h
      rw [runWith_jump _ (Gimple.popcount.Block.bb3 (x >>> 1) ((x &&& 1#32) + c))
          (by simp [Gimple.popcount.step, Gimple.gotoIf, Gimple.jump, Gimple.ok, h]),
        ih _ lt (x >>> 1) ((x &&& 1#32) + c) rfl, hstep, BitVec.add_comm (x &&& 1#32) c,
        BitVec.add_assoc]

/-- GCC's `popcount`, as transcribed: for every input it returns the bit count, with no undefined behavior,
and finishes. This is `popcount_correct` without the poison, since GIMPLE has none. -/
theorem gimple_popcount_correct (x : BitVec 32) : Gimple.popcount x = Gimple.ok (pop x) := by
  unfold Gimple.popcount
  by_cases h : x = 0#32
  · subst h
    rw [runWith_jump _ (Gimple.popcount.Block.bb4 0#32) rfl, runWith_ret (Gimple.popcount.Block.bb4 0#32) rfl, pop_zero]
    rfl
  · rw [runWith_jump _ (Gimple.popcount.Block.bb3 x 0#32)
        (by simp [Gimple.popcount.step, Gimple.gotoIf, Gimple.jump, Gimple.ok, h]),
      gimple_popcount_loop x.toNat x 0#32 rfl, BitVec.zero_add]

end Popcount

section Pick

/-- Clang's `pick`, as the emitter printed it. Clang moved the addition above the branch into a `select`, and
dropped `nsw` when it did, so it wraps. -/
theorem llvm_pick (c a b : BitVec 32) :
    MultiIRExample.pick (some c) (some a) (some b) =
      Outcome.ok (some (if c = 0#32 then 0#32 else b + a)) := by
  simp only [MultiIRExample.pick, noundef]
  rw [run]
  by_cases h : c = 0#32 <;> simp [MultiIRExample.pick.step, llvm, h]

/-- In LLVM, keeping `nsw` would have been fine too: the overflowing addition is poison, and `select` throws
it away when `c` is 0. -/
theorem llvm_hoisted_nsw_discards_poison :
    select (Val.icmpEq (some 0#32) (some 0#32)) (some 0#32)
      (Val.add (some 1#32) (some 0x7fffffff#32) (nsw := true)) = some 0#32 := by
  decide

/-- GCC's `pick`: 0 if `c` is 0, and otherwise the signed sum, which is undefined if it overflows. -/
theorem gimple_pick (c a b : BitVec 32) :
    Gimple.pick c a b = if c = 0#32 then Gimple.ok 0#32 else Gimple.plusSigned a b := by
  unfold Gimple.pick
  by_cases hc : c = 0#32
  · subst hc
    rw [runWith_jump _ (Gimple.pick.Block.bb4 0#32) rfl, runWith_ret (Gimple.pick.Block.bb4 0#32) rfl]
    rfl
  · rw [runWith_jump _ (Gimple.pick.Block.bb3 a b)
      (by simp [Gimple.pick.step, Gimple.gotoIf, Gimple.jump, Gimple.ok, hc])]
    by_cases ho : a.saddOverflow b
    · rw [runWith_error (Gimple.pick.Block.bb3 a b) (e := .undefined .signedOverflow)
        (by simp [Gimple.pick.step, Gimple.plusSigned, Gimple.andThen, Gimple.ub, ho])]
      simp [hc, Gimple.plusSigned, ho, Gimple.ub]
    · rw [runWith_jump _ (Gimple.pick.Block.bb4 (a + b))
          (by simp [Gimple.pick.step, Gimple.plusSigned, Gimple.andThen, Gimple.jump, Gimple.ok, ho]),
        runWith_ret (Gimple.pick.Block.bb4 (a + b)) rfl]
      simp [hc, Gimple.plusSigned, ho, Gimple.ok]

/-- In GIMPLE, hoisting the signed addition isn't a refinement: on this input GCC's `pick` returns 0, and the
hoisted one is undefined. -/
theorem gimple_hoisted_signed_adds_ub :
    Gimple.pick 0#32 0x7fffffff#32 1#32 = Gimple.ok 0#32 ∧
      Gimple.pickHoistedSigned 0#32 0x7fffffff#32 1#32 = Gimple.ub .signedOverflow :=
  ⟨by rw [gimple_pick]; rfl, rfl⟩

/-- GCC's way of hoisting it is a refinement: wherever `pick` returns, the hoisted version returns the same. -/
theorem gimple_hoisted_unsigned_refines (c a b r : BitVec 32) (h : Gimple.pick c a b = Gimple.ok r) :
    Gimple.pickHoistedUnsigned c a b = Gimple.ok r := by
  rw [gimple_pick] at h
  by_cases hc : c = 0#32
  · simp only [hc, ↓reduceIte, Gimple.ok, Option.some.injEq, Except.ok.injEq] at h
    subst h hc
    rfl
  · simp only [hc, ↓reduceIte, Gimple.plusSigned] at h
    split at h
    · simp [Gimple.ub, Gimple.ok] at h
    · simp only [Gimple.ok, Option.some.injEq, Except.ok.injEq] at h
      subst h
      simp [Gimple.pickHoistedUnsigned, hc]

/-- Clang's and GCC's outputs agree wherever GCC's is defined. This is about two compilers' IR in two models,
not about the C source. -/
theorem clang_does_what_gcc_does (c a b r : BitVec 32) (h : Gimple.pick c a b = Gimple.ok r) :
    MultiIRExample.pick (some c) (some a) (some b) = Outcome.ok (some r) := by
  rw [llvm_pick]
  rw [gimple_pick] at h
  by_cases hc : c = 0#32
  · simp only [hc, ↓reduceIte, Gimple.ok, Option.some.injEq, Except.ok.injEq] at h
    subst h hc
    rfl
  · simp only [hc, ↓reduceIte, Gimple.plusSigned] at h
    split at h
    · simp [Gimple.ub, Gimple.ok] at h
    · simp only [Gimple.ok, Option.some.injEq, Except.ok.injEq] at h
      subst h
      simp [hc, BitVec.add_comm]

/-- The other way fails: where GCC's output is undefined, clang's wraps. So neither model can stand in for
the other. -/
theorem gcc_undefined_where_clang_wraps :
    Gimple.pick 1#32 0x7fffffff#32 1#32 = Gimple.ub .signedOverflow ∧
      MultiIRExample.pick (some 1#32) (some 0x7fffffff#32) (some 1#32) =
        Outcome.ok (some 0x80000000#32) :=
  ⟨by rw [gimple_pick]; rfl, by rw [llvm_pick]; rfl⟩

end Pick

end MultiIR

#print axioms MultiIR.gimple_popcount_correct
#print axioms MultiIR.llvm_pick
#print axioms MultiIR.llvm_hoisted_nsw_discards_poison
#print axioms MultiIR.gimple_hoisted_signed_adds_ub
#print axioms MultiIR.gimple_hoisted_unsigned_refines
#print axioms MultiIR.clang_does_what_gcc_does
#print axioms MultiIR.gcc_undefined_where_clang_wraps
