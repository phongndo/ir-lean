import Peephole.Term

/-! # LLVM's matchers, from `llvm/include/llvm/IR/PatternMatch.h` at `llvmorg-23.1.3`

Each is a function on `Term`, answering what the C++ matcher answers on a scalar integer operand: whether it matches,
and what it binds. Vectors, splats and constant expressions aren't representable, so nothing here is about them.

- A matcher on an instruction, such as `m_Add`, matches only an instruction with that opcode, operand 0 then operand 1.
  The commutative ones, `m_c_Add` and the like, try both orders, operand 0 first.
- `m_Specific(V)` compares addresses: `specific`.
- `m_APInt`, and the predicates on constants such as `m_Zero` and `m_Power2`, match a `ConstantInt` only. Poison and
  `undef` aren't `ConstantInt`s. The variants that allow poison lanes, such as `m_APIntAllowPoison`, are the same on a
  scalar.

The theorems at the end say what each match tells a proof about the operand's value. -/

namespace Peephole

open IRLean

variable {w : Nat}

/-- `m_Specific(S)` on `V`: the same pointer. -/
def specific (s v : Term w) : Bool := v.ident == s.ident

/-- `m_APInt(C)`, and `m_ConstantInt`: a `ConstantInt`, binding its value. -/
def apint : Term w → Option (BitVec w)
  | .const c => some c
  | _ => none

/-- `cst_pred_ty<P>`: a `ConstantInt` whose value satisfies `P`. -/
def cst (p : BitVec w → Bool) (t : Term w) : Bool :=
  match apint t with
  | some c => p c
  | none => false

/-- `m_Zero()` and `m_ZeroInt()`, which are the same on a scalar integer. -/
def zero : Term w → Bool := cst (· == 0#w)
/-- `m_One()`. -/
def one : Term w → Bool := cst (· == 1#w)
/-- `m_AllOnes()`. -/
def allOnes : Term w → Bool := cst (· == BitVec.allOnes w)
/-- `m_SignMask()`: only the sign bit set. -/
def signMask : Term w → Bool := cst (· == BitVec.intMin w)
/-- `m_Power2()`: `APInt::isPowerOf2`, one bit set. -/
def power2 : Term w → Bool := cst fun c => c.toNat.isPowerOfTwo
/-- `m_Negative()`: the sign bit set. -/
def negative : Term w → Bool := cst (·.msb)

/-- `isa<PoisonValue>`. -/
def isPoison : Term w → Bool
  | .poison => true
  | _ => false

/-- `m_Undef()` and `SimplifyQuery::isUndefValue` with `CanUseUndef` true, as InstSimplify's queries have it: `undef`
or poison. -/
def isUndefValue : Term w → Bool
  | .undef | .poison => true
  | _ => false

/-- A binary operator with opcode `op`: its flags and operands. -/
def binop? (op : BinOp) : Term w → Option (Flags × Term w × Term w)
  | .bin _ op' f a b => if op' = op then some (f, a, b) else none
  | _ => none

/-- `m_Not(V)`, which is `m_c_Xor(m_AllOnes(), V)`: an `xor` whose operand 0 is all ones and operand 1 matches `p`, or
the other way round, operand 0 tried first. -/
def notWith (p : Term w → Bool) (t : Term w) : Bool :=
  match binop? .xor t with
  | some (_, a, b) => (allOnes a && p b) || (allOnes b && p a)
  | none => false

/-- `m_Not(m_Value(X))`, binding `X`: operand 1 if operand 0 is all ones, else operand 0 if operand 1 is. -/
def not? (t : Term w) : Option (Term w) :=
  match binop? .xor t with
  | some (_, a, b) => if allOnes a then some b else if allOnes b then some a else none
  | none => none

/-- `m_Neg(V)`: `sub 0, V`, binding `V`. -/
def neg? (t : Term w) : Option (Term w) :=
  match binop? .sub t with
  | some (_, a, b) => if zero a then some b else none
  | none => none

/-! ### What a match says about values -/

theorem apint_denote {ρ : Env} {t : Term w} {c : BitVec w} (h : apint t = some c) : t.denote ρ = some c := by
  cases t <;> simp_all [apint, Term.denote]

theorem cst_denote {ρ : Env} {p : BitVec w → Bool} {t : Term w} (h : cst p t = true) :
    ∃ c, p c = true ∧ t.denote ρ = some c := by
  unfold cst at h
  split at h
  · next c hc => exact ⟨c, h, apint_denote hc⟩
  · cases h

theorem specific_denote {ρ : Env} {s t : Term w} (h : specific s t = true) : t.denote ρ = s.denote ρ :=
  Term.denote_of_ident (by simpa [specific] using h)

theorem binop?_eq {t : Term w} {op : BinOp} {f : Flags} {a b : Term w} (h : binop? op t = some (f, a, b)) :
    ∃ id, t = .bin id op f a b := by
  cases t <;> simp [binop?] at h
  next id op' f' a' b' =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨id, rfl⟩

/-- A matched binary operator's operands are consistent, and its value is its operation on theirs. -/
theorem binop?_consistent {ρ : Env} {t : Term w} {op : BinOp} {f : Flags} {a b : Term w}
    (h : binop? op t = some (f, a, b)) (hc : t.Consistent ρ) :
    a.Consistent ρ ∧ b.Consistent ρ ∧ op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (t.denote ρ) := by
  obtain ⟨id, rfl⟩ := binop?_eq h
  simpa [Term.Consistent, Term.denote] using hc

/-- A matched binary operator's operands have no `undef` if it has none. -/
theorem binop?_noUndef {t : Term w} {op : BinOp} {f : Flags} {a b : Term w}
    (h : binop? op t = some (f, a, b)) (hu : t.hasUndef = false) : a.hasUndef = false ∧ b.hasUndef = false := by
  obtain ⟨id, rfl⟩ := binop?_eq h
  simpa [Term.hasUndef] using hu

theorem ok_inj {α : Type} {x y : α} (h : Outcome.ok x = Outcome.ok y) : x = y := by
  simpa [Outcome.ok] using h

/-- `isUndefValue` on an operand with no `undef` means it's poison. -/
theorem isUndefValue_denote {ρ : Env} {t : Term w} (h : isUndefValue t = true) (hu : t.hasUndef = false) :
    t.denote ρ = none := by
  cases t <;> simp_all [isUndefValue, Term.hasUndef, Term.denote]

theorem isPoison_denote {ρ : Env} {t : Term w} (h : isPoison t = true) : t.denote ρ = none := by
  cases t <;> simp_all [isPoison, Term.denote]

end Peephole
