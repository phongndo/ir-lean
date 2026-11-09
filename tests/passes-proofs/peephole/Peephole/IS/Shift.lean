import Peephole.IS.Add
import Peephole.IS.ShiftKnownBits
import Peephole.Lemmas.Shift
import IRLean.Generic.Bitwise

/-! # InstSimplify's shifts, and their rewrites for every input

`simplifyShift`, `simplifyRightShift`, `simplifyShlInst`, `simplifyLShrInst` and `simplifyAShrInst` are at
`llvm/lib/Analysis/InstructionSimplify.cpp:1269-1508` at `llvmorg-23.1.3`, with their helper `isPoisonShift`. This is
their model on `Peephole.Term`, step by step in the C++'s order. Each step that rewrites carries its ID from
`tests/llvm_scope/rewrites/instsimplify.json`, and each has a theorem of that name:

| ID | Rewrite |
| --- | --- |
| `IS.simplifyShift.L1310` | `poison` shifted by `X` to poison |
| `IS.simplifyShift.L1314` | 0 shifted by `X` to 0 |
| `IS.simplifyShift.L1322` | `X` shifted by 0, or by a `sext` of an `i1`, to `X` |
| `IS.simplifyShift.L1326` | `X` shifted by `undef`, poison, or a constant `w` or more, to poison |
| `IS.simplifyShift.L1344` | `X` shifted by an amount whose known ones are `w` or more, to poison |
| `IS.simplifyShift.L1350` | `X` shifted by an amount whose low `⌈log2 w⌉` bits are known 0, to `X` |
| `IS.simplifyShift.L1364` | `shl nsw X, A` to poison, where the known bits of the result and the sign bit of `X` conflict |
| `IS.simplifyRightShift.L1381` | `X >> X` to 0 |
| `IS.simplifyRightShift.L1386` | `undef >> X` to 0, or to `undef` if `exact` |
| `IS.simplifyRightShift.L1393` | `X >> A` with `exact` to `X`, where bit 0 of `X` is known 1 |
| `IS.simplifyShlInst.L1411` | `undef << X` to 0, or to `undef` with `nsw` or `nuw` |
| `IS.simplifyShlInst.L1417` | `(X >> A) << A`, the right shift `exact`, to `X` |
| `IS.simplifyShlInst.L1421` | `shl nuw C, X` to `C`, where `C` is negative |
| `IS.simplifyShlInst.L1430` | `shl nuw nsw X, w - 1` to 0 |
| `IS.simplifyLShrInst.L1451` | `lshr (shl nuw X, A), A` to `X` |
| `IS.simplifyLShrInst.L1466` | `lshr (or (shl nuw X, C), Y), C` to `X`, where `Y`'s known leading zeros leave it under `2 ^ C` |
| `IS.simplifyAShrInst.L1490` | `ashr -1, X` and `ashr (shl -1, X), X` to -1 |
| `IS.simplifyAShrInst.L1495` | `ashr (shl nsw X, A), A` to `X` |
| `IS.simplifyAShrInst.L1500` | `ashr X, A` to `X`, where `ComputeNumSignBits(X)` is the width |

`simplifyShlInst.sound`, `simplifyLShrInst.sound` and `simplifyAShrInst.sound` put them together: every value each
model returns refines the shift it replaces, at every width, flag set and recursion budget, poison included. Each
`onInst_sound` says the same of the instruction `onInst` is given.

What the model reads:

- `computeKnownBits` and `ComputeNumSignBits` are the core `Oracle`'s, and `KnownBits::shl` is modelled in
  `Peephole.IS.ShiftKnownBits`.
- `isa<PHINode>` can't be read off a `Term`, which shows a `phi` as `var`, as it does an argument. `Shift.Ext.phi` says
  which `var`s are `phi`s. It says nothing about values, so no theorem rests on it. `onInst` takes none: every `var`
  the comparison with `opt` builds is an argument.
- `Q.IIQ.UseInstrInfo` is true, as it is in the InstSimplify pass, so the flags of operand instructions are read.
- `threadBinOpOverSelect` and `threadBinOpOverPHI` call InstSimplify again, on the select's arms or the phi's incoming
  values: they're `.delegate`d, which claims nothing, unless `MaxRecurse` is 0, where they decline at once.
- Two constants are folded by the constant folder, at `IS.foldOrCommuteConstant.L582`, which is `.delegate`d too. -/

namespace Peephole.IS

open IRLean

variable {w : Nat}

namespace Shift

/-! ### What the model reads that `Term` and the core `Oracle` don't have -/

/-- What InstSimplify's shift, cast and `freeze` folds read that neither `Term` nor the core `Oracle` has. -/
structure Ext where
  /-- `isa<PHINode>(V)` of an instruction a `Term` shows as `var`, by its `id`. -/
  phi : Nat → Bool
  /-- `isGuaranteedNotToBeUndefOrPoison(V)`, which is stricter than `Oracle.notPoison`'s `isGuaranteedNotToBePoison`:
  it doesn't hold of `undef`. -/
  notUndefOrPoison : {w : Nat} → Term w → Bool

/-- Every answer `e` gives about values is true in the run `ρ`. Which instructions are `phi`s isn't about values. -/
structure Ext.Sound (e : Ext) (ρ : Env) : Prop where
  notUndefOrPoison : ∀ {w} (t : Term w), e.notUndefOrPoison t = true → t.denote ρ ≠ none

/-- What `onInst` reads: no `phi`s, and `isGuaranteedNotToBeUndefOrPoison` as the oracle answers
`isGuaranteedNotToBePoison`. The two differ on `undef`, which reads as poison here, so a sound answer of the one is
a sound answer of the other: `Ext.ofOracle_sound`. -/
def Ext.ofOracle (o : Oracle) : Ext where
  phi _ := false
  notUndefOrPoison t := o.notPoison t

theorem Ext.ofOracle_sound {o : Oracle} {ρ : Env} (ho : o.Sound ρ) : (Ext.ofOracle o).Sound ρ where
  notUndefOrPoison t h := ho.notPoison t h

/-! ### Matchers -/

/-- `isa<SelectInst>(V)`. -/
def isSelect : Term w → Bool
  | .select .. => true
  | _ => false

/-- `isa<PHINode>(V)`. -/
def isPhi (e : Ext) : Term w → Bool
  | .var id => e.phi id
  | _ => false

/-- `match(V, m_SExt(m_Value(X))) && X->getType()->isIntOrIntVectorTy(1)`: a `sext` of an `i1`. -/
def sextOfBool : Term w → Bool
  | .sext (v := v) _ _ => v == 1
  | _ => false

/-- `isPoisonShift(Amount, Q)` on a scalar: a constant that's `undef`, poison, or `w` or more. Its loop over a vector's
lanes doesn't apply. -/
def isPoisonShift (t : Term w) : Bool :=
  if !t.isConstant then false
  else if isUndefValue t then true
  else match apint t with
    | some c => decide (w ≤ c.toNat)
    | none => false

/-- `m_Exact(m_Shr(m_Value(X), m_Specific(A)))` on `V`, binding `X`: an `lshr exact` or `ashr exact` of `X` by `A`. -/
def exactShrOf (a v : Term w) : Option (Term w) :=
  match v with
  | .bin _ op f x b => if (op == .lshr || op == .ashr) && f.exact && specific a b then some x else none
  | _ => none

/-- `m_NUWShl(m_Value(X), m_Specific(A))` with `flag` `nuw`, and `m_NSWShl` with `flag` `nsw`, on `V`, binding `X`. -/
def shlOf (flag : Flags → Bool) (a v : Term w) : Option (Term w) :=
  match binop? .shl v with
  | some (f, x, b) => if flag f && specific a b then some x else none
  | none => none

/-- `m_Shl(m_AllOnes(), m_Specific(A))` on `V`. -/
def shlAllOnesOf (a v : Term w) : Bool :=
  match binop? .shl v with
  | some (_, x, b) => allOnes x && specific a b
  | none => false

/-- `m_NUWShl(m_Value(X), m_APInt(C))`, binding `X` and `C`. -/
def nuwShlConst (t : Term w) : Option (Term w × BitVec w) :=
  match binop? .shl t with
  | some (f, x, c) => if f.nuw then (apint c).map (x, ·) else none
  | none => none

/-- `m_c_Or(m_NUWShl(m_Value(X), m_APInt(C)), m_Value(Y))`, binding `X`, `C` and `Y`: the `shl` is tried as operand 0
first, and `m_Value` always matches the other. -/
def orNUWShl (t : Term w) : Option (Term w × BitVec w × Term w) :=
  match binop? .or t with
  | some (_, a, b) =>
    match nuwShlConst a with
    | some (x, c) => some (x, c, b)
    | none => (nuwShlConst b).map fun (x, c) => (x, c, a)
  | none => none

/-- Whether `shl nsw Op0, Op1` is poison by `simplifyShift`'s test: `KnownBits::shl` of the operands' known bits, with
the sign bit of `Op0`, if it's known, as the sign bit of the result, has a conflict. -/
def nswShlConflict (o : Oracle) (op0 op1 : Term w) : Bool :=
  let kv : KnownBits w := ⟨o.knownZero op0, o.knownOne op0⟩
  let ks := KnownBits.shl kv ⟨o.knownZero op1, o.knownOne op1⟩
  let z := if kv.zero.msb then ks.zero ||| BitVec.intMin w else ks.zero
  let one := if kv.one.msb then ks.one ||| BitVec.intMin w else ks.one
  KnownBits.hasConflict ⟨z, one⟩

end Shift

/-! ### The model -/

/-- `simplifyShift(Opcode, Op0, Op1, IsNSW, Q, MaxRecurse)`, step by step, for `Opcode` one of `shl`, `lshr` and
`ashr`. It never declines: its one `return nullptr` is its last statement, so a caller's steps follow its own, as
`if (Value *V = simplifyShift(...)) return V;` has them. Only the calls it delegates read `Opcode`. -/
def simplifyShift.steps (o : Oracle) (e : Shift.Ext) (_opc : BinOp) (op0 op1 : Term w) (isNSW : Bool)
    (maxRecurse : Nat) : List (Step w) :=
  [ -- foldOrCommuteConstant: two constants fold in the constant folder. A shift isn't commutative: nothing is swapped.
    if op0.isConstant && op1.isConstant then .delegate "ConstantFoldBinaryOpOperands" else .next,
    -- poison shift by X -> poison
    if isPoison op0 then .fire "IS.simplifyShift.L1310" (.old op0) else .next,
    -- 0 shift by X -> 0
    if zero op0 then .fire "IS.simplifyShift.L1314" (.const 0#w) else .next,
    -- X shift by 0 -> X
    -- Shift-by-sign-extended bool must be shift-by-0 because shift-by-all-ones would be poison.
    if zero op1 || Shift.sextOfBool op1 then .fire "IS.simplifyShift.L1322" (.old op0) else .next,
    -- Fold undefined shifts.
    if Shift.isPoisonShift op1 then .fire "IS.simplifyShift.L1326" .poison else .next,
    -- If the operation is with the result of a select instruction, check whether operating on either branch of the
    -- select always yields the same value. threadBinOpOverSelect returns nullptr at once if MaxRecurse is 0.
    if (Shift.isSelect op0 || Shift.isSelect op1) && maxRecurse != 0 then .delegate "threadBinOpOverSelect"
    else .next,
    -- If the operation is with the result of a phi instruction, check whether operating on all incoming values of the
    -- phi always yields the same value. threadBinOpOverPHI returns nullptr at once if MaxRecurse is 0.
    if (Shift.isPhi e op0 || Shift.isPhi e op1) && maxRecurse != 0 then .delegate "threadBinOpOverPHI" else .next,
    -- If any bits in the shift amount make that value greater than or equal to the number of bits in the type, the
    -- shift is undefined.
    if w ≤ (o.knownOne op1).toNat then .fire "IS.simplifyShift.L1344" .poison else .next,
    -- If all valid bits in the shift amount are known zero, the first operand is unchanged.
    if Shift.log2Ceil w ≤ Shift.countTrailingOnes (o.knownZero op1) then .fire "IS.simplifyShift.L1350" (.old op0)
    else .next,
    -- Check for nsw shl leading to a poison value.
    if isNSW && Shift.nswShlConflict o op0 op1 then .fire "IS.simplifyShift.L1364" .poison else .next ]

def simplifyShift (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w) (isNSW : Bool) (maxRecurse : Nat) :
    Result w :=
  run (simplifyShift.steps o e opc op0 op1 isNSW maxRecurse)

/-- The steps of `simplifyRightShift` after its call to `simplifyShift`. -/
def simplifyRightShift.own (o : Oracle) (op0 op1 : Term w) (isExact : Bool) : List (Step w) :=
  [ -- X >> X -> 0
    if specific op0 op1 then .fire "IS.simplifyRightShift.L1381" (.const 0#w) else .next,
    -- undef >> X -> 0
    -- undef >> X -> undef (if it's exact)
    if isUndefValue op0 then .fire "IS.simplifyRightShift.L1386" (if isExact then .old op0 else .const 0#w)
    else .next,
    -- The low bit cannot be shifted out of an exact shift if it is set.
    if isExact && (o.knownOne op0).getLsbD 0 then .fire "IS.simplifyRightShift.L1393" (.old op0) else .next ]

/-- `simplifyRightShift(Opcode, Op0, Op1, IsExact, Q, MaxRecurse)`, for `Opcode` one of `lshr` and `ashr`: first
`simplifyShift` with `IsNSW` false, then its own steps. It never declines either. -/
def simplifyRightShift.steps (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : List (Step w) :=
  simplifyShift.steps o e opc op0 op1 false maxRecurse ++ simplifyRightShift.own o op0 op1 isExact

def simplifyRightShift (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w) (isExact : Bool)
    (maxRecurse : Nat) : Result w :=
  run (simplifyRightShift.steps o e opc op0 op1 isExact maxRecurse)

/-- The steps of `simplifyShlInst` after its call to `simplifyShift`. -/
def simplifyShlInst.own (op0 op1 : Term w) (isNSW isNUW : Bool) : List (Step w) :=
  [ -- undef << X -> 0
    -- undef << X -> undef if (if it's NSW/NUW)
    if isUndefValue op0 then .fire "IS.simplifyShlInst.L1411" (if isNSW || isNUW then .old op0 else .const 0#w)
    else .next,
    -- (X >> A) << A -> X
    match Shift.exactShrOf op1 op0 with
    | some x => .fire "IS.simplifyShlInst.L1417" (.old x)
    | none => .next,
    -- shl nuw i8 C, %x  ->  C  iff C has sign bit set.
    if isNUW && negative op0 then .fire "IS.simplifyShlInst.L1421" (.old op0) else .next,
    -- "nuw" guarantees that only zeros are shifted out, and "nsw" guarantees that the sign-bit does not change, so the
    -- only input that does not produce poison is 0, and "0 << (bitwidth-1) --> 0".
    if isNSW && isNUW && cst (fun c => c.toNat == w - 1) op1 then .fire "IS.simplifyShlInst.L1430" (.const 0#w)
    else .next ]

/-- `simplifyShlInst(Op0, Op1, IsNSW, IsNUW, Q, MaxRecurse)`: `simplifyShift`, then its own steps. -/
def simplifyShlInst.steps (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isNSW isNUW : Bool) (maxRecurse : Nat) :
    List (Step w) :=
  simplifyShift.steps o e .shl op0 op1 isNSW maxRecurse ++ simplifyShlInst.own op0 op1 isNSW isNUW

def simplifyShlInst (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isNSW isNUW : Bool) (maxRecurse : Nat) :
    Result w :=
  run (simplifyShlInst.steps o e op0 op1 isNSW isNUW maxRecurse)

/-- The steps of `simplifyLShrInst` after its call to `simplifyRightShift`. -/
def simplifyLShrInst.own (o : Oracle) (op0 op1 : Term w) : List (Step w) :=
  [ -- (X << A) >> A -> X
    match Shift.shlOf (·.nuw) op1 op0 with
    | some x => .fire "IS.simplifyLShrInst.L1451" (.old x)
    | none => .next,
    -- ((X << A) | Y) >> A -> X  if effective width of Y is not larger than A.
    match apint op1, Shift.orNUWShl op0 with
    | some r, some (x, l, y) =>
      if r = l ∧ w - Shift.countLeadingOnes (o.knownZero y) ≤ r.toNat then .fire "IS.simplifyLShrInst.L1466" (.old x)
      else .next
    | _, _ => .next ]

/-- `simplifyLShrInst(Op0, Op1, IsExact, Q, MaxRecurse)`: `simplifyRightShift`, then its own steps. -/
def simplifyLShrInst.steps (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (maxRecurse : Nat) :
    List (Step w) :=
  simplifyRightShift.steps o e .lshr op0 op1 isExact maxRecurse ++ simplifyLShrInst.own o op0 op1

def simplifyLShrInst (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (maxRecurse : Nat) : Result w :=
  run (simplifyLShrInst.steps o e op0 op1 isExact maxRecurse)

/-- The steps of `simplifyAShrInst` after its call to `simplifyRightShift`. -/
def simplifyAShrInst.own (o : Oracle) (op0 op1 : Term w) : List (Step w) :=
  [ -- -1 >>a X --> -1
    -- (-1 << X) a>> X --> -1
    if allOnes op0 || Shift.shlAllOnesOf op1 op0 then .fire "IS.simplifyAShrInst.L1490" (.const (BitVec.allOnes w))
    else .next,
    -- (X << A) >> A -> X
    match Shift.shlOf (·.nsw) op1 op0 with
    | some x => .fire "IS.simplifyAShrInst.L1495" (.old x)
    | none => .next,
    -- Arithmetic shifting an all-sign-bit value is a no-op.
    if o.signBits op0 = w then .fire "IS.simplifyAShrInst.L1500" (.old op0) else .next ]

/-- `simplifyAShrInst(Op0, Op1, IsExact, Q, MaxRecurse)`: `simplifyRightShift`, then its own steps. -/
def simplifyAShrInst.steps (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (maxRecurse : Nat) :
    List (Step w) :=
  simplifyRightShift.steps o e .ashr op0 op1 isExact maxRecurse ++ simplifyAShrInst.own o op0 op1

def simplifyAShrInst (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (maxRecurse : Nat) : Result w :=
  run (simplifyAShrInst.steps o e op0 op1 isExact maxRecurse)

/-- What InstSimplify does with a `shl` it reaches: `simplifyInstructionWithOperands` calls `simplifyShlInst` with the
instruction's flags and `MaxRecurse` at `RecursionLimit`, 3. -/
def simplifyShlInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .shl f a b => simplifyShlInst o (Shift.Ext.ofOracle o) a b f.nsw f.nuw 3
  | _, _ => .null

/-- What InstSimplify does with an `lshr` it reaches. -/
def simplifyLShrInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .lshr f a b => simplifyLShrInst o (Shift.Ext.ofOracle o) a b f.exact 3
  | _, _ => .null

/-- What InstSimplify does with an `ashr` it reaches. -/
def simplifyAShrInst.onInst (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .ashr f a b => simplifyAShrInst o (Shift.Ext.ofOracle o) a b f.exact 3
  | _, _ => .null

/-! ### Forwarding: a callee's steps, then the caller's -/

namespace Shift

/-- When a list of steps that never declines comes first, a run answers what the first list does, unless that's
`nullptr`, and then what the rest does: `if (Value *V = callee(...)) return V;`. -/
theorem run_append_eq {A B : List (Step w)} (h : ∀ s ∈ A, s ≠ .decline) :
    run (A ++ B) = match run A with
      | .null => run B
      | r => r := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    have hA : ∀ s ∈ A, s ≠ .decline := fun s hs => h s (List.mem_cons_of_mem _ hs)
    cases a with
    | next => simpa [run] using ih hA
    | fire s r => rfl
    | decline => exact absurd rfl (h _ List.mem_cons_self)
    | delegate c => rfl

/-- When a run of two lists answers `r`, a step of the first fired `r`, or all of the first fell through and the second
answered `r`. -/
theorem run_append_value {A B : List (Step w)} {r : Repl w} (h : run (A ++ B) = .value r) :
    (∃ s, Step.fire s r ∈ A) ∨ ((∀ s ∈ A, s = .next) ∧ run B = .value r) := by
  induction A with
  | nil => exact Or.inr ⟨by simp, h⟩
  | cons a A ih =>
    cases a with
    | next =>
      rcases ih h with ⟨s, hs⟩ | ⟨hn, hb⟩
      · exact Or.inl ⟨s, List.mem_cons_of_mem _ hs⟩
      · exact Or.inr ⟨by simpa using hn, hb⟩
    | fire s r' =>
      simp only [List.cons_append, run, Result.value.injEq] at h
      subst h
      exact Or.inl ⟨s, List.mem_cons_self⟩
    | decline => simp [run] at h
    | delegate c => simp [run] at h

end Shift

theorem simplifyShift.steps_ne_decline (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w) (isNSW : Bool)
    (n : Nat) : ∀ s ∈ simplifyShift.steps o e opc op0 op1 isNSW n, s ≠ .decline := by
  intro s hs
  simp only [simplifyShift.steps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h <;> subst h <;> split <;> simp

theorem simplifyRightShift.steps_ne_decline (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w)
    (isExact : Bool) (n : Nat) : ∀ s ∈ simplifyRightShift.steps o e opc op0 op1 isExact n, s ≠ .decline := by
  intro s hs
  simp only [simplifyRightShift.steps, simplifyRightShift.own, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with h | h | h | h
  · exact simplifyShift.steps_ne_decline o e opc op0 op1 false n s h
  all_goals subst h; split <;> simp

/-- `simplifyRightShift` returns what `simplifyShift` does, unless that's `nullptr`. -/
theorem simplifyRightShift.forward (o : Oracle) (e : Shift.Ext) (opc : BinOp) (op0 op1 : Term w) (isExact : Bool)
    (n : Nat) : simplifyRightShift o e opc op0 op1 isExact n =
      match simplifyShift o e opc op0 op1 false n with
      | .null => run (simplifyRightShift.own o op0 op1 isExact)
      | r => r :=
  Shift.run_append_eq (simplifyShift.steps_ne_decline o e opc op0 op1 false n)

/-- `simplifyShlInst` returns what `simplifyShift` does, unless that's `nullptr`. -/
theorem simplifyShlInst.forward (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat) :
    simplifyShlInst o e op0 op1 isNSW isNUW n =
      match simplifyShift o e .shl op0 op1 isNSW n with
      | .null => run (simplifyShlInst.own op0 op1 isNSW isNUW)
      | r => r :=
  Shift.run_append_eq (simplifyShift.steps_ne_decline o e .shl op0 op1 isNSW n)

/-- `simplifyLShrInst` returns what `simplifyRightShift` does, unless that's `nullptr`. -/
theorem simplifyLShrInst.forward (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (n : Nat) :
    simplifyLShrInst o e op0 op1 isExact n =
      match simplifyRightShift o e .lshr op0 op1 isExact n with
      | .null => run (simplifyLShrInst.own o op0 op1)
      | r => r :=
  Shift.run_append_eq (simplifyRightShift.steps_ne_decline o e .lshr op0 op1 isExact n)

/-- `simplifyAShrInst` returns what `simplifyRightShift` does, unless that's `nullptr`. -/
theorem simplifyAShrInst.forward (o : Oracle) (e : Shift.Ext) (op0 op1 : Term w) (isExact : Bool) (n : Nat) :
    simplifyAShrInst o e op0 op1 isExact n =
      match simplifyRightShift o e .ashr op0 op1 isExact n with
      | .null => run (simplifyAShrInst.own o op0 op1)
      | r => r :=
  Shift.run_append_eq (simplifyRightShift.steps_ne_decline o e .ashr op0 op1 isExact n)

/-! ### Shifts as values -/

namespace Shift

/-- `opc` is a shift. -/
def IsShift (opc : BinOp) : Prop := opc = .shl ∨ opc = .lshr ∨ opc = .ashr

/-- The shift `opc`, with flags `f`, on two values: a shift is never undefined. -/
def shiftVal : BinOp → Flags → Val w → Val w → Val w
  | .shl, f, a, b => Val.shl a b f.nuw f.nsw
  | .lshr, f, a, b => Val.lshr a b f.exact
  | .ashr, f, a, b => Val.ashr a b f.exact
  | _, _, _, _ => none

/-- The shift `opc`, with flags `f`, that a fold replaces. -/
def shiftSrc (opc : BinOp) (f : Flags) (op0 op1 : Term w) : Repl w := .bin opc f (.old op0) (.old op1)

theorem shiftSrc_eval {opc : BinOp} (h : IsShift opc) (ρ : Env) (f : Flags) (op0 op1 : Term w) :
    (shiftSrc opc f op0 op1).eval ρ = Outcome.ok (shiftVal opc f (op0.denote ρ) (op1.denote ρ)) := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem shiftVal_none_left {opc : BinOp} (h : IsShift opc) (f : Flags) (b : Val w) : shiftVal opc f none b = none := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem shiftVal_none_right {opc : BinOp} (h : IsShift opc) (f : Flags) (a : Val w) :
    shiftVal opc f a none = none := by
  rcases h with rfl | rfl | rfl <;> cases a <;> rfl

theorem shiftVal_of_le {opc : BinOp} (h : IsShift opc) (f : Flags) (a : Val w) {y : BitVec w} (hy : w ≤ y.toNat) :
    shiftVal opc f a (some y) = none := by
  rcases h with rfl | rfl | rfl
  · exact Lemmas.shl_of_le_toNat a hy _ _
  · exact Lemmas.lshr_of_le_toNat a hy _
  · exact Lemmas.ashr_of_le_toNat a hy _

theorem shiftVal_zero_right_refines {opc : BinOp} (h : IsShift opc) (f : Flags) (a : Val w) :
    Refines (shiftVal opc f a (some 0#w)) a := by
  by_cases hw : w = 0
  · subst hw
    rw [shiftVal_of_le h f a (Nat.zero_le _)]
    exact Refine.val_none _
  · have hw : 0 < w := Nat.pos_of_ne_zero hw
    rcases h with rfl | rfl | rfl
    · simp only [shiftVal]; rw [Generic.shl_zero a _ _ hw]; exact Refine.refl_val _
    · simp only [shiftVal]; rw [Generic.lshr_zero a _ hw]; exact Refine.refl_val _
    · simp only [shiftVal]; rw [Generic.ashr_zero a _ hw]; exact Refine.refl_val _

theorem shiftVal_zero_left_refines {opc : BinOp} (h : IsShift opc) (f : Flags) (b : Val w) :
    Refines (shiftVal opc f (some 0#w) b) (some 0#w) := by
  rcases h with rfl | rfl | rfl
  · exact Lemmas.shl_zero_left_refines b _ _
  · exact Lemmas.lshr_zero_left_refines b _
  · exact Lemmas.ashr_zero_left_refines b _

theorem le_toNat_allOnes : w ≤ (BitVec.allOnes w).toNat := by
  have := Nat.lt_two_pow_self (n := w)
  rw [BitVec.toNat_allOnes]
  omega

theorem sextOfBool_denote {ρ : Env} {t : Term w} (h : sextOfBool t = true) (hc : t.Consistent ρ) :
    t.denote ρ = none ∨ t.denote ρ = some 0#w ∨ t.denote ρ = some (BitVec.allOnes w) := by
  cases t with
  | sext id a =>
    rename_i v
    simp only [sextOfBool, beq_iff_eq] at h
    subst h
    simp only [Term.Consistent] at hc
    simp only [Term.denote, ← hc.2, Val.sext, Val.map₁]
    split
    · next x _ =>
      rcases Lemmas.signExtend_of_width_one x w with h | h <;> simp [h]
    · simp
  | _ => simp [sextOfBool] at h

theorem isPoisonShift_denote {ρ : Env} {t : Term w} (h : isPoisonShift t = true) (hu : t.hasUndef = false) :
    t.denote ρ = none ∨ ∃ y, t.denote ρ = some y ∧ w ≤ y.toNat := by
  cases t with
  | const c => exact Or.inr ⟨c, rfl, by simpa [isPoisonShift, Term.isConstant, isUndefValue, apint] using h⟩
  | poison => exact Or.inl rfl
  | undef => simp [Term.hasUndef] at hu
  | _ => simp [isPoisonShift, Term.isConstant] at h

/-- Bits known 0 below `k` leave a value a multiple of `2 ^ k`. -/
theorem toNat_mod_eq_zero {y z : BitVec w} (h : y &&& z = 0#w) {k : Nat} (hz : ∀ j, j < k → z.getLsbD j = true) :
    y.toNat % 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have := congrArg (·.getLsbD j) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, Nat.zero_testBit]
  by_cases hj : j < k
  · simp_all
  · simp [hj]

theorem countWhile_go_le (p : Nat → Bool) (n : Nat) : ∀ i, i ≤ n → countWhile.go p n i ≤ n := by
  intro i
  induction i using countWhile.go.induct p n with
  | case1 i hi hp ih =>
    intro _
    rw [countWhile.go]
    simp only [hi, hp, ↓reduceIte]
    exact ih (by omega)
  | case2 i hi hp =>
    intro _
    rw [countWhile.go]
    simp only [hi, hp, Bool.false_eq_true, ↓reduceIte]
    omega
  | case3 i hi =>
    intro h
    rw [countWhile.go]
    simp only [hi, ↓reduceIte]
    exact h

theorem countLeadingOnes_le (z : BitVec w) : countLeadingOnes z ≤ w :=
  countWhile_go_le _ _ 0 (Nat.zero_le _)

/-- Bits known 0 from the top leave a value under `2 ^ (w - k)`. -/
theorem toNat_lt_of_and {y z : BitVec w} (h : y &&& z = 0#w) {k : Nat} (hk : k ≤ countLeadingOnes z) :
    y.toNat < 2 ^ (w - k) := by
  have hz := countWhile_spec hk
  have hkw : k ≤ w := Nat.le_trans hk (countLeadingOnes_le z)
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [BitVec.testBit_toNat]
  by_cases hiw : i < w
  · have h1 := hz (w - 1 - i) (by omega)
    rw [BitVec.getMsbD_eq_getLsbD] at h1
    simp only [show w - 1 - i < w by omega, decide_true, Bool.true_and, show w - 1 - (w - 1 - i) = i by omega] at h1
    have := congrArg (·.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, h1, Bool.and_true] at this
    exact this
  · exact BitVec.getLsbD_of_ge y i (by omega)

theorem and_intMin_of_msb_false {r : BitVec w} (h : r.msb = false) : r &&& BitVec.intMin w = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.msb_eq_getLsbD_last] at h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_intMin, BitVec.getLsbD_zero]
  by_cases hi' : i = w - 1
  · subst hi'; simp [h]
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega

theorem and_intMin_of_msb_true {r : BitVec w} (h : r.msb = true) : r &&& BitVec.intMin w = BitVec.intMin w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.msb_eq_getLsbD_last] at h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_intMin]
  by_cases hi' : i = w - 1
  · subst hi'; simp [h]
  · simp only [show ¬ i + 1 = w by omega, decide_false, Bool.and_false]

/-- With `nsw`, `simplifyShift`'s known bits of the result, the sign bit included, hold of a `shl` that isn't poison,
so they don't conflict. -/
theorem nswShlConflict_false {o : Oracle} {ρ : Env} (ho : o.Sound ρ) {op0 op1 : Term w} {x y : BitVec w}
    (hx : op0.denote ρ = some x) (hy : op1.denote ρ = some y) (hyw : y.toNat < w)
    (hs : (x <<< y.toNat).sshiftRight y.toNat = x) : nswShlConflict o op0 op1 = false := by
  have hkx : KnownBits.Holds ⟨o.knownZero op0, o.knownOne op0⟩ x := ⟨ho.knownZero op0 x hx, ho.knownOne op0 x hx⟩
  have hky : KnownBits.Holds ⟨o.knownZero op1, o.knownOne op1⟩ y := ⟨ho.knownZero op1 y hy, ho.knownOne op1 y hy⟩
  have hr := KnownBits.shl_holds hkx hky hyw
  have hmsb : (x <<< y.toNat).msb = x.msb := by
    conv => rhs; rw [← hs]
    rw [BitVec.msb_sshiftRight]
  unfold nswShlConflict
  apply KnownBits.hasConflict_eq_false (v := x <<< y.toNat)
  constructor
  · simp only
    split
    · next hz =>
      have : x.msb = false := by
        have := congrArg BitVec.msb hkx.1
        simp only [BitVec.msb_and, BitVec.msb_zero] at this
        simp_all
      rw [BitVec.and_or_distrib_left, hr.1, and_intMin_of_msb_false (by rw [hmsb, this]), BitVec.zero_or]
    · exact hr.1
  · simp only
    split
    · next ho1 =>
      have : x.msb = true := by
        have := congrArg BitVec.msb hkx.2
        simp only [BitVec.msb_and] at this
        simp_all
      rw [BitVec.and_or_distrib_left, hr.2, and_intMin_of_msb_true (by rw [hmsb, this])]
    · exact hr.2

theorem or_comm (a b : Val w) (d : Bool) : Val.or a b d = Val.or b a d := by
  cases a <;> cases b <;> simp [Val.or, BitVec.or_comm, BitVec.and_comm]

theorem or_none_left (b : Val w) (d : Bool) : Val.or none b d = none := rfl

theorem or_none_right (a : Val w) (d : Bool) : Val.or a none d = none := by
  cases a <;> rfl

theorem binop?_denote {ρ : Env} {t a b : Term w} {op : BinOp} {f : Flags} (h : binop? op t = some (f, a, b))
    (hc : t.Consistent ρ) : op.eval f (a.denote ρ) (b.denote ρ) = Outcome.ok (t.denote ρ) :=
  (binop?_consistent h hc).2.2

theorem shlOf_denote {ρ : Env} {flag : Flags → Bool} {a v x : Term w} (h : shlOf flag a v = some x)
    (hc : v.Consistent ρ) : ∃ f : Flags, flag f = true ∧ v.denote ρ = Val.shl (x.denote ρ) (a.denote ρ) f.nuw f.nsw := by
  unfold shlOf at h
  split at h
  · next f x' b hb =>
    split at h
    · next hf =>
      cases h
      simp only [Bool.and_eq_true] at hf
      refine ⟨f, hf.1, ?_⟩
      rw [← specific_denote hf.2]
      exact (ok_inj (binop?_denote hb hc)).symm
    · cases h
  · cases h

end Shift

/-! ### The rewrites, one theorem each -/

open Shift in
/-- `IS.simplifyShift.L1310`: `poison` shifted by `X` to poison. -/
theorem simplifyShift.L1310 (ρ : Env) {opc : BinOp} (hop : IsShift opc) (f : Flags) (op0 op1 : Term w)
    (h : isPoison op0 = true) : Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [shiftSrc_eval hop, isPoison_denote h, shiftVal_none_left hop]
  exact refines_ok (Refine.val_none _)

open Shift in
/-- `IS.simplifyShift.L1314`: 0 shifted by `X` to 0. -/
theorem simplifyShift.L1314 (ρ : Env) {opc : BinOp} (hop : IsShift opc) (f : Flags) (op0 op1 : Term w)
    (h : zero op0 = true) : Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [shiftSrc_eval hop, cst_eq h]
  exact refines_ok (shiftVal_zero_left_refines hop f _)

open Shift in
/-- `IS.simplifyShift.L1322`: `X` shifted by 0, or by a `sext` of an `i1`, which is 0 or all ones, to `X`. -/
theorem simplifyShift.L1322 (ρ : Env) {opc : BinOp} (hop : IsShift opc) (f : Flags) (op0 op1 : Term w)
    (c1 : op1.Consistent ρ) (h : (zero op1 || sextOfBool op1) = true) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [shiftSrc_eval hop, Repl.eval_old]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [cst_eq h]
    exact shiftVal_zero_right_refines hop f _
  · rcases sextOfBool_denote h c1 with hd | hd | hd <;> rw [hd]
    · rw [shiftVal_none_right hop]; exact Refine.val_none _
    · exact shiftVal_zero_right_refines hop f _
    · rw [shiftVal_of_le hop f _ le_toNat_allOnes]; exact Refine.val_none _

open Shift in
/-- `IS.simplifyShift.L1326`: `X` shifted by `undef`, poison, or a constant `w` or more, to poison. -/
theorem simplifyShift.L1326 (ρ : Env) {opc : BinOp} (hop : IsShift opc) (f : Flags) (op0 op1 : Term w)
    (u1 : op1.hasUndef = false) (h : isPoisonShift op1 = true) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [shiftSrc_eval hop]
  refine refines_ok ?_
  rcases isPoisonShift_denote h u1 with hd | ⟨y, hd, hy⟩ <;> rw [hd]
  · rw [shiftVal_none_right hop]; exact Refine.val_none _
  · rw [shiftVal_of_le hop f _ hy]; exact Refine.val_none _

open Shift in
/-- `IS.simplifyShift.L1344`: `X` shifted by an amount whose known ones make it `w` or more, to poison. -/
theorem simplifyShift.L1344 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) {opc : BinOp} (hop : IsShift opc) (f : Flags)
    (op0 op1 : Term w) (h : w ≤ (o.knownOne op1).toNat) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [shiftSrc_eval hop]
  refine refines_ok ?_
  cases hd : op1.denote ρ with
  | none => rw [shiftVal_none_right hop]; exact Refine.val_none _
  | some y =>
    have := KnownBits.toNat_le_of_and_eq (ho.knownOne op1 y hd)
    rw [shiftVal_of_le hop f _ (by omega)]
    exact Refine.val_none _

open Shift in
/-- `IS.simplifyShift.L1350`: `X` shifted by an amount whose low `⌈log2 w⌉` bits are known 0, to `X`: the amount is 0,
or at least `2 ^ ⌈log2 w⌉`, which is `w` or more. -/
theorem simplifyShift.L1350 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) {opc : BinOp} (hop : IsShift opc) (f : Flags)
    (op0 op1 : Term w) (h : log2Ceil w ≤ countTrailingOnes (o.knownZero op1)) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [shiftSrc_eval hop, Repl.eval_old]
  refine refines_ok ?_
  cases hd : op1.denote ρ with
  | none => rw [shiftVal_none_right hop]; exact Refine.val_none _
  | some y =>
    by_cases hw : w = 0
    · rw [shiftVal_of_le hop f _ (by omega)]; exact Refine.val_none _
    · have hmod := toNat_mod_eq_zero (ho.knownZero op1 y hd) (countWhile_spec h)
      have hpow := le_two_pow_log2Ceil hw
      by_cases hy : y.toNat < 2 ^ log2Ceil w
      · rw [Nat.mod_eq_of_lt hy] at hmod
        have : y = 0#w := BitVec.eq_of_toNat_eq (by simp [hmod])
        subst this
        exact shiftVal_zero_right_refines hop f _
      · rw [shiftVal_of_le hop f _ (by omega)]; exact Refine.val_none _

open Shift in
/-- `IS.simplifyShift.L1364`: `shl nsw X, A` to poison, where `KnownBits::shl` of the operands' known bits, with the
sign bit of `X` as the result's, conflicts: a `shl nsw` that isn't poison keeps the sign bit of `X`, and has the bits
`KnownBits::shl` says. -/
theorem simplifyShift.L1364 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (f : Flags) (hf : f.nsw = true)
    (op0 op1 : Term w) (h : nswShlConflict o op0 op1 = true) :
    Refines ((shiftSrc .shl f op0 op1).eval ρ) ((Repl.poison : Repl w).eval ρ) := by
  rw [shiftSrc_eval (Or.inl rfl)]
  refine refines_ok ?_
  suffices shiftVal .shl f (op0.denote ρ) (op1.denote ρ) = none by rw [this]; exact Refine.val_none _
  simp only [shiftVal, hf]
  cases hx : op0.denote ρ with
  | none => rfl
  | some x =>
  cases hy : op1.denote ρ with
  | none => rfl
  | some y =>
  simp only [Val.shl]
  split
  · rfl
  · next hok =>
    split
    · rfl
    · split
      · rfl
      · next hn =>
        exfalso
        have hyw : y.toNat < w := by simpa [Generic.shiftOk_iff] using hok
        simp only [Bool.true_and, bne_iff_ne, ne_eq, Decidable.not_not, BitVec.shiftLeft_eq',
          BitVec.sshiftRight_eq'] at hn
        rw [nswShlConflict_false ho hx hy hyw hn] at h
        cases h

theorem simplifyShift.steps_sound (o : Oracle) (e : Shift.Ext) (ρ : Env) {opc : BinOp} (hop : Shift.IsShift opc)
    (f : Flags) (op0 op1 : Term w) (isNSW : Bool) (n : Nat) (hnsw : isNSW = true → opc = .shl ∧ f.nsw = true)
    (ho : o.Sound ρ) (c1 : op1.Consistent ρ) (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyShift.steps o e opc op0 op1 isNSW n →
      Refines ((Shift.shiftSrc opc f op0 op1).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyShift.steps, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1310 ρ hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1314 ρ hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1322 ρ hop f op0 op1 c1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1326 ρ hop f op0 op1 u1 (by assumption)
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [reduceCtorEq] at h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1344 o ρ ho hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShift.L1350 o ρ ho hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨rfl, hf⟩ := hnsw hc.1
    exact simplifyShift.L1364 o ρ ho f hf op0 op1 hc.2

/-- Theorem 1 for `simplifyShift`: every value the model returns refines the shift it's given, `shl`, `lshr` or
`ashr`, with any flags, where `IsNSW` is only set with `nsw` on a `shl`. It rests on `Oracle.Sound`, and says nothing
about an amount that reaches an `undef`. -/
theorem simplifyShift.sound (o : Oracle) (e : Shift.Ext) (ρ : Env) {opc : BinOp} (hop : Shift.IsShift opc)
    (f : Flags) (op0 op1 : Term w) (isNSW : Bool) (n : Nat) (hnsw : isNSW = true → opc = .shl ∧ f.nsw = true)
    (ho : o.Sound ρ) (c1 : op1.Consistent ρ) (u1 : op1.hasUndef = false) {r : Repl w}
    (h : simplifyShift o e opc op0 op1 isNSW n = .value r) :
    Refines ((Shift.shiftSrc opc f op0 op1).eval ρ) (r.eval ρ) :=
  run_sound (simplifyShift.steps_sound o e ρ hop f op0 op1 isNSW n hnsw ho c1 u1) h

open Shift in
/-- `IS.simplifyRightShift.L1381`: `X >> X` to 0. -/
theorem simplifyRightShift.L1381 (ρ : Env) {opc : BinOp} (hop : opc = .lshr ∨ opc = .ashr) (f : Flags)
    (op0 op1 : Term w) (h : specific op0 op1 = true) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.const 0#w).eval ρ) := by
  rw [shiftSrc_eval (Or.inr hop), specific_denote h]
  refine refines_ok ?_
  rcases hop with rfl | rfl
  · exact Lemmas.lshr_self_refines _ _
  · exact Lemmas.ashr_self_refines _ _

open Shift in
/-- `IS.simplifyRightShift.L1386`: `undef >> X` to 0, or to `undef` if `exact`. Without `undef`, the operand is
poison, and so is the shift. -/
theorem simplifyRightShift.L1386 (ρ : Env) {opc : BinOp} (hop : IsShift opc) (f : Flags) (op0 op1 : Term w)
    (isExact : Bool) (u0 : op0.hasUndef = false) (h : isUndefValue op0 = true) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((if isExact then Repl.old op0 else Repl.const 0#w).eval ρ) := by
  rw [shiftSrc_eval hop, isUndefValue_denote h u0, shiftVal_none_left hop]
  split <;> exact refines_ok (Refine.val_none _)

open Shift in
/-- `IS.simplifyRightShift.L1393`: an `exact` right shift of `X` to `X`, where bit 0 of `X` is known 1: shifting by
more than 0 would drop it. -/
theorem simplifyRightShift.L1393 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) {opc : BinOp}
    (hop : opc = .lshr ∨ opc = .ashr) (f : Flags) (hf : f.exact = true) (op0 op1 : Term w)
    (h : (o.knownOne op0).getLsbD 0 = true) :
    Refines ((shiftSrc opc f op0 op1).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [shiftSrc_eval (Or.inr hop), Repl.eval_old]
  refine refines_ok ?_
  cases hd : op0.denote ρ with
  | none => rw [shiftVal_none_left (Or.inr hop)]; exact Refine.val_none _
  | some x =>
    have hx : x.getLsbD 0 = true := by
      have := congrArg (·.getLsbD 0) (ho.knownOne op0 x hd)
      simp only [BitVec.getLsbD_and, h, Bool.and_true] at this
      exact this
    rcases hop with rfl | rfl <;> simp only [shiftVal, hf]
    · exact Lemmas.lshr_exact_of_getLsbD_refines x hx _
    · exact Lemmas.ashr_exact_of_getLsbD_refines x hx _

theorem simplifyRightShift.steps_sound (o : Oracle) (e : Shift.Ext) (ρ : Env) {opc : BinOp}
    (hop : opc = .lshr ∨ opc = .ashr) (f : Flags) (op0 op1 : Term w) (isExact : Bool) (n : Nat)
    (hex : isExact = true → f.exact = true) (ho : o.Sound ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) :
    ∀ s r, Step.fire s r ∈ simplifyRightShift.steps o e opc op0 op1 isExact n →
      Refines ((Shift.shiftSrc opc f op0 op1).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyRightShift.steps, simplifyRightShift.own, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | h | h
  · exact simplifyShift.steps_sound o e ρ (Or.inr hop) f op0 op1 false n (by simp) ho c1 u1 s r h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyRightShift.L1381 ρ hop f op0 op1 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyRightShift.L1386 ρ (Or.inr hop) f op0 op1 isExact u0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    exact simplifyRightShift.L1393 o ρ ho hop f (hex hc.1) op0 op1 hc.2

/-- Theorem 1 for `simplifyRightShift`: every value the model returns refines the `lshr` or `ashr` it's given, with any
flags, where `IsExact` is only set with `exact`. -/
theorem simplifyRightShift.sound (o : Oracle) (e : Shift.Ext) (ρ : Env) {opc : BinOp}
    (hop : opc = .lshr ∨ opc = .ashr) (f : Flags) (op0 op1 : Term w) (isExact : Bool) (n : Nat)
    (hex : isExact = true → f.exact = true) (ho : o.Sound ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) {r : Repl w} (h : simplifyRightShift o e opc op0 op1 isExact n = .value r) :
    Refines ((Shift.shiftSrc opc f op0 op1).eval ρ) (r.eval ρ) :=
  run_sound (simplifyRightShift.steps_sound o e ρ hop f op0 op1 isExact n hex ho c1 u0 u1) h

/-! ### `shl` -/

/-- The `shl` `simplifyShlInst` replaces, with its operands and flags. -/
def shlSrc (op0 op1 : Term w) (isNSW isNUW : Bool) : Repl w :=
  Shift.shiftSrc .shl { nuw := isNUW, nsw := isNSW } op0 op1

theorem shlSrc_eval (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) :
    (shlSrc op0 op1 isNSW isNUW).eval ρ = Outcome.ok (Val.shl (op0.denote ρ) (op1.denote ρ) isNUW isNSW) := rfl

/-- `IS.simplifyShlInst.L1411`: `undef << X` to 0, or to `undef` with `nsw` or `nuw`. Without `undef`, the operand is
poison, and so is the shift. -/
theorem simplifyShlInst.L1411 (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (u0 : op0.hasUndef = false)
    (h : isUndefValue op0 = true) :
    Refines ((shlSrc op0 op1 isNSW isNUW).eval ρ)
      ((if isNSW || isNUW then Repl.old op0 else Repl.const 0#w).eval ρ) := by
  rw [shlSrc_eval, isUndefValue_denote h u0]
  split <;> exact refines_ok (Refine.val_none _)

theorem Shift.exactShrOf_denote {ρ : Env} {a v x : Term w} (h : Shift.exactShrOf a v = some x) (hc : v.Consistent ρ) :
    v.denote ρ = Val.lshr (x.denote ρ) (a.denote ρ) true ∨ v.denote ρ = Val.ashr (x.denote ρ) (a.denote ρ) true := by
  unfold Shift.exactShrOf at h
  split at h
  · next id op f x' b =>
    split at h
    · next hc' =>
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc'
      obtain ⟨⟨hop, hf⟩, hb⟩ := hc'
      simp only [Term.Consistent] at hc
      change ρ w id = _ ∨ ρ w id = _
      rw [← specific_denote hb]
      rcases hop with rfl | rfl
      · left
        have hd : Val.lshr (x.denote ρ) (b.denote ρ) f.exact = ρ w id := ok_inj hc.2.2
        rw [← hd, hf]
      · right
        have hd : Val.ashr (x.denote ρ) (b.denote ρ) f.exact = ρ w id := ok_inj hc.2.2
        rw [← hd, hf]
    · cases h
  · cases h

/-- `IS.simplifyShlInst.L1417`: `(X >> A) << A`, the right shift `exact`, to `X`, whatever the flags on `shl`. -/
theorem simplifyShlInst.L1417 (ρ : Env) (op0 op1 x : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (h : Shift.exactShrOf op1 op0 = some x) :
    Refines ((shlSrc op0 op1 isNSW isNUW).eval ρ) ((Repl.old x).eval ρ) := by
  rw [shlSrc_eval, Repl.eval_old]
  refine refines_ok ?_
  rcases Shift.exactShrOf_denote h c0 with hd | hd <;> rw [hd]
  · exact Generic.shl_lshr_exact_refines _ _ _ _
  · exact Generic.shl_ashr_exact_refines _ _ _ _

/-- `IS.simplifyShlInst.L1421`: `shl nuw C, X` to `C`, where `C` is negative: shifting by more than 0 drops its sign
bit. -/
theorem simplifyShlInst.L1421 (ρ : Env) (op0 op1 : Term w) (isNSW : Bool) (h : negative op0 = true) :
    Refines ((shlSrc op0 op1 isNSW true).eval ρ) ((Repl.old op0).eval ρ) := by
  obtain ⟨c, hc, hd⟩ := cst_denote (ρ := ρ) h
  rw [shlSrc_eval, Repl.eval_old, hd]
  exact refines_ok (Lemmas.shl_nuw_of_msb_refines c hc _ _)

/-- `IS.simplifyShlInst.L1430`: `shl nuw nsw X, w - 1` to 0. At width 1, `w - 1` is 0, which `IS.simplifyShift.L1322`
has already folded, as `simplifyShlInst` runs it first: that the amount isn't 0 is this rewrite's hypothesis. -/
theorem simplifyShlInst.L1430 (ρ : Env) (op0 op1 : Term w) (hz : zero op1 = false)
    (h : cst (fun c => c.toNat == w - 1) op1 = true) :
    Refines ((shlSrc op0 op1 true true).eval ρ) ((Repl.const 0#w).eval ρ) := by
  unfold cst at h
  split at h
  · next c hc =>
    simp only [beq_iff_eq] at h
    have hz' : (c == 0#w) = false := by simpa [zero, cst, hc] using hz
    have hw : 1 < w := by
      false_or_by_contra
      have : c = 0#w := BitVec.eq_of_toNat_eq (by simp; omega)
      simp [this] at hz'
    rw [shlSrc_eval, apint_denote hc]
    exact refines_ok (Lemmas.shl_nuw_nsw_of_toNat_eq_refines _ h hw)
  · cases h

theorem simplifyShlInst.own_sound (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (c0 : op0.Consistent ρ)
    (u0 : op0.hasUndef = false) (hz : zero op1 = false) :
    ∀ s r, Step.fire s r ∈ simplifyShlInst.own op0 op1 isNSW isNUW →
      Refines ((shlSrc op0 op1 isNSW isNUW).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyShlInst.own, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyShlInst.L1411 ρ op0 op1 isNSW isNUW u0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next x hx =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyShlInst.L1417 ρ op0 op1 x isNSW isNUW c0 hx
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨rfl, hn⟩ := hc
    exact simplifyShlInst.L1421 ρ op0 op1 isNSW hn
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next hc =>
    obtain ⟨-, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨rfl, rfl⟩, hc⟩ := hc
    exact simplifyShlInst.L1430 ρ op0 op1 hz hc

/-- Theorem 1 for `simplifyShlInst`: every value the model returns refines the `shl` it replaces, at every width, for
both flags and every recursion budget, in every run its operands are consistent with and the oracle is sound in, poison
included. It says nothing about operands that reach an `undef`. -/
theorem simplifyShlInst.sound (o : Oracle) (e : Shift.Ext) (ρ : Env) (op0 op1 : Term w) (isNSW isNUW : Bool) (n : Nat)
    (ho : o.Sound ρ) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) {r : Repl w} (h : simplifyShlInst o e op0 op1 isNSW isNUW n = .value r) :
    Refines ((shlSrc op0 op1 isNSW isNUW).eval ρ) (r.eval ρ) := by
  rcases Shift.run_append_value h with ⟨s, hs⟩ | ⟨hn, ht⟩
  · exact simplifyShift.steps_sound o e ρ (Or.inl rfl) _ op0 op1 isNSW n (fun h => ⟨rfl, h⟩) ho c1 u1 s r hs
  · -- `simplifyShift` fell through, so the amount isn't 0: `IS.simplifyShift.L1322` didn't fire.
    have hz : zero op1 = false := by
      have := hn _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      split at this
      · cases this
      · next hc => exact (by simpa using hc : zero op1 = false ∧ _).1
    exact run_sound (simplifyShlInst.own_sound ρ op0 op1 isNSW isNUW c0 u0 hz) ht

/-! ### `lshr` -/

/-- The `lshr` `simplifyLShrInst` replaces, with its operands and flag. -/
def lshrSrc (op0 op1 : Term w) (isExact : Bool) : Repl w := Shift.shiftSrc .lshr { exact := isExact } op0 op1

theorem lshrSrc_eval (ρ : Env) (op0 op1 : Term w) (isExact : Bool) :
    (lshrSrc op0 op1 isExact).eval ρ = Outcome.ok (Val.lshr (op0.denote ρ) (op1.denote ρ) isExact) := rfl

/-- `IS.simplifyLShrInst.L1451`: `lshr (shl nuw X, A), A` to `X`. -/
theorem simplifyLShrInst.L1451 (ρ : Env) (op0 op1 x : Term w) (isExact : Bool) (c0 : op0.Consistent ρ)
    (h : Shift.shlOf (·.nuw) op1 op0 = some x) :
    Refines ((lshrSrc op0 op1 isExact).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨f, hf, hd⟩ := Shift.shlOf_denote h c0
  rw [lshrSrc_eval, Repl.eval_old, hd, hf]
  exact refines_ok (Generic.lshr_shl_nuw_refines _ _ _ _)

theorem Shift.nuwShlConst_denote {ρ : Env} {t x : Term w} {c : BitVec w} (h : Shift.nuwShlConst t = some (x, c))
    (hc : t.Consistent ρ) : ∃ nsw, t.denote ρ = Val.shl (x.denote ρ) (some c) true nsw := by
  unfold Shift.nuwShlConst at h
  split at h
  · next f x' c' hb =>
    split at h
    · next hf =>
      cases hac : apint c' with
      | none => simp [hac] at h
      | some c'' =>
        simp only [hac, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨f.nsw, ?_⟩
        rw [← apint_denote hac, ← hf]
        exact (ok_inj (Shift.binop?_denote hb hc)).symm
    · cases h
  · cases h

theorem Shift.orNUWShl_denote {ρ : Env} {t x y : Term w} {c : BitVec w} (h : Shift.orNUWShl t = some (x, c, y))
    (hc : t.Consistent ρ) : ∃ nsw d,
      t.denote ρ = Val.or (Val.shl (x.denote ρ) (some c) true nsw) (y.denote ρ) d ∨
      t.denote ρ = Val.or (y.denote ρ) (Val.shl (x.denote ρ) (some c) true nsw) d := by
  unfold Shift.orNUWShl at h
  split at h
  · next f a b hb =>
    have ⟨ca, cb, hd⟩ := binop?_consistent hb hc
    have hd := (ok_inj hd).symm
    split at h
    · next x' c' hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨nsw, hs⟩ := Shift.nuwShlConst_denote hs ca
      exact ⟨nsw, f.disjoint, Or.inl (by rw [hd, hs])⟩
    · cases hs : Shift.nuwShlConst b with
      | none => simp [hs] at h
      | some p =>
        obtain ⟨x', c'⟩ := p
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨nsw, hs⟩ := Shift.nuwShlConst_denote hs cb
        exact ⟨nsw, f.disjoint, Or.inr (by rw [hd, hs])⟩
  · cases h

/-- `IS.simplifyLShrInst.L1466`: `lshr (or (shl nuw X, C), Y), C`, the `or` either way round, to `X`, where the known
leading zeros of `Y` leave it under `2 ^ C`: `Y` is in the bits the `shl` cleared, which the `lshr` drops. -/
theorem simplifyLShrInst.L1466 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (op0 op1 x y : Term w) (r : BitVec w)
    (isExact : Bool) (c0 : op0.Consistent ρ) (hr : apint op1 = some r) (hm : Shift.orNUWShl op0 = some (x, r, y))
    (hw : w - Shift.countLeadingOnes (o.knownZero y) ≤ r.toNat) :
    Refines ((lshrSrc op0 op1 isExact).eval ρ) ((Repl.old x).eval ρ) := by
  rw [lshrSrc_eval, Repl.eval_old, apint_denote hr]
  refine refines_ok ?_
  obtain ⟨nsw, d, hd | hd⟩ := Shift.orNUWShl_denote hm c0 <;> rw [hd] <;> cases hy : y.denote ρ
  · rw [Shift.or_none_right]; exact Refine.val_none _
  · next v =>
    have hlt := Shift.toNat_lt_of_and (ho.knownZero y v hy) (Nat.le_refl _)
    have : v.toNat < 2 ^ r.toNat := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hw)
    exact Lemmas.lshr_or_shl_nuw_refines _ this _ _ _
  · rw [Shift.or_none_left]; exact Refine.val_none _
  · next v =>
    have hlt := Shift.toNat_lt_of_and (ho.knownZero y v hy) (Nat.le_refl _)
    have : v.toNat < 2 ^ r.toNat := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hw)
    rw [Shift.or_comm]
    exact Lemmas.lshr_or_shl_nuw_refines _ this _ _ _

theorem simplifyLShrInst.own_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (op0 op1 : Term w) (isExact : Bool)
    (c0 : op0.Consistent ρ) :
    ∀ s r, Step.fire s r ∈ simplifyLShrInst.own o op0 op1 → Refines ((lshrSrc op0 op1 isExact).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyLShrInst.own, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next x hx =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyLShrInst.L1451 ρ op0 op1 x isExact c0 hx
  · split at h
    · next r' x l y hr hm =>
      split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
      next hc =>
      obtain ⟨-, rfl⟩ := h
      obtain ⟨rfl, hw⟩ := hc
      exact simplifyLShrInst.L1466 o ρ ho op0 op1 x y r' isExact c0 hr hm hw
    · simp only [reduceCtorEq] at h

/-- Theorem 1 for `simplifyLShrInst`: every value the model returns refines the `lshr` it replaces, at every width,
with or without `exact`, at every recursion budget, in every run its operands are consistent with and the oracle is
sound in, poison included. It says nothing about operands that reach an `undef`. -/
theorem simplifyLShrInst.sound (o : Oracle) (e : Shift.Ext) (ρ : Env) (op0 op1 : Term w) (isExact : Bool) (n : Nat)
    (ho : o.Sound ρ) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) {r : Repl w} (h : simplifyLShrInst o e op0 op1 isExact n = .value r) :
    Refines ((lshrSrc op0 op1 isExact).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((lshrSrc op0 op1 isExact).eval ρ) (r.eval ρ)) ?_ h
  intro s r hmem
  simp only [simplifyLShrInst.steps, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact simplifyRightShift.steps_sound o e ρ (Or.inl rfl) _ op0 op1 isExact n id ho c1 u0 u1 s r hmem
  · exact simplifyLShrInst.own_sound o ρ ho op0 op1 isExact c0 s r hmem

/-! ### `ashr` -/

/-- The `ashr` `simplifyAShrInst` replaces, with its operands and flag. -/
def ashrSrc (op0 op1 : Term w) (isExact : Bool) : Repl w := Shift.shiftSrc .ashr { exact := isExact } op0 op1

theorem ashrSrc_eval (ρ : Env) (op0 op1 : Term w) (isExact : Bool) :
    (ashrSrc op0 op1 isExact).eval ρ = Outcome.ok (Val.ashr (op0.denote ρ) (op1.denote ρ) isExact) := rfl

/-- `IS.simplifyAShrInst.L1490`: `ashr -1, X` and `ashr (shl -1, X), X` to -1. -/
theorem simplifyAShrInst.L1490 (ρ : Env) (op0 op1 : Term w) (isExact : Bool) (c0 : op0.Consistent ρ)
    (h : (allOnes op0 || Shift.shlAllOnesOf op1 op0) = true) :
    Refines ((ashrSrc op0 op1 isExact).eval ρ) ((Repl.const (BitVec.allOnes w)).eval ρ) := by
  rw [ashrSrc_eval]
  refine refines_ok ?_
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [cst_eq h]
    exact Lemmas.ashr_allOnes_refines _ _
  · unfold Shift.shlAllOnesOf at h
    split at h
    · next f a b hb =>
      simp only [Bool.and_eq_true] at h
      rw [← (ok_inj (Shift.binop?_denote hb c0)), cst_eq h.1, ← specific_denote h.2]
      exact Lemmas.ashr_shl_allOnes_refines _ _ _ _
    · cases h

/-- `IS.simplifyAShrInst.L1495`: `ashr (shl nsw X, A), A` to `X`. -/
theorem simplifyAShrInst.L1495 (ρ : Env) (op0 op1 x : Term w) (isExact : Bool) (c0 : op0.Consistent ρ)
    (h : Shift.shlOf (·.nsw) op1 op0 = some x) :
    Refines ((ashrSrc op0 op1 isExact).eval ρ) ((Repl.old x).eval ρ) := by
  obtain ⟨f, hf, hd⟩ := Shift.shlOf_denote h c0
  rw [ashrSrc_eval, Repl.eval_old, hd, hf]
  exact refines_ok (Generic.ashr_shl_nsw_refines _ _ _ _)

/-- `IS.simplifyAShrInst.L1500`: `ashr X, A` to `X`, where `ComputeNumSignBits(X)` is the width: every bit of `X` is
its sign bit, so `X` is 0 or -1. -/
theorem simplifyAShrInst.L1500 (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (op0 op1 : Term w) (isExact : Bool)
    (h : o.signBits op0 = w) : Refines ((ashrSrc op0 op1 isExact).eval ρ) ((Repl.old op0).eval ρ) := by
  rw [ashrSrc_eval, Repl.eval_old]
  refine refines_ok ?_
  cases hd : op0.denote ρ with
  | none => exact Refine.val_none _
  | some x =>
    have hs := ho.signBits op0 x hd
    rw [h] at hs
    exact Lemmas.ashr_of_getMsbD_refines x (fun i hi => hs i hi hi) _ _

theorem simplifyAShrInst.own_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (op0 op1 : Term w) (isExact : Bool)
    (c0 : op0.Consistent ρ) :
    ∀ s r, Step.fire s r ∈ simplifyAShrInst.own o op0 op1 → Refines ((ashrSrc op0 op1 isExact).eval ρ) (r.eval ρ) := by
  intro s r hmem
  simp only [simplifyAShrInst.own, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAShrInst.L1490 ρ op0 op1 isExact c0 (by assumption)
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    next x hx =>
    obtain ⟨-, rfl⟩ := h
    exact simplifyAShrInst.L1495 ρ op0 op1 x isExact c0 hx
  · split at h <;> simp only [Step.fire.injEq, reduceCtorEq] at h
    obtain ⟨-, rfl⟩ := h
    exact simplifyAShrInst.L1500 o ρ ho op0 op1 isExact (by assumption)

/-- Theorem 1 for `simplifyAShrInst`: every value the model returns refines the `ashr` it replaces, at every width,
with or without `exact`, at every recursion budget, in every run its operands are consistent with and the oracle is
sound in, poison included. It says nothing about operands that reach an `undef`. -/
theorem simplifyAShrInst.sound (o : Oracle) (e : Shift.Ext) (ρ : Env) (op0 op1 : Term w) (isExact : Bool) (n : Nat)
    (ho : o.Sound ρ) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false)
    (u1 : op1.hasUndef = false) {r : Repl w} (h : simplifyAShrInst o e op0 op1 isExact n = .value r) :
    Refines ((ashrSrc op0 op1 isExact).eval ρ) (r.eval ρ) := by
  refine run_sound (P := fun r => Refines ((ashrSrc op0 op1 isExact).eval ρ) (r.eval ρ)) ?_ h
  intro s r hmem
  simp only [simplifyAShrInst.steps, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact simplifyRightShift.steps_sound o e ρ (Or.inr rfl) _ op0 op1 isExact n id ho c1 u0 u1 s r hmem
  · exact simplifyAShrInst.own_sound o ρ ho op0 op1 isExact c0 s r hmem

/-! ### On an instruction -/

/-- What `simplifyShlInst.onInst` returns refines the instruction it's given, in every run the instruction is
consistent with and the oracle is sound in. -/
theorem simplifyShlInst.onInst_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (t : Term w)
    (ct : t.Consistent ρ) (ut : t.hasUndef = false) {r : Repl w} (h : simplifyShlInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold simplifyShlInst.onInst at h
  split at h
  · next id f a b =>
    simp only [Term.Consistent] at ct
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at ut
    exact simplifyShlInst.sound o _ ρ a b f.nsw f.nuw 3 ho ct.1 ct.2.1 ut.1 ut.2 h
  · cases h

/-- What `simplifyLShrInst.onInst` returns refines the instruction it's given. -/
theorem simplifyLShrInst.onInst_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (t : Term w)
    (ct : t.Consistent ρ) (ut : t.hasUndef = false) {r : Repl w} (h : simplifyLShrInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold simplifyLShrInst.onInst at h
  split at h
  · next id f a b =>
    simp only [Term.Consistent] at ct
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at ut
    exact simplifyLShrInst.sound o _ ρ a b f.exact 3 ho ct.1 ct.2.1 ut.1 ut.2 h
  · cases h

/-- What `simplifyAShrInst.onInst` returns refines the instruction it's given. -/
theorem simplifyAShrInst.onInst_sound (o : Oracle) (ρ : Env) (ho : o.Sound ρ) (t : Term w)
    (ct : t.Consistent ρ) (ut : t.hasUndef = false) {r : Repl w} (h : simplifyAShrInst.onInst o t = .value r) :
    Refines (t.top.eval ρ) (r.eval ρ) := by
  unfold simplifyAShrInst.onInst at h
  split at h
  · next id f a b =>
    simp only [Term.Consistent] at ct
    simp only [Term.hasUndef, Bool.or_eq_false_iff] at ut
    exact simplifyAShrInst.sound o _ ρ a b f.exact 3 ho ct.1 ct.2.1 ut.1 ut.2 h
  · cases h


end Peephole.IS
