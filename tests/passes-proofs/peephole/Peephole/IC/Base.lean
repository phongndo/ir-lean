import Peephole.Match
import Peephole.Oracle
import Peephole.Fold

/-! # InstCombine's folds, as models

An InstCombine fold, such as `visitAdd` in `llvm/lib/Transforms/InstCombine/InstCombineAddSub.cpp`, is modelled as
InstSimplify's are, with what `Peephole.Fold` already has: a list of `Step`s, one for each statement in the C++ that can
end the function, in the C++'s order, run by `run`, whose answer is a `Repl`. What's different is what the answer can
be, and what the C++ reads besides operands and analyses. This module adds what InstCombine's models share, beside the
core and without changing it:

- **New instructions.** A fold that returns `BinaryOperator::CreateSub(C, X)`, or `new ZExtInst(V, Ty)`, answers a
  `Repl` built on the operands that exist (`Repl.old`), with the flags the C++ sets on what it creates: `.bin .sub {}
  (.const c) (.old x)`. `BinaryOperator::Create*` and `new *Inst` make an instruction whatever its operands are.
- **The builder's constant folding.** `Builder.CreateNot(Y)` and the other `Builder.Create*` calls go through IRBuilder's
  `TargetFolder`, which answers a constant, not an instruction, when every operand is a constant. `ConstantExpr::get*`,
  `InstCombiner::AddOne` and `SubOne` fold their constant operands the same way. The functions under
  [constants](#constants-as-llvm-folds-them) are those folds on scalar integers, with poison and `undef` as
  `ConstantFold.cpp` treats them, and each has a theorem that its value is the instruction's.
- **In-place changes.** A fold that changes `I` and returns `&I`, as `I.setHasNoSignedWrap(true)` or
  `replaceOperand(I, 0, A)` do, makes `I` a new instruction. The step that ends the fold fires that instruction, as a
  `Repl` on `I`'s operands with its new flags, under the ID of the change. Where the C++ goes on after a change, the
  steps after it see `I` as changed.
- **`replaceInstUsesWith(I, V)`** answers `V`, as InstSimplify's folds do. A fold's call into InstSimplify, as
  `visitAdd`'s first statement calls `simplifyAddInst`, is a step that forwards to that fold's model with `forward`:
  it fires what the callee answers, and its theorem is the callee's `sound` theorem.
- **What the C++ reads from the function around an operand:** `V->hasOneUse()` and `isa<PHINode>(V)`, which neither
  `Term` nor an analysis holds. A model takes them from a `Ctx`, and a theorem about it holds for every `Ctx`: they
  decide only whether a fold is worth making, not whether it's right. The comparison with `opt` gives each case's
  `Ctx` from the function it runs, where every `var` is an argument, so no operand is a phi.

What a fold's model doesn't follow is the pass around it, as for InstSimplify's: InstCombine's worklist, replacing
`I`'s uses and revisiting its users, deleting what's dead, and running again until nothing changes. A fold's theorem
says its answer refines `I`, and nothing about what InstCombine does with the answer next. A statement of the C++ that
can end the fold with code the model doesn't follow is `.delegate`, which claims nothing, as `return &I` after
`SimplifyAssociativeOrCommutative(I)` changed `I` in ways not modelled here. -/

namespace Peephole.IC

open IRLean

variable {w : Nat}

/-- What an InstCombine fold reads about its operands from the function around them, which neither `Term` nor an
analysis says. A theorem about a fold holds for every `Ctx`. -/
structure Ctx where
  /-- `V->hasOneUse()`: the instruction `V` has exactly one use. -/
  oneUse : {w : Nat} → Term w → Bool
  /-- `isa<PHINode>(V)`. `Term` holds no phi, so a phi is a `var`. -/
  phi : {w : Nat} → Term w → Bool

/-- No operand has exactly one use, and none is a phi. -/
def Ctx.none : Ctx where
  oneUse _ := false
  phi _ := false

/-- `m_OneUse(m_BinOp<op>(...))`: a binary operator with opcode `op` that has one use, with its flags and operands. -/
def binop1? (c : Ctx) (op : BinOp) (t : Term w) : Option (Flags × Term w × Term w) :=
  if c.oneUse t then binop? op t else none

/-- `isa<SelectInst>(V)`. -/
def isSelect : Term w → Bool
  | .select .. => true
  | _ => false

/-- `isa<BinaryOperator>(V)` with this opcode. -/
def isBin (op : BinOp) (t : Term w) : Bool := (binop? op t).isSome

/-! ### Forwarding to a fold modelled here -/

/-- `if (Value *V = g(...)) return replaceInstUsesWith(I, V);`, for a `g` modelled as a function answering a
`Result`: what `g` answers, as a step. A forward isn't a site: it fires under the callee's name, and the comparison
with `opt` reports the site of the callee's step that fired. -/
def forward (callee : String) : Result w → Step w
  | .value r => .fire callee r
  | .null => .next
  | .delegated c => .delegate c

theorem forward_fire {callee s : String} {res : Result w} {r : Repl w} (h : forward callee res = .fire s r) :
    res = .value r := by
  cases res <;> simp_all [forward]

/-! ### Constants, as LLVM folds them

`ConstantFoldBinaryInstruction` in `llvm/lib/IR/ConstantFold.cpp` folds two constants: poison wins, then `undef` by
the opcode's rule, then the integers. `TargetFolder` and `ConstantExpr::get` call it, or `ConstantFoldCompareInstruction`
or `ConstantFoldIntrinsic`, when every operand is a constant. Each function here is one of those, on operands that are
`Term`s, and is the instruction itself when an operand isn't a constant. Each has a theorem that its value, run, is the
instruction's, for operands with no `undef`. -/

/-- `ConstantExpr::getAdd(C1, C2)`, `InstCombiner::AddOne(C)` with `C2` one: `add` of two constants. -/
def constAdd (a b : Term w) : Repl w :=
  match a, b with
  | .const x, .const y => .const (x + y)
  | .poison, _ => .poison
  | _, .poison => .poison
  | .undef, _ => .old .undef
  | _, .undef => .old .undef
  | _, _ => .bin .add {} (.old a) (.old b)

/-- `ConstantExpr::getSub(C1, C2)`, `InstCombiner::SubOne(C)` with `C2` one: `sub` of two constants. -/
def constSub (a b : Term w) : Repl w :=
  match a, b with
  | .const x, .const y => .const (x - y)
  | .poison, _ => .poison
  | _, .poison => .poison
  | .undef, _ => .old .undef
  | _, .undef => .old .undef
  | _, _ => .bin .sub {} (.old a) (.old b)

/-- `Builder.CreateNot(V)`: `xor V, -1`, folded when `V` is a constant. -/
def notOf (v : Term w) : Repl w :=
  match v with
  | .const x => .const (~~~x)
  | .poison => .poison
  | .undef => .old .undef
  | _ => .bin .xor {} (.old v) (.const (BitVec.allOnes w))

/-- `Builder.CreateIsNotNeg(V)`: `icmp sgt V, -1`, folded when `V` is a constant. `ConstantFoldCompareInstruction`
folds an `undef` operand of an ordered predicate to the predicate's value on equal operands, false for `sgt`. -/
def isNotNegOf (v : Term w) : Repl 1 :=
  match v with
  | .const x => .const (BitVec.ofBool (BitVec.slt (BitVec.allOnes w) x))
  | .poison => .poison
  | .undef => .const 0#1
  | _ => .icmp .sgt false (.old v) (.const (BitVec.allOnes w))

/-- `Builder.CreateShl(V, C)`, with no flags, folded when `V` is a constant: `undef << C` is 0, or `undef` if `C` is
0, `shl`'s identity. -/
def shlOf (v : Term w) (k : BitVec w) : Repl w :=
  match v with
  | .const x => if Val.shiftOk k then .const (x <<< k) else .poison
  | .poison => .poison
  | .undef => if k = 0#w then .old .undef else .const 0#w
  | _ => .bin .shl {} (.old v) (.const k)

/-- `Builder.CreateBinaryIntrinsic(Intrinsic::usub_sat, V, C)`, folded when `V` is a constant: the intrinsic
propagates poison, and `undef` saturates to 0. -/
def usubSatOf (v : Term w) (k : BitVec w) : Repl w :=
  match v with
  | .const x => .const (if BitVec.ult x k then 0#w else x - k)
  | .poison => .poison
  | .undef => .const 0#w
  | _ => .bi .usubSat (.old v) (.const k)

theorem constAdd_eval (ρ : Env) (a b : Term w) :
    (constAdd a b).eval ρ = Outcome.ok (Val.add (a.denote ρ) (b.denote ρ)) := by
  unfold constAdd
  split <;> simp_all [Repl.eval, Term.denote, Val.add, BinOp.eval, andThen, Outcome.ok]

theorem constSub_eval (ρ : Env) (a b : Term w) :
    (constSub a b).eval ρ = Outcome.ok (Val.sub (a.denote ρ) (b.denote ρ)) := by
  unfold constSub
  split <;> simp_all [Repl.eval, Term.denote, Val.sub, BinOp.eval, andThen, Outcome.ok]

theorem notOf_eval (ρ : Env) (v : Term w) :
    (notOf v).eval ρ = Outcome.ok (Val.xor (v.denote ρ) (some (BitVec.allOnes w))) := by
  unfold notOf
  split <;> simp_all [Repl.eval, Term.denote, Val.xor, Val.map₂, BinOp.eval, andThen, Outcome.ok,
    BitVec.xor_allOnes]

theorem isNotNegOf_eval (ρ : Env) (v : Term w) (hu : v.hasUndef = false) :
    (isNotNegOf v).eval ρ = Outcome.ok (Val.icmpSgt (v.denote ρ) (some (BitVec.allOnes w))) := by
  unfold isNotNegOf
  split <;> simp_all [Repl.eval, Term.denote, Term.hasUndef, Val.icmpSgt, Val.icmp, Pred.eval, andThen,
    Outcome.ok]

theorem shlOf_eval (ρ : Env) (v : Term w) (k : BitVec w) (hu : v.hasUndef = false) :
    (shlOf v k).eval ρ = Outcome.ok (Val.shl (v.denote ρ) (some k)) := by
  unfold shlOf
  split
  · split <;> simp_all [Repl.eval, Term.denote, Val.shl, Outcome.ok]
  · simp [Repl.eval, Term.denote, Val.shl, Outcome.ok]
  · simp [Term.hasUndef] at hu
  · simp [Repl.eval, BinOp.eval, andThen, Outcome.ok]

theorem usubSatOf_eval (ρ : Env) (v : Term w) (k : BitVec w) (hu : v.hasUndef = false) :
    (usubSatOf v k).eval ρ = Outcome.ok (Val.usubSat (v.denote ρ) (some k)) := by
  unfold usubSatOf
  split <;> simp_all [Repl.eval, Term.denote, Term.hasUndef, Val.usubSat, Val.map₂, BinIntr.eval, andThen,
    Outcome.ok]

/-! ### Analyses on constants

`willNotOverflowSignedAdd(C1, C2, I)` and `willNotOverflowSignedSub` ask `computeOverflowForSignedAdd` and `Sub` in
`llvm/lib/Analysis/ValueTracking.cpp`, which on two `ConstantInt`s answer exactly whether the operation overflows: the
operands' known bits, and so their ranges, are exact. On poison or `undef` nothing is known, so the range is every
value, which overflows with anything but 0 added. -/

/-- `willNotOverflowSignedAdd(A, C)` for a constant `A` and a `ConstantInt` `C`. -/
def willNotOverflowSignedAdd (a : Term w) (c : BitVec w) : Bool :=
  match a with
  | .const x => !x.saddOverflow c
  | _ => c == 0#w

/-- `willNotOverflowSignedSub(A, 1)` for a constant `A`. Subtracting 1 from every value overflows at every width LLVM
has. -/
def willNotOverflowSignedSubOne (a : Term w) : Bool :=
  match a with
  | .const x => !x.ssubOverflow 1#w
  | _ => false

end Peephole.IC
