import Peephole.IC.AddConst

/-! # InstCombine's `visitAdd`, as far as `foldAddWithConstant`

`InstCombinerImpl::visitAdd` is at `llvm/lib/Transforms/InstCombine/InstCombineAddSub.cpp:1594-2067` at
`llvmorg-23.1.3`. This is its model on `Peephole.Term`, step by step in the C++'s order, up to and through
`foldAddWithConstant`, which `Peephole.IC.AddConst` models:

1. `simplifyAddInst`, which `Peephole.IS.Add` models, forwarded: its answer replaces the `add`.
2. `SimplifyAssociativeOrCommutative`, `foldVectorBinop`, `foldBinopWithPhiOperands`, `foldUsingDistributiveLaws`,
   `foldBoxMultiply` and `factorizeMathWithShlOps`, which aren't modelled: each delegates where it could change the
   `add`, as far as its first matches say, and falls through where it can't.
3. `foldAddWithConstant`, whose steps run as `visitAdd`'s own.
4. The rest of `visitAdd`, from `foldNoWrapAdd` on, which isn't modelled: it delegates unless both operands are
   arguments or constants, two different values, wider than `i1`, where none of its steps can fire.

`visitAdd.sound` is theorem 1 for this model, in the sense of
[the binding approach](../../../../../docs/binding-approach.md#two-theorems-per-unit): every value it answers refines the
`add`, at every width, for every flag, `Ctx` and sound `Oracle`, poison included. -/

namespace Peephole.IC

open IRLean

variable {w : Nat}

/-! ### What the steps it doesn't model look at -/

/-- `InstCombiner::getComplexity(V)`: 0 for `undef` and poison, 1 for another constant, 2 for a cast, `m_Neg` or
`m_Not`, and 3 for an argument or any other instruction. -/
def complexity (t : Term w) : Nat :=
  match t with
  | .poison | .undef => 0
  | .const _ => 1
  | .zext .. | .sext .. | .trunc .. => 2
  | _ => if (neg? t).isSome || (not? t).isSome then 2 else 3

/-- Two min/max intrinsics whose predicates are each other's swapped: `smax` and `smin`, `umax` and `umin`. -/
def swappedMinMax : BinIntr → BinIntr → Bool
  | .smax, .smin | .smin, .smax | .umax, .umin | .umin, .umax => true
  | _, _ => false

/-- `matchSymmetricPair(LHS, RHS)` finds a pair: two `select`s on one condition with their arms swapped, two min/max
intrinsics with swapped predicates on the same operands in either order, or two phis, which it may. -/
def symmetricPair (c : Ctx) (a b : Term w) : Bool :=
  match a, b with
  | .select _ c1 t1 f1, .select _ c2 t2 f2 => specific c1 c2 && specific t1 f2 && specific f1 t2
  | .bi _ f1 x1 y1, .bi _ f2 x2 y2 =>
    swappedMinMax f1 f2 && ((specific x1 x2 && specific y1 y2) || (specific x1 y2 && specific y1 x2))
  | _, _ => c.phi a && c.phi b

/-- Whether `SimplifyAssociativeOrCommutative(I)` may change an `add`: it swaps operands the less complex first, rewrites
a symmetric pair, and reassociates an `add` operand when InstSimplify, which isn't modelled, simplifies part of it. -/
def assocOrCommutes (c : Ctx) (op0 op1 : Term w) : Bool :=
  decide (complexity op0 < complexity op1) || symmetricPair c op0 op1 || isBin .add op0 || isBin .add op1

/-- A `mul`, or a `shl` by a constant, which `getBinOpsForFactorization` treats as a `mul` under an `add`. -/
def mulLike (t : Term w) : Bool :=
  isBin .mul t ||
    match binop? .shl t with
    | some (_, _, s) => s.isConstant
    | none => false

/-- Whether `foldUsingDistributiveLaws(I)` may fold an `add`: factorizing needs an operand that's a `mul` and the other
not a constant, since only `mul` distributes over `add`, and `SimplifySelectsFeedingBinaryOp` a `select` operand.
Nothing distributes over an `add`, so it expands nothing. -/
def distributes (op0 op1 : Term w) : Bool :=
  (mulLike op0 && !op1.isConstant) || (mulLike op1 && !op0.isConstant) || isSelect op0 || isSelect op1

/-- Whether `foldBoxMultiply(I)` may fold: it needs an even width, a `shl` operand and a `mul` one. -/
def boxMultiply (op0 op1 : Term w) : Bool :=
  w % 2 == 0 && ((isBin .shl op0 && isBin .mul op1) || (isBin .mul op0 && isBin .shl op1))

/-- Whether `factorizeMathWithShlOps(I, Builder)` folds: two `shl`s by one amount, one of them with one use. -/
def shlOps (c : Ctx) (op0 op1 : Term w) : Bool :=
  match binop? .shl op0, binop? .shl op1 with
  | some (_, _, s0), some (_, _, s1) => specific s0 s1 && (c.oneUse op0 || c.oneUse op1)
  | _, _ => false

/-- An argument, or a constant integer: what none of `visitAdd`'s steps after `foldAddWithConstant` looks into, and
whose known bits say nothing a step there could use, but for a constant's own value. -/
def leaf : Term w → Bool
  | .var _ | .const _ => true
  | _ => false

/-- Whether the rest of `visitAdd`, from `foldNoWrapAdd` on, may fold. It can't on two different leaves wider than
`i1`: an `i1` `add` becomes an `xor`, `X + X` a `shl`, and every other step needs an operand that's an instruction, or
known bits that show the operands share no bit or the `add` doesn't wrap, which an argument and a constant other than 0
don't, and `simplifyAddInst` takes 0 first. -/
def restMayFold (op0 op1 : Term w) : Bool :=
  !(w != 1 && leaf op0 && leaf op1 && !specific op0 op1)

/-! ### The model -/

/-- `visitAdd(I)` for `I = add op0, op1` with flags `f`, step by step, as far as `foldAddWithConstant` and through it. -/
def visitAdd.steps (c : Ctx) (o : Oracle) (op0 op1 : Term w) (f : Flags) : List (Step w) :=
  [ -- if (Value *V = simplifyAddInst(I.getOperand(0), I.getOperand(1), I.hasNoSignedWrap(),
    --                                I.hasNoUnsignedWrap(), SQ.getWithInstruction(&I)))
    --   return replaceInstUsesWith(I, V);
    forward "IS.simplifyAddInst" (IS.simplifyAddInst op0 op1 f.nsw f.nuw 3),
    -- if (SimplifyAssociativeOrCommutative(I)) return &I;
    if assocOrCommutes c op0 op1 then .delegate "SimplifyAssociativeOrCommutative" else .next,
    -- if (Instruction *X = foldVectorBinop(I)) return X;
    -- A scalar isn't a vector.
    .next,
    -- if (Instruction *Phi = foldBinopWithPhiOperands(I)) return Phi;
    if (isBin .add op0 && isBin .add op1) || (c.phi op0 && c.phi op1) then .delegate "foldBinopWithPhiOperands"
    else .next,
    -- (A*B)+(A*C) -> A*(B+C) etc
    if distributes op0 op1 then .delegate "foldUsingDistributiveLaws" else .next,
    -- if (Instruction *R = foldBoxMultiply(I)) return R;
    if boxMultiply op0 op1 then .delegate "foldBoxMultiply" else .next,
    -- if (Instruction *R = factorizeMathWithShlOps(I, Builder)) return R;
    if shlOps c op0 op1 then .delegate "factorizeMathWithShlOps" else .next ] ++
  -- if (Instruction *X = foldAddWithConstant(I)) return X;
  foldAddWithConstant.steps c o op0 op1 f.nsw f.nuw ++
  [ -- foldNoWrapAdd and the rest of visitAdd, which the model doesn't follow.
    if restMayFold op0 op1 then .delegate "visitAdd" else .next ]

/-- `InstCombinerImpl::visitAdd(I)`, for `I = add op0, op1` with flags `f`. -/
def visitAdd (c : Ctx) (o : Oracle) (op0 op1 : Term w) (f : Flags) : Result w :=
  run (visitAdd.steps c o op0 op1 f)

/-- What InstCombine does with an `add` it visits: `visitAdd` on its operands and flags. -/
def visitAdd.onInst (c : Ctx) (o : Oracle) : {w : Nat} → Term w → Result w
  | _, .bin _ .add f a b => visitAdd c o a b f
  | _, _ => .null

/-! ### The fold's theorem -/

theorem run_cons_ne_null {s : Step w} {rest : List (Step w)} (hs : s = .next ∨ ∃ site r, s = .fire site r)
    (h : run rest ≠ .null) : run (s :: rest) ≠ .null := by
  rcases hs with rfl | ⟨site, r, rfl⟩
  · exact h
  · simp [run]

/-- `simplifyAddInst` answers for every `i1` `add`: with `MaxRecurse` at 3, a step that rewrites fires, or it hands
the `add` to `simplifyXorInst`, which the model delegates. It never answers `nullptr`. -/
theorem simplifyAddInst_ne_null_i1 (a b : Term 1) (nsw nuw : Bool) : IS.simplifyAddInst a b nsw nuw 3 ≠ .null := by
  have steps (x y : Term 1) : run (IS.simplifyAddInst.steps x y nsw nuw 3) ≠ .null := by
    simp only [IS.simplifyAddInst.steps]
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    refine run_cons_ne_null (by split <;> (try split) <;> simp) ?_
    refine run_cons_ne_null (by split <;> simp) ?_
    simp [run]
  unfold IS.simplifyAddInst
  split
  · split
    · simp
    · exact steps _ _
  · exact steps _ _

/-- Theorem 1 for `visitAdd`: every value the model answers refines the `add` it replaces, at every width, for every
flag, every `Ctx` and every sound `Oracle`, in every run its operands are consistent with, poison included. It says
nothing about operands that reach an `undef`. -/
theorem visitAdd.sound (ρ : Env) (c : Ctx) (o : Oracle) (ho : o.Sound ρ) (op0 op1 : Term w) (f : Flags)
    (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ) (u0 : op0.hasUndef = false) (u1 : op1.hasUndef = false)
    {r : Repl w} (h : visitAdd c o op0 op1 f = .value r) :
    Refines ((IS.addSrc op0 op1 f.nsw f.nuw).eval ρ) (r.eval ρ) := by
  unfold visitAdd visitAdd.steps at h
  simp only [List.cons_append] at h
  cases hs : IS.simplifyAddInst op0 op1 f.nsw f.nuw 3 with
  | value r' =>
    rw [hs] at h
    simp only [forward, run, Result.value.injEq] at h
    subst h
    exact IS.simplifyAddInst.sound ρ op0 op1 f.nsw f.nuw 3 c0 c1 u0 u1 hs
  | delegated callee =>
    rw [hs] at h
    simp [forward, run] at h
  | null =>
    rw [hs] at h
    simp only [forward, run] at h
    have hw : w ≠ 1 := by
      rintro rfl
      exact simplifyAddInst_ne_null_i1 op0 op1 f.nsw f.nuw hs
    refine run_sound (P := fun r => Refines ((IS.addSrc op0 op1 f.nsw f.nuw).eval ρ) (r.eval ρ)) (fun s r hmem => ?_) h
    simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h
    · split at h <;> simp at h
    · simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h
    · exact foldAddWithConstant.sound ρ c o ho op0 op1 f.nsw f.nuw c0 u0 u1 (Or.inl hw) s r h
    · split at h <;> simp at h

end Peephole.IC
