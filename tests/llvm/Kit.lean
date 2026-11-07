import IRLean
import Std.Tactic.BVDecide

/-! A kit for running emitted code on values known not to be poison, where every flag's condition, and whatever
else a block needs to know, is left to `bv_decide`. Anything it can't discharge stays in the goal. -/

namespace IRLean

namespace Val
variable {w v : Nat} {x y z : BitVec w}

theorem add_ok {nuw nsw : Bool} (h : (nuw && x.uaddOverflow y || nsw && x.saddOverflow y) = false) :
    add (some x) (some y) nuw nsw = some (x + y) := by simp [add, h]

theorem sub_ok {nuw nsw : Bool} (h : (nuw && x.usubOverflow y || nsw && x.ssubOverflow y) = false) :
    sub (some x) (some y) nuw nsw = some (x - y) := by simp [sub, h]

theorem mul_ok {nuw nsw : Bool} (h : (nuw && x.umulOverflow y || nsw && x.smulOverflow y) = false) :
    mul (some x) (some y) nuw nsw = some (x * y) := by simp [mul, h]

theorem or_ok {disjoint : Bool} (h : (disjoint && x &&& y != 0#w) = false) :
    or (some x) (some y) disjoint = some (x ||| y) := by simp [or, h]

theorem shl_ok {nuw nsw : Bool}
    (h : (!decide (y < BitVec.ofNat w w) || nuw && (x <<< y) >>> y != x ||
      nsw && (x <<< y).sshiftRight' y != x) = false) :
    shl (some x) (some y) nuw nsw = some (x <<< y) := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨a, b⟩, c⟩ := h
  have a' : (!shiftOk y) = false := a
  simp only [shl, a', b, c, Bool.false_eq_true, ite_false]

theorem lshr_ok {exact : Bool}
    (h : (!decide (y < BitVec.ofNat w w) || exact && (x >>> y) <<< y != x) = false) :
    lshr (some x) (some y) exact = some (x >>> y) := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨a, b⟩ := h
  have a' : (!shiftOk y) = false := a
  simp only [lshr, a', b, Bool.false_eq_true, ite_false]

theorem ashr_ok {exact : Bool}
    (h : (!decide (y < BitVec.ofNat w w) || exact && (x.sshiftRight' y) <<< y != x) = false) :
    ashr (some x) (some y) exact = some (x.sshiftRight' y) := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨a, b⟩ := h
  have a' : (!shiftOk y) = false := a
  simp only [ashr, a', b, Bool.false_eq_true, ite_false]

theorem zext_ok {nneg : Bool} (h : (nneg && x.msb) = false) :
    zext v (some x) nneg = some (x.setWidth v) := by simp [zext, h]

theorem sext_some : sext v (some x) = some (x.signExtend v) := rfl

theorem trunc_ok {nuw nsw : Bool}
    (h : (nuw && (x.setWidth v).setWidth w != x || nsw && (x.setWidth v).signExtend w != x) = false) :
    trunc v (some x) nuw nsw = some (x.setWidth v) := by
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨a, b⟩ := h
  simp only [trunc, a, b, Bool.false_eq_true, ite_false]

theorem icmp_ok {p : BitVec w → BitVec w → Bool} {samesign : Bool} (h : (samesign && x.msb != y.msb) = false) :
    icmp p (some x) (some y) samesign = some (BitVec.ofBool (p x y)) := by simp [icmp, h]

theorem range_ok {lo hi : BitVec w} (h : (BitVec.ult (x - lo) (hi - lo)) = true) :
    range lo hi (some x) = some x := by simp [range, h]

theorem ctlz_ok {zeroPoison : Bool} (h : (zeroPoison && x == 0#w) = false) :
    ctlz (some x) zeroPoison = some x.clz := by simp [ctlz, h]

theorem cttz_ok {zeroPoison : Bool} (h : (zeroPoison && x == 0#w) = false) :
    cttz (some x) zeroPoison = some x.ctz := by simp [cttz, h]

theorem fshl_some {s : BitVec w} : fshl (some x) (some y) (some s) = some (fshlRaw x y s) := rfl

theorem fshr_some {s : BitVec w} : fshr (some x) (some y) (some s) = some (fshrRaw x y s) := rfl

/-- Rotating in one bit, which is how a double-width shift comes out of the optimizer. -/
theorem fshlRaw_one_32 (x y : BitVec 32) : fshlRaw x y 1#32 = (x <<< 1#32) ||| (y >>> 31#32) := by
  simp [fshlRaw]

theorem fshlRaw_one_64 (x y : BitVec 64) : fshlRaw x y 1#64 = (x <<< 1#64) ||| (y >>> 63#64) := by
  simp [fshlRaw]

theorem udiv_ok (h : (y == 0#w) = false) : udiv (some x) (some y) = Outcome.ok (some (x / y)) := by
  simp [udiv, h]

theorem urem_ok (h : (y == 0#w) = false) : urem (some x) (some y) = Outcome.ok (some (x % y)) := by
  simp [urem, h]

theorem ctpop_some : ctpop (some x) = some x.cpop := rfl

theorem bitreverse_some : bitreverse (some x) = some x.reverse := rfl

theorem abs_ok {intMinPoison : Bool} (h : (intMinPoison && x == BitVec.intMin w) = false) :
    abs (some x) intMinPoison = some (if x.msb then -x else x) := by simp [abs, h]

theorem umin_some : umin (some x) (some y) = some (if BitVec.ule x y then x else y) := rfl
theorem umax_some : umax (some x) (some y) = some (if BitVec.ule x y then y else x) := rfl
theorem smin_some : smin (some x) (some y) = some (if BitVec.sle x y then x else y) := rfl
theorem smax_some : smax (some x) (some y) = some (if BitVec.sle x y then y else x) := rfl

end Val

theorem assume_ok {α : Type} {x : BitVec 1} {k : Outcome α} (h : x = 1#1) : assume (some x) k = k := by
  simp [assume, h]

theorem ite_some {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by split <;> rfl

theorem ite_except_ok {ε α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (Except.ok a : Except ε α) else Except.ok b) = Except.ok (if c then a else b) := by split <;> rfl

theorem run_ite {β ρ : Type} (step : β → Outcome (Next β ρ)) (c : Prop) [Decidable c] (a b : β) :
    run step (if c then a else b) = if c then run step a else run step b := by split <;> rfl

theorem ite_cases {α : Type} {c : Prop} [Decidable c] {a b r : α} (ht : c → a = r) (he : ¬c → b = r) :
    (if c then a else b) = r := by
  split
  · exact ht ‹_›
  · exact he ‹_›

theorem result_congr {τ : Type} {x y : τ} (h : x = y) :
    (some (.ok (some x)) : Outcome (Option τ)) = some (.ok (some y)) := by rw [h]

theorem andThen_error {α β : Type} (e : Stop) (k : α → Outcome β) :
    andThen (some (Except.error e)) k = some (Except.error e) := rfl

theorem andThen_some {α β : Type} (x : α) (k : α → Outcome β) : andThen (some (Except.ok x)) k = k x := rfl

/-- A `select` for `&&`, which is how a short-circuit comes out of the optimizer. -/
theorem ofBool_ite_and (c : Prop) [Decidable c] (b : Bool) :
    (if c then BitVec.ofBool b else 0#1) = BitVec.ofBool (decide c && b) := by
  by_cases h : c <;> simp [h]

theorem observe_free {t : List Tag} (hfree : ∀ x, x ∈ t → x.noAddress = false) {α : Type} {block : Nat}
    {off : BitVec 64} (nullCheck : Bool) (k : Outcome α) :
    Mem.observeAddress (some ⟨block, off, t⟩) nullCheck k = k := by
  have h : t.any (fun x => x.noAddress && !(nullCheck && x.nullCheck)) = false := by
    rw [List.any_eq_false]
    intro x hx
    simp [hfree x hx]
  simp only [Mem.observeAddress, h, Bool.false_eq_true, ite_false]

theorem toVal_some {m : Mem} {p : Ptr} : Mem.toVal m (some p) = some (m.addr p) := rfl

end IRLean

/-- Works out what it can of a block, or of what's left of one. Each `br` becomes an `if`. Whatever `bv_decide` can't
discharge stays in the goal. -/
macro "llvm_simp " "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := first | bv_decide | omega) only [$extra:simpLemma,*, llvm_val, IRLean.ite_some, IRLean.ite_except_ok,
      IRLean.Val.add_ok, IRLean.Val.sub_ok, IRLean.Val.mul_ok, IRLean.Val.or_ok, IRLean.Val.shl_ok,
      IRLean.Val.lshr_ok, IRLean.Val.ashr_ok, IRLean.Val.zext_ok, IRLean.Val.sext_some,
      IRLean.Val.trunc_ok, IRLean.Val.icmp_ok, IRLean.Val.range_ok, IRLean.Val.ctlz_ok,
      IRLean.Val.cttz_ok, IRLean.Val.ctpop_some, IRLean.Val.bitreverse_some, IRLean.Val.abs_ok,
      IRLean.Val.umin_some, IRLean.Val.umax_some, IRLean.Val.smin_some, IRLean.Val.smax_some,
      IRLean.Val.udiv_ok, IRLean.Val.urem_ok, IRLean.Val.fshl_some, IRLean.Val.fshr_some, IRLean.Val.fshlRaw_one_32, IRLean.Val.fshlRaw_one_64,
      IRLean.assume_ok, IRLean.Val.icmpEq, IRLean.Val.icmpNe, IRLean.Val.icmpUlt, IRLean.Val.icmpUgt,
      IRLean.Val.icmpSlt, IRLean.Val.icmpSle, IRLean.Val.icmpSgt, IRLean.Val.icmpSge, IRLean.Val.icmpUle,
      IRLean.Val.icmpUge, IRLean.jump, IRLean.ret, IRLean.Outcome.ok, IRLean.Outcome.stop, IRLean.andThen_some,
      IRLean.andThen_error, IRLean.run_ite, IRLean.ofBool_ite_and, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq, reduceIte])

/-- Runs one block of an emitted function, whose `step` is given. -/
macro "llvm_step " step:ident : tactic => `(tactic| (rw [IRLean.run]; llvm_simp [$step:ident]))

/-- Runs an emitted function's blocks from its entry, on any input, to a `ret` on every path: `f` is the function,
and each `br` it reaches becomes a case split, with its condition as a hypothesis. Whatever `bv_decide` can't
discharge stays in the goal. -/
macro "llvm_exec " f:ident : tactic => do
  let step := Lean.mkIdent (f.getId ++ `step)
  `(tactic| (
    simp only [$f:ident, IRLean.noundef_some]
    repeat' (first
      | llvm_step $step:ident
      | (apply IRLean.ite_cases <;> intro _))))

/-- Finishes what `llvm_exec` left: a result to compare, leaving it to `bv_decide`, or a path whose conditions can't
hold. Paths that `simp` merged into an `if` are split back apart. -/
syntax "llvm_close" : tactic
macro_rules
  | `(tactic| llvm_close) =>
    `(tactic| first
      | with_reducible rfl
      | (apply IRLean.result_congr; bv_decide)
      | (exfalso; bv_decide)
      | (split <;> (try llvm_simp [IRLean.jump]) <;> llvm_close))
