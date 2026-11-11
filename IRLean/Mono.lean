import IRLean.Cut
import IRLean.Vec

/-! # Operations that keep refinement

The cut lemma, `IRLean/Cut.lean`, asks that the code after a cut keeps refinement: given a value where the source had
poison, it gives a result the source's allows. Being the same code on both sides isn't enough. `freeze` isn't
monotone, since it turns poison into a value of its own choosing, and nor is anything that stops the model on a value
and not on poison.

This proves it of the model's operations, one lemma each, named for the operation. Integer and vector operations give
`Refine.le` on values. Ones that can be undefined give `Refine.le` on runs where they can't stop the model, and
`Outcome.Sim` where they can. `refine_mono` chains them.

What's here is most of the model's integer, vector and control operations. `IRLean/MemRefine.lean` has memory's.
`sdiv`, `srem`, the funnel shifts, the overflow intrinsics and `Vec.reduce` have none yet, and nor do floating point,
`IRLean/Lanes.lean`'s lane-wise forms and x86's intrinsics, so code after a cut that uses one needs its own lemma, or a
cut whose replacement returns the same values, where reflexivity is enough. -/

namespace IRLean

/-- Types whose poison allows anything: what `select` on a poison condition needs. -/
class Refine.PoisonLeast (α : Type) [Refine α] [HasPoison α] : Prop where
  poison_le : ∀ a : α, Refine.le (HasPoison.poison : α) a

instance : Refine.PoisonLeast (Val w) := ⟨fun _ => trivial⟩

instance : Refine.PoisonLeast (Vec n w) :=
  ⟨fun a i => by
    show Refine.le (Vector.replicate n (none : Val w))[i] a[i]
    rw [Fin.getElem_fin, Vector.getElem_replicate]
    trivial⟩

instance : Refine.PoisonLeast Unit := ⟨fun _ => trivial⟩

instance [Refine α] [Refine β] [HasPoison α] [HasPoison β] [Refine.PoisonLeast α] [Refine.PoisonLeast β] :
    Refine.PoisonLeast (α × β) :=
  ⟨fun a => ⟨Refine.PoisonLeast.poison_le a.1, Refine.PoisonLeast.poison_le a.2⟩⟩

namespace Mono

open Refine

variable {w v u n : Nat}

/-! ### Integers -/

section Int
variable {a a' b b' : Val w}

theorem add {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.add a b nuw nsw) (Val.add a' b' nuw nsw) :=
  val_map₂_mono (f := fun a b => Val.add a b nuw nsw) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem sub {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.sub a b nuw nsw) (Val.sub a' b' nuw nsw) :=
  val_map₂_mono (f := fun a b => Val.sub a b nuw nsw) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem mul {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.mul a b nuw nsw) (Val.mul a' b' nuw nsw) :=
  val_map₂_mono (f := fun a b => Val.mul a b nuw nsw) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem and (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.and a b) (Val.and a' b') :=
  val_map₂_mono (f := Val.and) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb

theorem xor (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.xor a b) (Val.xor a' b') :=
  val_map₂_mono (f := Val.xor) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb

theorem or {disjoint : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.or a b disjoint) (Val.or a' b' disjoint) :=
  val_map₂_mono (f := fun a b => Val.or a b disjoint) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem shl {nuw nsw : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.shl a b nuw nsw) (Val.shl a' b' nuw nsw) :=
  val_map₂_mono (f := fun a b => Val.shl a b nuw nsw) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem lshr {exact : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.lshr a b exact) (Val.lshr a' b' exact) :=
  val_map₂_mono (f := fun a b => Val.lshr a b exact) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem ashr {exact : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.ashr a b exact) (Val.ashr a' b' exact) :=
  val_map₂_mono (f := fun a b => Val.ashr a b exact) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl)
    ha hb

theorem icmp {p : BitVec w → BitVec w → Bool} {samesign : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmp p a b samesign) (Val.icmp p a' b' samesign) :=
  val_map₂_mono (f := fun a b => Val.icmp p a b samesign) (fun b => by cases b <;> rfl)
    (fun a => by cases a <;> rfl) ha hb

theorem icmpEq {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpEq a b s) (Val.icmpEq a' b' s) := icmp ha hb
theorem icmpNe {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpNe a b s) (Val.icmpNe a' b' s) := icmp ha hb
theorem icmpUlt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUlt a b s) (Val.icmpUlt a' b' s) := icmp ha hb
theorem icmpUle {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUle a b s) (Val.icmpUle a' b' s) := icmp ha hb
theorem icmpUgt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUgt a b s) (Val.icmpUgt a' b' s) := icmp ha hb
theorem icmpUge {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpUge a b s) (Val.icmpUge a' b' s) := icmp ha hb
theorem icmpSlt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSlt a b s) (Val.icmpSlt a' b' s) := icmp ha hb
theorem icmpSle {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSle a b s) (Val.icmpSle a' b' s) := icmp ha hb
theorem icmpSgt {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSgt a b s) (Val.icmpSgt a' b' s) := icmp ha hb
theorem icmpSge {s : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.icmpSge a b s) (Val.icmpSge a' b' s) := icmp ha hb

theorem umin (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.umin a b) (Val.umin a' b') :=
  val_map₂_mono (f := Val.umin) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem umax (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.umax a b) (Val.umax a' b') :=
  val_map₂_mono (f := Val.umax) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem smin (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.smin a b) (Val.smin a' b') :=
  val_map₂_mono (f := Val.smin) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem smax (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.smax a b) (Val.smax a' b') :=
  val_map₂_mono (f := Val.smax) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb

theorem uaddSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.uaddSat a b) (Val.uaddSat a' b') :=
  val_map₂_mono (f := Val.uaddSat) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem usubSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.usubSat a b) (Val.usubSat a' b') :=
  val_map₂_mono (f := Val.usubSat) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem saddSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.saddSat a b) (Val.saddSat a' b') :=
  val_map₂_mono (f := Val.saddSat) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem ssubSat (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.ssubSat a b) (Val.ssubSat a' b') :=
  val_map₂_mono (f := Val.ssubSat) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb

theorem ucmp {v : Nat} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.ucmp v a b) (Val.ucmp v a' b') :=
  val_map₂_mono (f := Val.ucmp v) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb
theorem scmp {v : Nat} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.scmp v a b) (Val.scmp v a' b') :=
  val_map₂_mono (f := Val.scmp v) (fun b => by cases b <;> rfl) (fun a => by cases a <;> rfl) ha hb

theorem zext {v : Nat} {nneg : Bool} (ha : Refine.le a a') :
    Refine.le (Val.zext v a nneg) (Val.zext v a' nneg) :=
  val_map_mono (f := fun a => Val.zext v a nneg) rfl ha
theorem sext {v : Nat} (ha : Refine.le a a') : Refine.le (Val.sext v a) (Val.sext v a') :=
  val_map_mono (f := Val.sext v) rfl ha
theorem trunc {v : Nat} {nuw nsw : Bool} (ha : Refine.le a a') :
    Refine.le (Val.trunc v a nuw nsw) (Val.trunc v a' nuw nsw) :=
  val_map_mono (f := fun a => Val.trunc v a nuw nsw) rfl ha
theorem range {lo hi : BitVec w} (ha : Refine.le a a') : Refine.le (Val.range lo hi a) (Val.range lo hi a') :=
  val_map_mono (f := Val.range lo hi) rfl ha
theorem abs {p : Bool} (ha : Refine.le a a') : Refine.le (Val.abs a p) (Val.abs a' p) :=
  val_map_mono (f := fun a => Val.abs a p) rfl ha
theorem ctpop (ha : Refine.le a a') : Refine.le (Val.ctpop a) (Val.ctpop a') :=
  val_map_mono (f := Val.ctpop) rfl ha
theorem bitreverse (ha : Refine.le a a') : Refine.le (Val.bitreverse a) (Val.bitreverse a') :=
  val_map_mono (f := Val.bitreverse) rfl ha
theorem bswap (ha : Refine.le a a') : Refine.le (Val.bswap a) (Val.bswap a') :=
  val_map_mono (f := Val.bswap) rfl ha
theorem ctlz {p : Bool} (ha : Refine.le a a') : Refine.le (Val.ctlz a p) (Val.ctlz a' p) :=
  val_map_mono (f := fun a => Val.ctlz a p) rfl ha
theorem cttz {p : Bool} (ha : Refine.le a a') : Refine.le (Val.cttz a p) (Val.cttz a' p) :=
  val_map_mono (f := fun a => Val.cttz a p) rfl ha

/-- `udiv`: a poison or zero divisor is undefined in the source, and it never stops the model. -/
theorem udiv {exact : Bool} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (Val.udiv a b exact) (Val.udiv a' b' exact) := by
  cases b with
  | none => exact outcome_ub _ _
  | some y =>
    cases hb
    simp only [Val.udiv]
    split
    · exact outcome_ub _ _
    · cases a with
      | none => cases a' <;> exact (outcome_ok_ok _ _).2 trivial
      | some x => cases ha; exact (outcome_ok_ok _ _).2 (refl_val _)

theorem urem (ha : Refine.le a a') (hb : Refine.le b b') : Refine.le (Val.urem a b) (Val.urem a' b') := by
  cases b with
  | none => exact outcome_ub _ _
  | some y =>
    cases hb
    simp only [Val.urem]
    split
    · exact outcome_ub _ _
    · cases a with
      | none => cases a' <;> exact (outcome_ok_ok _ _).2 trivial
      | some x => cases ha; exact (outcome_ok_ok _ _).2 (refl_val _)

end Int

/-! ### `select`, and the instructions that end a block or can be undefined -/

theorem select [Refine α] [HasPoison α] [PoisonLeast α] {c c' : Val 1} {t t' e e' : α} (hc : Refine.le c c')
    (ht : Refine.le t t') (he : Refine.le e e') : Refine.le (IRLean.select c t e) (IRLean.select c' t' e') := by
  cases c with
  | none => exact PoisonLeast.poison_le _
  | some x =>
    cases hc
    simp only [IRLean.select]
    split
    · exact ht
    · exact he

/-- `noundef`: poison is undefined in the source. -/
theorem noundef {r : α → β → Prop} {x x' : Val w} {k : Outcome α} {k' : Outcome β} (hx : Refine.le x x')
    (hk : Outcome.Sim r k k') : Outcome.Sim r (IRLean.noundef x k) (IRLean.noundef x' k') := by
  cases x with
  | none => trivial
  | some y => cases hx; exact hk

/-- `llvm.assume`: anything but true is undefined in the source. -/
theorem assume {r : α → β → Prop} {c c' : Val 1} {k : Outcome α} {k' : Outcome β} (hc : Refine.le c c')
    (hk : Outcome.Sim r k k') : Outcome.Sim r (IRLean.assume c k) (IRLean.assume c' k') := by
  cases c with
  | none => trivial
  | some y =>
    cases hc
    simp only [IRLean.assume]
    split
    · exact hk
    · trivial

/-- `switch`: a poison selector is undefined in the source. -/
theorem sw {r : α → β → Prop} {x x' : Val w} {k : BitVec w → Outcome α} {k' : BitVec w → Outcome β}
    (hx : Refine.le x x') (hk : ∀ y, Outcome.Sim r (k y) (k' y)) :
    Outcome.Sim r (IRLean.sw x k) (IRLean.sw x' k') := by
  cases x with
  | none => trivial
  | some y => cases hx; exact hk y

/-- A branch whose arms are runs, as a recursive function has them. -/
theorem branch {r : α → β → Prop} {c c' : Val 1} {t e : Outcome α} {t' e' : Outcome β} (hc : Refine.le c c')
    (ht : Outcome.Sim r t t') (he : Outcome.Sim r e e') :
    Outcome.Sim r (IRLean.branch c t e) (IRLean.branch c' t' e') := by
  cases c with
  | none => trivial
  | some y =>
    cases hc
    simp only [IRLean.branch]
    split
    · exact ht
    · exact he

/-! ### Vectors, lane by lane -/

section Vec
variable {a a' : Vec n w}

theorem lane (ha : Refine.le a a') (i : Nat) : Refine.le (Vec.lane a i) (Vec.lane a' i) := by
  simp only [Vec.lane]
  split
  · rename_i h; exact ha ⟨i, h⟩
  · trivial

theorem map {f f' : Val w → Val v} (hf : ∀ x y, Refine.le x y → Refine.le (f x) (f' y)) (ha : Refine.le a a') :
    Refine.le (Vec.map f a) (Vec.map f' a') := fun i => by
  show Refine.le (Vector.map f a)[i] (Vector.map f' a')[i]
  rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_map]
  exact hf _ _ (ha i)

theorem map2 {f f' : Val w → Val u → Val v} {b b' : Vec n u}
    (hf : ∀ x x' y y', Refine.le x x' → Refine.le y y' → Refine.le (f x y) (f' x' y')) (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (Vec.map2 f a b) (Vec.map2 f' a' b') := fun i => by
  show Refine.le (Vector.ofFn fun i => f a[i] b[i])[i] (Vector.ofFn fun i => f' a'[i] b'[i])[i]
  rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact hf _ _ _ _ (ha i) (hb i)

theorem vselect {c c' : Vec n 1} {t t' e e' : Vec n w} (hc : Refine.le c c') (ht : Refine.le t t')
    (he : Refine.le e e') : Refine.le (Vec.select c t e) (Vec.select c' t' e') := fun i => by
  show Refine.le (Vector.ofFn fun i => IRLean.select c[i] t[i] e[i])[i]
    (Vector.ofFn fun i => IRLean.select c'[i] t'[i] e'[i])[i]
  rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact select (hc i) (ht i) (he i)

theorem extract {k : Nat} {i i' : Val k} (ha : Refine.le a a') (hi : Refine.le i i') :
    Refine.le (Vec.extract a i) (Vec.extract a' i') := by
  cases i with
  | none => trivial
  | some j => cases hi; exact lane ha _

theorem insert {k : Nat} {x x' : Val w} {i i' : Val k} (ha : Refine.le a a') (hx : Refine.le x x')
    (hi : Refine.le i i') : Refine.le (Vec.insert a x i) (Vec.insert a' x' i') := by
  cases i with
  | none => exact PoisonLeast.poison_le _
  | some j =>
    cases hi
    simp only [Vec.insert]
    split
    · rename_i h
      intro l
      rw [Fin.getElem_fin, Fin.getElem_fin, Vector.getElem_set, Vector.getElem_set]
      split
      · exact hx
      · exact ha l
    · exact PoisonLeast.poison_le _

theorem shuffle {k : Nat} {b b' : Vec n w} {mask : Array (Option Nat)} (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (Vec.shuffle k a b mask) (Vec.shuffle k a' b' mask) := fun i => by
  simp only [Vec.shuffle, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · split
    · exact lane ha _
    · exact lane hb _
  · trivial

/-- A scalar as a vector of one lane, which is how a `bitcast` of it starts. -/
theorem singleton {x x' : Val w} (hx : Refine.le x x') : Refine.le (#v[x] : Vec 1 w) #v[x'] := fun i => by
  match i with
  | ⟨0, _⟩ => exact hx

/-- `bitcast` to narrower lanes: a lane of the result is poison where the lane it's cut from is. -/
theorem split {m v k : Nat} (ha : Refine.le a a') : Refine.le (Vec.split m v k a) (Vec.split m v k a') :=
  fun i => by
    simp only [Vec.split, Fin.getElem_fin, Vector.getElem_ofFn]
    have h := lane ha (i.val / k)
    revert h
    cases Vec.lane a (i.val / k) with
    | none => intro _; trivial
    | some x => intro h; rw [(val_some _ _).1 h]; exact refl_val _

/-- `bitcast` to wider lanes: a lane of the result is poison where any lane it joins is. -/
theorem join {m v k : Nat} (ha : Refine.le a a') : Refine.le (Vec.join m v k a) (Vec.join m v k a') :=
  fun i => by
    simp only [Vec.join, Fin.getElem_fin, Vector.getElem_ofFn]
    induction List.range k with
    | nil => exact refl_val _
    | cons j rest ih =>
      simp only [List.foldr_cons]
      have h := lane ha (k * i.val + j)
      revert h ih
      generalize List.foldr _ _ rest = acc
      generalize List.foldr _ _ rest = acc'
      cases Vec.lane a (k * i.val + j) with
      | none => intro _ _; trivial
      | some x =>
        intro ih h
        rw [(val_some _ _).1 h]
        cases acc with
        | none => trivial
        | some y => rw [(val_some _ _).1 ih]; exact refl_val _

end Vec

end Mono

/-- Proves that an expression built from the model's integer and vector operations keeps refinement, from hypotheses
that its inputs refine: `IRLean.Mono`'s lemmas, chained. What it can't close, it leaves. Each lemma is matched by the
operation's name, without unfolding it, so a goal no lemma is for fails at once instead of being searched. It uses
`refine` and not `apply`, which reads a vector's `Refine.le` as the `∀` over lanes it unfolds to and doesn't come back
from 32 lanes. -/
macro "refine_mono" : tactic =>
  `(tactic| with_reducible repeat' (first
    | assumption
    | exact Refine.Reflexive.refl _
    | exact Refine.refl_val _
    | refine Mono.add ?_ ?_ | refine Mono.sub ?_ ?_ | refine Mono.mul ?_ ?_ | refine Mono.and ?_ ?_
    | refine Mono.xor ?_ ?_ | refine Mono.or ?_ ?_ | refine Mono.shl ?_ ?_ | refine Mono.lshr ?_ ?_
    | refine Mono.ashr ?_ ?_ | refine Mono.icmpEq ?_ ?_ | refine Mono.icmpNe ?_ ?_ | refine Mono.icmpUlt ?_ ?_
    | refine Mono.icmpUle ?_ ?_ | refine Mono.icmpUgt ?_ ?_ | refine Mono.icmpUge ?_ ?_ | refine Mono.icmpSlt ?_ ?_
    | refine Mono.icmpSle ?_ ?_ | refine Mono.icmpSgt ?_ ?_ | refine Mono.icmpSge ?_ ?_ | refine Mono.icmp ?_ ?_
    | refine Mono.umin ?_ ?_ | refine Mono.umax ?_ ?_ | refine Mono.smin ?_ ?_ | refine Mono.smax ?_ ?_
    | refine Mono.uaddSat ?_ ?_ | refine Mono.usubSat ?_ ?_ | refine Mono.saddSat ?_ ?_ | refine Mono.ssubSat ?_ ?_
    | refine Mono.ucmp ?_ ?_ | refine Mono.scmp ?_ ?_ | refine Mono.udiv ?_ ?_ | refine Mono.urem ?_ ?_
    | refine Mono.extract ?_ ?_ | refine Mono.shuffle ?_ ?_ | refine Mono.zext ?_ | refine Mono.sext ?_
    | refine Mono.trunc ?_ | refine Mono.range ?_ | refine Mono.abs ?_ | refine Mono.ctpop ?_
    | refine Mono.bitreverse ?_ | refine Mono.bswap ?_ | refine Mono.ctlz ?_ | refine Mono.cttz ?_
    | refine Mono.split ?_ | refine Mono.join ?_ | refine Mono.singleton ?_ | refine Mono.vselect ?_ ?_ ?_
    | refine Mono.select ?_ ?_ ?_ | refine Mono.insert ?_ ?_ ?_ | refine Mono.lane ?_ _
    | refine Mono.map2 (fun _ _ _ _ _ _ => ?_) ?_ ?_ | refine Mono.map (fun _ _ _ => ?_) ?_))

end IRLean
