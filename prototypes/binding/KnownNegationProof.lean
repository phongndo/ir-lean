import HeapView
import KnownNegation

/-! # The compiled `llvm::isKnownNegation` computes what #47's model computes

`KnownNegation` is `ir-lean`'s translation of `llvm::isKnownNegation`, compiled by the pinned clang from the pinned
`ValueTracking.cpp` with upstream's Release flags, after `cut.py` replaced its three calls out of the module with model
stops. `isKnownNegation` in `SimplifyAddModel.lean` is #47's hand-written model of the same C++. The theorem at the end
says: on every heap that holds two operands as `HeapView.lean` says, called with `NeedNSW` false and `AllowPoison`
true, as `simplifyAddInst` calls it, the compiled function returns the model's answer.

The cuts are on paths the theorem shows aren't taken: a constant wider than 64 bits, a vector, and `NeedNSW`. So the
theorem is about the cut function, and holds of the uncut one by an argument on paper, which `README.md` gives. -/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Binding

open IRLean CppCorrespondence.SimplifyAdd
open KnownNegation._ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb (step G0 G1 G2 G3 Block)

variable {w : Nat} {M : Mem} {loc : Locs w} {ty : Nat × Nat}

/-! ## What each read gives -/

theorem Header.load_id {l : Nat × Nat} {id : BitVec 8} {a : Alloc} (H : Header M l id ty a) (hc : M.calls = []) :
    Mem.loadInt 8 M (some (ptrOf l)) 8 = Outcome.ok (some id) :=
  load8 H.placed hc (by have := H.room; omega) H.align H.id

theorem Header.gep_type {l : Nat × Nat} {id : BitVec 8} {a : Alloc} (H : Header M l id ty a) :
    Mem.gep M (some (ptrOf l)) (some 8#64) (inbounds := true) (nuw := true) = some (obj l.1 (l.2 + 8)) :=
  gep_fwd H.placed (by have := H.room; omega)

theorem Header.load_type {l : Nat × Nat} {id : BitVec 8} {a : Alloc} (H : Header M l id ty a) (hc : M.calls = []) :
    Mem.loadPtr M (some (obj l.1 (l.2 + 8))) 8 = Outcome.ok (some (ptrOf ty)) :=
  loadPtr H.placed hc (by have := H.room; omega) (by have := H.align; omega) H.type

theorem Header.addr_ne_null {l : Nat × Nat} {id : BitVec 8} {a : Alloc} (H : Header M l id ty a) :
    (M.addr (ptrOf l) == M.addr Ptr.null) = false := by
  have h := H.placed.addr (o := l.2) (by have := H.room; omega)
  have := H.placed.base_pos
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e
  have e' := congrArg BitVec.toNat e
  simp only [ptrOf] at e'
  rw [h] at e'
  simp [Mem.addr, Ptr.null] at e'
  omega

theorem Header.addr_ne_null' {l : Nat × Nat} {id : BitVec 8} {a : Alloc} (H : Header M l id ty a) :
    (M.addr (ptrOf l) == 0#64) = false := by
  have := H.addr_ne_null
  simpa [Mem.addr, Ptr.null] using this

theorem TypeObj.gep {a : Alloc} {tw : BitVec 32} (T : TypeObj M ty a tw) :
    Mem.gep M (some (ptrOf ty)) (some 8#64) (inbounds := true) (nuw := true) = some (obj ty.1 (ty.2 + 8)) :=
  gep_fwd T.placed (by have := T.room; omega)

theorem TypeObj.load {a : Alloc} {tw : BitVec 32} (T : TypeObj M ty a tw) (hc : M.calls = []) :
    Mem.loadInt 32 M (some (obj ty.1 (ty.2 + 8))) 8 = Outcome.ok (some tw) :=
  load32 T.placed hc (by have := T.room; omega) (by have := T.align; omega) T.word

theorem sub_gep0 {n : Nat} {a : Alloc} {id : BitVec 8} (H : Header M (loc (.node n)) id ty a)
    (h64 : 64 ≤ (loc (.node n)).2) :
    Mem.gep M (some (ptrOf (loc (.node n)))) (some 18446744073709551552#64) (inbounds := true) =
      some (obj (loc (.node n)).1 ((loc (.node n)).2 - 64)) :=
  gep_back H.placed h64 (by have := H.room; omega) (by omega) (by decide)

theorem sub_gep1 {n : Nat} {a : Alloc} {id : BitVec 8} (H : Header M (loc (.node n)) id ty a)
    (h64 : 64 ≤ (loc (.node n)).2) :
    Mem.gep M (some (ptrOf (loc (.node n)))) (some 18446744073709551584#64) (inbounds := true) =
      some (obj (loc (.node n)).1 ((loc (.node n)).2 - 32)) :=
  gep_back H.placed (by omega) (by have := H.room; omega) (by omega) (by decide)

theorem sub_load {n : Nat} {a : Alloc} {id : BitVec 8} (H : Header M (loc (.node n)) id ty a) (hc : M.calls = [])
    {k : Nat} (hk : k = 64 ∨ k = 32) (h64 : 64 ≤ (loc (.node n)).2) {p : Ptr}
    (hp : ∀ i, i < 8 → a.bytes ((loc (.node n)).2 - k + i) = .ptr p i) :
    Mem.loadPtr M (some (obj (loc (.node n)).1 ((loc (.node n)).2 - k))) 8 = Outcome.ok (some p) :=
  loadPtr H.placed hc (by have := H.room; omega) (by have := H.align; omega) hp

theorem observe_obj {α : Type} (l : Nat × Nat) (b : Bool) (k : Outcome α) :
    Mem.observeAddress (some (ptrOf l)) b k = k := by
  simp [Mem.observeAddress, ptrOf]

theorem toVal_some' (p : Ptr) : Mem.toVal M (some p) = some (M.addr p) := rfl

theorem br_zero {β ρ : Type} (t e : β) : (br (some 0#1) t e : Outcome (Next β ρ)) = jump e := by simp [br]

theorem br_one {β ρ : Type} (t e : β) : (br (some 1#1) t e : Outcome (Next β ρ)) = jump t := by simp [br]

/-- Two identities the code can see are the same `Value *` exactly when their addresses are equal. -/
theorem View.addr_beq {x y : Operand w} {lo : Nat} (V : View M loc ty x y lo) {i j : Ident w}
    (hi : i ∈ reads x ++ reads y) (hj : j ∈ reads x ++ reads y) :
    (M.addr (ptrOf (loc i)) == M.addr (ptrOf (loc j))) = (j == i) := by
  by_cases h : i = j
  · subst h; simp
  · have hne : M.addr (ptrOf (loc i)) ≠ M.addr (ptrOf (loc j)) := fun e => h (V.distinct i hi j hj e)
    simp only [beq_eq_false_iff_ne.mpr hne]
    exact (beq_eq_false_iff_ne.mpr (Ne.symm h)).symm

theorem Holds.header {x : Operand w} (H : Holds M loc ty x) :
    ∃ id a, Header M (loc x.ident) id ty a ∧ (id = 46#8 ↔ x.isSub = true) ∧ (id = 5#8 ↔ x.isConstInt = true) := by
  cases H with
  | const c a h1 _ _ _ => exact ⟨_, _, h1, by simp [Operand.isSub], by simp [Operand.isConstInt]⟩
  | sub n nuw nsw x y a h1 _ _ _ _ _ => exact ⟨_, _, h1, by simp [Operand.isSub], by simp [Operand.isConstInt]⟩
  | other op id a h1 h2 h3 h4 h5 => exact ⟨_, _, h5, by simp [h1, h4], by simp [h2, h3]⟩

/-! ## Running blocks -/

/-- One block: `run` takes a step, and the step is worked out. -/
macro "kn_step" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ((conv => lhs; rw [IRLean.run]); simp only [$extra,*, step, G0.step, G1.step, G2.step, G3.step, andThen, llvm_val,
    noundef, jump, ret, Outcome.ok, observe_obj, toVal_some', br_zero, br_one, ite_true, ite_false, Bool.false_eq_true,
    Bool.true_eq_false, decide_true, decide_false, reduceIte, beq_self_eq_true]))

/-- Runs blocks until the left side is done. -/
macro "kn_run" "[" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat (kn_step [$extra,*]))

@[simp] theorem ident_sub {n : Nat} {nuw nsw : Bool} {a b : Operand w} :
    (Operand.sub n nuw nsw a b).ident = .node n := rfl

theorem mem_reads_sub {n : Nat} {nuw nsw : Bool} {a b : Operand w} :
    a.ident ∈ reads (.sub n nuw nsw a b) ∧ b.ident ∈ reads (.sub n nuw nsw a b) ∧
      Ident.node n ∈ reads (Operand.sub n nuw nsw a b) := by
  simp [reads, ident_mem_reads]

/-- The last part, once `X` is a `sub`: `Y = sub (B, A)`. -/
theorem swapped_sub {n : Nat} {nuw nsw : Bool} {xa xb y : Operand w} {lo : Nat}
    (V : View M loc ty (.sub n nuw nsw xa xb) y lo) :
    run step (.g2 (.if_then_i_i_i M (some (ptrOf (loc (.node n)))) (some (ptrOf (loc y.ident))))) =
      Outcome.ok (some (BitVec.ofBool (isKnownNegation.subSwapped (.sub n nuw nsw xa xb) y)), M) := by
  have hc := V.calls
  have HX := V.hx
  cases HX with
  | other op id a h1 _ _ _ _ => simp [Operand.isSub] at h1
  | sub _ _ _ _ _ a h1 h64 h0 h1' HA HB =>
    obtain ⟨_, _, HAh, -, -⟩ := HA.header
    obtain ⟨_, _, HBh, -, -⟩ := HB.header
    kn_step [sub_gep0 h1 h64, sub_load h1 hc (Or.inl rfl) h64 h0, HAh.addr_ne_null]
    kn_step [sub_gep1 h1 h64, sub_load h1 hc (Or.inr rfl) h64 h1', HBh.addr_ne_null]
    obtain ⟨idy, ay, Hy, hy46, -⟩ := V.hy.header
    kn_step [Hy.load_id hc]
    by_cases hys : y.isSub = true
    · have HY := V.hy
      cases HY with
      | const c b g1 _ _ _ => simp [Operand.isSub] at hys
      | other op id b g1 _ _ _ _ => simp [g1] at hys
      | sub m nuw' nsw' ya yb b g1 g64 g0 g1' _ _ =>
        have mx := mem_reads_sub (n := n) (nuw := nuw) (nsw := nsw) (a := xa) (b := xb)
        have my := mem_reads_sub (n := m) (nuw := nuw') (nsw := nsw') (a := ya) (b := yb)
        have e1 := V.addr_beq (i := ya.ident) (j := xb.ident) (by simp [my.1]) (by simp [mx.2.1])
        have e2 := V.addr_beq (i := yb.ident) (j := xa.ident) (by simp [my.2.1]) (by simp [mx.1])
        have hid : idy = 46#8 := hy46.mpr hys
        subst hid
        kn_step [ident_sub, sub_gep0 g1 g64, sub_load g1 hc (Or.inl rfl) g64 g0, e1]
        by_cases hb : xb.ident = ya.ident
        · kn_step [ident_sub, hb, sub_gep1 g1 g64, sub_load g1 hc (Or.inr rfl) g64 g1', e2]
          by_cases ha : xa.ident = yb.ident
          · kn_step [ha]
            simp [isKnownNegation.subSwapped, specific, hb, ha]
          · have ha' : (xa.ident == yb.ident) = false := by simpa using ha
            kn_step [ha']
            kn_step [Bool.false_eq_true]
            have : (yb.ident == xa.ident) = false := by simpa using Ne.symm ha
            simp [isKnownNegation.subSwapped, specific, hb, this]
        · have hb' : (xb.ident == ya.ident) = false := by simpa using hb
          kn_step [hb']
          kn_step [Bool.false_eq_true]
          have : (ya.ident == xb.ident) = false := by simpa using Ne.symm hb
          simp [isKnownNegation.subSwapped, specific, this]
    · have hne : (idy == 46#8) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hys (hy46.mp h)
      kn_step [hne]
      kn_step [Bool.false_eq_true]
      have : isKnownNegation.subSwapped (.sub n nuw nsw xa xb) y = false := by
        cases y <;> simp_all [isKnownNegation.subSwapped, Operand.isSub]
      simp [this]

/-- The last part: `X = sub (A, B)` and `Y = sub (B, A)`, with `NeedNSW` false. Nothing here writes memory. -/
theorem swapped {x y : Operand w} {lo : Nat} (V : View M loc ty x y lo) :
    run step (.g1 (.if_end M (some (ptrOf (loc x.ident))) (some (ptrOf (loc y.ident))) (some 0#1))) =
      Outcome.ok (some (BitVec.ofBool (isKnownNegation.subSwapped x y)), M) := by
  have hc := V.calls
  obtain ⟨idx, ax, Hx, hx46, -⟩ := V.hx.header
  kn_step [Hx.load_id hc]
  by_cases hxs : x.isSub = true
  · obtain ⟨n, nuw, nsw, xa, xb, rfl⟩ : ∃ n nuw nsw xa xb, x = .sub n nuw nsw xa xb := by
      cases x <;> simp_all [Operand.isSub]
    have h46 : idx = 46#8 := hx46.mpr hxs
    subst h46
    kn_step [ident_sub]
    exact swapped_sub V
  · have hne : (idx == 46#8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hxs (hx46.mp h)
    kn_step [hne]
    kn_step [Bool.false_eq_true]
    have : isKnownNegation.subSwapped x y = false := by
      cases x <;> simp_all [isKnownNegation.subSwapped, Operand.isSub]
    simp [this]

/-! ## The stack slots the function allocates -/

/-- The two slots the function allocates, at `M.next` and `M.next + 1`, are placed where its accesses are valid. -/
def StackRoom (M : Mem) : Prop :=
  ∀ k, k < 2 → 0 < (M.base (M.next + k)).toNat ∧ (M.base (M.next + k)).toNat % 8 = 0 ∧
    (M.base (M.next + k)).toNat + 16 < 2 ^ 64

/-- A live slot: `deadSlot` after `llvm.lifetime.start`, perhaps written since. -/
theorem placed_slot {M : Mem} {s : Nat} {a : Alloc} (ha : M.allocs s = some a) (hs : s ≠ 0) (hsz : a.size = 16)
    (h : 0 < (M.base s).toNat ∧ (M.base s).toNat % 8 = 0 ∧ (M.base s).toNat + 16 < 2 ^ 64) : Placed M s a :=
  ⟨ha, hs, h.1, h.2.1, by rw [hsz]; exact h.2.2, by rw [hsz]; decide⟩

@[simp] theorem ident_const {c : BitVec w} : (Operand.const c).ident = .const c := rfl

theorem width_ok (hw : w ≤ 64) : BitVec.ult (BitVec.ofNat 32 w) 65#32 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem zero_iff (hw : w ≤ 64) (c : BitVec w) : (c.setWidth 64 == 0#64) = (c == 0#w) := by
  have hc := c.isLt
  have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  by_cases h : c = 0#w
  · subst h; simp
  · have h' : c.setWidth 64 ≠ 0#64 := by
      intro e
      apply h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

/-- The first part: `X = 0 - Y`. It allocates both slots, writes `Y` into the second, which `m_Specific(Y)` reads,
and ends that slot's lifetime either way. -/
theorem part1 {x y : Operand w} (hw : w ≤ 64) (V : View M loc ty x y M.next) (R : StackRoom M) :
    ∃ M6, View M6 loc ty x y M.next ∧ M6.allocs M.next = some deadSlot ∧ M6.next = M.next + 2 ∧
      M6.base = M.base ∧
      run step (.g0 (.entry M (some (ptrOf (loc x.ident))) (some (ptrOf (loc y.ident))) (some 0#1) (some 1#1))) =
        if isKnownNegation.negationOf x y then Outcome.ok (some 1#1, M6)
        else run step (.g0 (.lor_lhs_false M6 (some (ptrOf (loc x.ident))) (some (ptrOf (loc y.ident)))
          (some 0#1) (some 1#1) (some ⟨M.next, 0#64, []⟩))) := by
  have hc := V.calls
  obtain ⟨tA, tw, T⟩ := V.type
  have hn0 : M.next ≠ 0 := by have := V.typeBelow; omega
  obtain ⟨M1, e1, S1, a1, n1, b1⟩ := alloca16 M
  obtain ⟨M2, e2, S2, a2, n2, b2⟩ := alloca16 M1
  rw [n1] at a2 n2
  obtain ⟨M3, e3, S3, a3, n3⟩ := lifetime_slot M2 a2 (by omega)
    (by intro h; have := (R 1 (by omega)).1; rw [b2, b1] at h; simp [h] at this) true
  have R1 := R 1 (by omega)
  have P3 := placed_slot (M := M3) a3 (by omega) (by simp [deadSlot])
    (by rw [S3.base, b2, b1]; exact R1)
  obtain ⟨M4, e4, S4, n4, a4, hA4, hs4, hr4, -, -⟩ := storePtr_slot P3 (o := 0) (by simp) (by
    rw [S3.calls, S2.calls, S1.calls]; exact hc) (by simp [deadSlot]) (by decide) Ptr.null
  have P4 := placed_slot (M := M4) hA4 (by omega) (by rw [hs4]; simp [deadSlot])
    (by rw [S4.base, S3.base, b2, b1]; exact R1)
  have g4 := gep_fwd P4 (o := 0) (k := 8) (by rw [hs4]; simp [deadSlot])
  simp only [Nat.zero_add] at g4
  have hc4 : M4.calls = [] := by rw [S4.calls, S3.calls, S2.calls, S1.calls]; exact hc
  obtain ⟨M5, e5, S5, n5, a5, hA5, hs5, hr5, -, hb5⟩ := storePtr_slot P4 (o := 8) (by rw [hr4]; simp)
    hc4 (by rw [hs4]; simp [deadSlot]) (by decide) (ptrOf (loc y.ident))
  have P5 := placed_slot (M := M5) hA5 (by omega) (by rw [hs5, hs4]; simp [deadSlot])
    (by rw [S5.base, S4.base, S3.base, b2, b1]; exact R1)
  have hc5 : M5.calls = [] := by rw [S5.calls]; exact hc4
  obtain ⟨M6, e6, S6, a6, n6⟩ := lifetime_slot M5 hA5 (by omega)
    (by intro h; have := R1.1; rw [S5.base, S4.base, S3.base, b2, b1] at h; simp [h] at this) false
  have V5 : View M5 loc ty x y M.next :=
    ((((V.same S1 (Nat.le_refl _)).same S2 (by omega)).same S3 (by omega)).same S4 (by omega)).same S5 (by omega)
  have V6 : View M6 loc ty x y M.next := V5.same S6 (by omega)
  have hy8 := loadPtr P5 hc5 (o := 8) (by rw [hs5, hs4]; simp [deadSlot]) (by decide) hb5
  refine ⟨M6, V6, ?_, ?_, ?_, ?_⟩
  · rw [S6.allocs _ (by omega), S5.allocs _ (by omega), S4.allocs _ (by omega), S3.allocs _ (by omega),
      S2.allocs _ (by omega)]
    exact a1
  · rw [n6, n5, n4, n3, n2]
  · rw [S6.base, S5.base, S4.base, S3.base, b2, b1]
  obtain ⟨idx, ax, Hx, hx46, -⟩ := V5.hx.header
  obtain ⟨tA5, tw5, T5⟩ := V5.type
  have eX := Hx.load_id hc5
  have hy5 : y.ident ∈ reads x ++ reads y := by simp [ident_mem_reads]
  -- What every path does to memory, and the model's own definitions, for `simp`.
  have ent := And.intro e1 (And.intro e2 (And.intro e3 (And.intro e4 (And.intro g4 (And.intro e5 e6)))))
  by_cases hxs : x.isSub = true
  · obtain ⟨n, nuw, nsw, xa, xb, rfl⟩ : ∃ n nuw nsw xa xb, x = .sub n nuw nsw xa xb := by
      cases x <;> simp_all [Operand.isSub]
    have h46 : idx = 46#8 := hx46.mpr hxs
    subst h46
    have HX := V5.hx
    cases HX with
    | other op id a h1 _ _ _ _ => simp [Operand.isSub] at h1
    | sub _ _ _ _ _ a h1 h64 h0 h1' HA HB =>
      have eXs := h1.load_id hc5
      have mx := mem_reads_sub (n := n) (nuw := nuw) (nsw := nsw) (a := xa) (b := xb)
      have eB := V5.addr_beq (i := xb.ident) (j := y.ident) (by simp [mx.2.1]) hy5
      have l0 := sub_load h1 hc5 (Or.inl rfl) h64 h0
      have l1 := sub_load h1 hc5 (Or.inr rfl) h64 h1'
      obtain ⟨ida, aa, HAh, -, ha5⟩ := HA.header
      by_cases hac : xa.isConstInt = true
      · obtain ⟨c, rfl⟩ : ∃ c, xa = .const c := by cases xa <;> simp_all [Operand.isConstInt]
        cases HA with
        | other op id b g1 g2 _ _ _ => simp [Operand.isConstInt] at g2
        | const _ b g1 g40 gw gv =>
          have ew := load32 g1.placed hc5 (o := (loc (.const c)).2 + 32) (by omega)
            (by have := g1.align; omega) gw
          have ev := load64 g1.placed hc5 (o := (loc (.const c)).2 + 24) (by omega)
            (by have := g1.align; omega) gv
          have g24 : Mem.gep M5 (some (ptrOf (loc (.const c)))) (some 24#64) (inbounds := true) (nuw := true) =
              some (obj (loc (.const c)).1 ((loc (.const c)).2 + 24)) :=
            gep_fwd g1.placed (o := (loc (.const c)).2) (k := 24) (by omega)
          have g32 : Mem.gep M5 (some (ptrOf (loc (.const c)))) (some 32#64) (inbounds := true) (nuw := true) =
              some (obj (loc (.const c)).1 ((loc (.const c)).2 + 32)) :=
            gep_fwd g1.placed (o := (loc (.const c)).2) (k := 32) (by omega)
          have el := g1.load_id hc5
          by_cases hc0 : c = 0#w
          · subst hc0
            by_cases hby : xb.ident = y.ident
            · have hb1 : (y.ident == xb.ident) = true := by simp [hby]
              have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const 0#w) xb) y = true := by
                simp [isKnownNegation.negationOf, zeroInt, cstPred, specific, hby]
              kn_run [hm, ent.1, ent.2.1, n1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2.1, ent.2.2.2.2.2.2, eXs,
                ident_sub, ident_const, sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw,
                sub_gep1 h1 h64, l1, hy8, eB, hb1]
            · have hb0 : (y.ident == xb.ident) = false := by simpa using Ne.symm hby
              have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const 0#w) xb) y = false := by
                have : (xb.ident == y.ident) = false := by simpa using hby
                simp [isKnownNegation.negationOf, zeroInt, cstPred, specific, this]
              kn_run [hm, ent.1, ent.2.1, n1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2.1, ent.2.2.2.2.2.2, eXs,
                ident_sub, ident_const, sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw,
                sub_gep1 h1 h64, l1, hy8, eB, hb0]
          · have hz : (c == 0#w) = false := by simpa using hc0
            have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const c) xb) y = false := by
              simp [isKnownNegation.negationOf, zeroInt, cstPred, hz]
            kn_run [hm, ent.1, ent.2.1, n1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2.1, ent.2.2.2.2.2.2, eXs,
              ident_sub, ident_const, sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw, hz]
      · have hne : (ida == 5#8) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hac (ha5.mp h)
        have hv : (tw5 &&& 254#32 == 18#32) = false := by simpa using T5.scalar
        have hm : isKnownNegation.negationOf (.sub n nuw nsw xa xb) y = false := by
          have : zeroInt xa = false := by cases xa <;> simp_all [zeroInt, cstPred, Operand.isConstInt]
          simp [isKnownNegation.negationOf, this]
        kn_run [hm, ent.1, ent.2.1, n1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2.1, ent.2.2.2.2.2.2, eXs,
          ident_sub, sub_gep0 h1 h64, l0, HAh.load_id hc5, hne, HAh.gep_type, HAh.load_type hc5, T5.gep,
          T5.load hc5, hv]
  · have hne : (idx == 46#8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hxs (hx46.mp h)
    have hm : isKnownNegation.negationOf x y = false := by
      cases x <;> simp_all [isKnownNegation.negationOf, Operand.isSub]
    kn_run [hm, ent.1, ent.2.1, n1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2.1, ent.2.2.2.2.2.1, ent.2.2.2.2.2.2, eX, hne]

/-- The second part: `Y = 0 - X`, with the first slot, which holds `X` for `m_Specific(X)`. -/
theorem part2 {x y : Operand w} {lo s : Nat} (hw : w ≤ 64) (V : View M loc ty x y lo) (hs : lo ≤ s) (hs0 : s ≠ 0)
    (ha : M.allocs s = some deadSlot)
    (R : 0 < (M.base s).toNat ∧ (M.base s).toNat % 8 = 0 ∧ (M.base s).toNat + 16 < 2 ^ 64) :
    ∃ M9, View M9 loc ty x y lo ∧
      run step (.g0 (.lor_lhs_false M (some (ptrOf (loc x.ident))) (some (ptrOf (loc y.ident))) (some 0#1)
          (some 1#1) (some ⟨s, 0#64, []⟩))) =
        if isKnownNegation.negationOf y x then Outcome.ok (some 1#1, M9)
        else run step (.g1 (.if_end M9 (some (ptrOf (loc x.ident))) (some (ptrOf (loc y.ident))) (some 0#1))) := by
  have hc := V.calls
  obtain ⟨M3, e3, S3, a3, n3⟩ := lifetime_slot M ha hs0 (by intro h; have := R.1; simp [h] at this) true
  have P3 := placed_slot (M := M3) a3 hs0 (by simp [deadSlot]) (by rw [S3.base]; exact R)
  obtain ⟨M4, e4, S4, n4, a4, hA4, hs4, hr4, -, -⟩ := storePtr_slot P3 (o := 0) (by simp) (by
    rw [S3.calls]; exact hc) (by simp [deadSlot]) (by decide) Ptr.null
  have P4 := placed_slot (M := M4) hA4 hs0 (by rw [hs4]; simp [deadSlot]) (by rw [S4.base, S3.base]; exact R)
  have g4 := gep_fwd P4 (o := 0) (k := 8) (by rw [hs4]; simp [deadSlot])
  simp only [Nat.zero_add] at g4
  have hc4 : M4.calls = [] := by rw [S4.calls, S3.calls]; exact hc
  obtain ⟨M5, e5, S5, n5, a5, hA5, hs5, hr5, -, hb5⟩ := storePtr_slot P4 (o := 8) (by rw [hr4]; simp)
    hc4 (by rw [hs4]; simp [deadSlot]) (by decide) (ptrOf (loc x.ident))
  have P5 := placed_slot (M := M5) hA5 hs0 (by rw [hs5, hs4]; simp [deadSlot])
    (by rw [S5.base, S4.base, S3.base]; exact R)
  have hc5 : M5.calls = [] := by rw [S5.calls]; exact hc4
  obtain ⟨M6, e6, S6, a6, n6⟩ := lifetime_slot M5 hA5 hs0
    (by intro h; have := R.1; rw [S5.base, S4.base, S3.base] at h; simp [h] at this) false
  have V5 : View M5 loc ty x y lo := ((V.same S3 hs).same S4 hs).same S5 hs
  have V6 : View M6 loc ty x y lo := V5.same S6 hs
  have hx8 := loadPtr P5 hc5 (o := 8) (by rw [hs5, hs4]; simp [deadSlot]) (by decide) hb5
  refine ⟨M6, V6, ?_⟩
  obtain ⟨idy, ay, Hy, hy46, -⟩ := V5.hy.header
  obtain ⟨tA5, tw5, T5⟩ := V5.type
  have eY := Hy.load_id hc5
  have hx5 : x.ident ∈ reads x ++ reads y := by simp [ident_mem_reads]
  have ent := And.intro e3 (And.intro e4 (And.intro g4 (And.intro e5 e6)))
  by_cases hys : y.isSub = true
  · obtain ⟨n, nuw, nsw, ya, yb, rfl⟩ : ∃ n nuw nsw ya yb, y = .sub n nuw nsw ya yb := by
      cases y <;> simp_all [Operand.isSub]
    have h46 : idy = 46#8 := hy46.mpr hys
    subst h46
    have HY := V5.hy
    cases HY with
    | other op id a h1 _ _ _ _ => simp [Operand.isSub] at h1
    | sub _ _ _ _ _ a h1 h64 h0 h1' HA HB =>
      have eYs := h1.load_id hc5
      have my := mem_reads_sub (n := n) (nuw := nuw) (nsw := nsw) (a := ya) (b := yb)
      have eB := V5.addr_beq (i := yb.ident) (j := x.ident) (by simp [my.2.1]) hx5
      have l0 := sub_load h1 hc5 (Or.inl rfl) h64 h0
      have l1 := sub_load h1 hc5 (Or.inr rfl) h64 h1'
      obtain ⟨ida, aa, HAh, -, ha5⟩ := HA.header
      by_cases hac : ya.isConstInt = true
      · obtain ⟨c, rfl⟩ : ∃ c, ya = .const c := by cases ya <;> simp_all [Operand.isConstInt]
        cases HA with
        | other op id b g1 g2 _ _ _ => simp [Operand.isConstInt] at g2
        | const _ b g1 g40 gw gv =>
          have ew := load32 g1.placed hc5 (o := (loc (.const c)).2 + 32) (by omega)
            (by have := g1.align; omega) gw
          have ev := load64 g1.placed hc5 (o := (loc (.const c)).2 + 24) (by omega)
            (by have := g1.align; omega) gv
          have g24 : Mem.gep M5 (some (ptrOf (loc (.const c)))) (some 24#64) (inbounds := true) (nuw := true) =
              some (obj (loc (.const c)).1 ((loc (.const c)).2 + 24)) :=
            gep_fwd g1.placed (o := (loc (.const c)).2) (k := 24) (by omega)
          have g32 : Mem.gep M5 (some (ptrOf (loc (.const c)))) (some 32#64) (inbounds := true) (nuw := true) =
              some (obj (loc (.const c)).1 ((loc (.const c)).2 + 32)) :=
            gep_fwd g1.placed (o := (loc (.const c)).2) (k := 32) (by omega)
          have el := g1.load_id hc5
          by_cases hc0 : c = 0#w
          · subst hc0
            by_cases hbx : yb.ident = x.ident
            · have hb1 : (x.ident == yb.ident) = true := by simp [hbx]
              have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const 0#w) yb) x = true := by
                simp [isKnownNegation.negationOf, zeroInt, cstPred, specific, hbx]
              kn_run [hm, ent.1, ent.2.1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2, eYs, ident_sub, ident_const,
                sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw, sub_gep1 h1 h64, l1, hx8, eB,
                hb1]
            · have hb0 : (x.ident == yb.ident) = false := by simpa using Ne.symm hbx
              have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const 0#w) yb) x = false := by
                have : (yb.ident == x.ident) = false := by simpa using hbx
                simp [isKnownNegation.negationOf, zeroInt, cstPred, specific, this]
              kn_run [hm, ent.1, ent.2.1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2, eYs, ident_sub, ident_const,
                sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw, sub_gep1 h1 h64, l1, hx8, eB,
                hb0]
          · have hz : (c == 0#w) = false := by simpa using hc0
            have hm : isKnownNegation.negationOf (.sub n nuw nsw (.const c) yb) x = false := by
              simp [isKnownNegation.negationOf, zeroInt, cstPred, hz]
            kn_run [hm, ent.1, ent.2.1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2, eYs, ident_sub, ident_const,
              sub_gep0 h1 h64, l0, el, g24, g32, ew, width_ok hw, ev, zero_iff hw, hz]
      · have hne : (ida == 5#8) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hac (ha5.mp h)
        have hv : (tw5 &&& 254#32 == 18#32) = false := by simpa using T5.scalar
        have hm : isKnownNegation.negationOf (.sub n nuw nsw ya yb) x = false := by
          have : zeroInt ya = false := by cases ya <;> simp_all [zeroInt, cstPred, Operand.isConstInt]
          simp [isKnownNegation.negationOf, this]
        kn_run [hm, ent.1, ent.2.1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2, eYs, ident_sub, sub_gep0 h1 h64, l0,
          HAh.load_id hc5, hne, HAh.gep_type, HAh.load_type hc5, T5.gep, T5.load hc5, hv]
  · have hne : (idy == 46#8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hys (hy46.mp h)
    have hm : isKnownNegation.negationOf y x = false := by
      cases y <;> simp_all [isKnownNegation.negationOf, Operand.isSub]
    kn_run [hm, ent.1, ent.2.1, ent.2.2.1, ent.2.2.2.1, ent.2.2.2.2, eY, hne]

/-! ## The theorem -/

/-- **The compiled `llvm::isKnownNegation` returns #47's model's answer.** Called with `NeedNSW` false and
`AllowPoison` true, as `simplifyAddInst` calls it, on two `Value *`s that the heap holds as `x` and `y` with
`HeapView.lean`'s layout, at any width up to 64, the function the pinned clang compiled from the pinned
`ValueTracking.cpp` returns `isKnownNegation x y`, the model's, and doesn't stop or reach undefined behavior. -/
theorem isKnownNegation_compiled {x y : Operand w} (hw : w ≤ 64) (V : View M loc ty x y M.next)
    (R : StackRoom M) :
    ∃ M', KnownNegation._ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb (some (ptrOf (loc x.ident)))
        (some (ptrOf (loc y.ident))) (some 0#1) (some 1#1) M =
      Outcome.ok (some (BitVec.ofBool (isKnownNegation x y)), M') := by
  have V0 : View { M with frame := [] } loc ty x y M.next := V.same (same_frame M [] M.next) (Nat.le_refl _)
  have R0 : StackRoom { M with frame := [] } := R
  obtain ⟨M6, V6, a6, n6, b6, eq1⟩ := part1 (M := { M with frame := [] }) hw V0 R0
  have R6 : 0 < (M6.base M.next).toNat ∧ (M6.base M.next).toNat % 8 = 0 ∧ (M6.base M.next).toNat + 16 < 2 ^ 64 := by
    rw [b6]; simpa using R 0 (by omega)
  have hn0 : M.next ≠ 0 := by have := V.typeBelow; omega
  obtain ⟨M9, V9, eq2⟩ := part2 hw V6 (Nat.le_refl _) hn0 a6 R6
  have eq3 := swapped V9
  simp only [KnownNegation._ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb, noundef, Mem.withFrame]
  rw [eq1]
  by_cases h1 : isKnownNegation.negationOf x y = true
  · have hk : isKnownNegation x y = true := by simp [isKnownNegation, h1]
    simp only [h1, ite_true, promised_ok, andThen, Outcome.ok, hk]
    exact ⟨_, rfl⟩
  · rw [eq2]
    by_cases h2 : isKnownNegation.negationOf y x = true
    · have hk : isKnownNegation x y = true := by simp [isKnownNegation, h2]
      simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false, promised_ok, andThen, Outcome.ok, hk]
      exact ⟨_, rfl⟩
    · rw [eq3]
      have hk : isKnownNegation x y = isKnownNegation.subSwapped x y := by simp_all [isKnownNegation]
      simp only [h1, h2, Bool.false_eq_true, ite_false, promised_ok, andThen, Outcome.ok, hk]
      exact ⟨_, rfl⟩

/-! ## The hypotheses can hold

A heap with `X = sub i8 0, Y`, built here byte by byte: a type, the `sub` with its two `Use`s in front of it, the
`ConstantInt` 0 and an argument `Y`, and room for the two slots. `View` holds of it, so the theorem isn't vacuous, and
on it the compiled function returns true, as the model does. -/

namespace Example

/-- The type `i8`: its ID, 13, in the low byte of the word at offset 8. -/
def tyAlloc : Alloc :=
  { size := 16, readonly := false,
    bytes := fun j => if 8 ≤ j ∧ j < 12 then Mem.intByte (13#32) (j - 8) else .uninit }

def tyPtr : Ptr := obj 1 0

/-- The `sub`: two `Use`s, then the object at offset 64. -/
def subAlloc : Alloc :=
  { size := 80, readonly := false,
    bytes := fun j =>
      if j < 8 then .ptr (obj 3 0) j
      else if 32 ≤ j ∧ j < 40 then .ptr (obj 4 0) (j - 32)
      else if j = 64 then .val 46#8
      else if 72 ≤ j ∧ j < 80 then .ptr tyPtr (j - 72)
      else .uninit }

/-- The `ConstantInt` 0 of type `i8`. -/
def zeroAlloc : Alloc :=
  { size := 40, readonly := false,
    bytes := fun j =>
      if j = 0 then .val 5#8
      else if 8 ≤ j ∧ j < 16 then .ptr tyPtr (j - 8)
      else if 24 ≤ j ∧ j < 32 then Mem.intByte (0#64) (j - 24)
      else if 32 ≤ j ∧ j < 36 then Mem.intByte (8#32) (j - 32)
      else .uninit }

/-- An argument: its ID, 22, and its type. -/
def argAlloc : Alloc :=
  { size := 16, readonly := false,
    bytes := fun j => if j = 0 then .val 22#8 else if 8 ≤ j ∧ j < 16 then .ptr tyPtr (j - 8) else .uninit }

def heap : Mem :=
  { allocs := fun b =>
      if b = 1 then some tyAlloc else if b = 2 then some subAlloc else if b = 3 then some zeroAlloc
      else if b = 4 then some argAlloc else none
    next := 5
    base := fun b => BitVec.ofNat 64 (b * 4096)
    frame := [] }

def y : Operand 8 := .other 7

def x : Operand 8 := .sub 1 false false (.const 0#8) y

def place : Locs 8
  | .node 1 => (2, 64)
  | .const _ => (3, 0)
  | _ => (4, 0)

@[simp] theorem place_sub : place (.node 1) = (2, 64) := rfl
@[simp] theorem place_const (c : BitVec 8) : place (.const c) = (3, 0) := rfl
@[simp] theorem place_arg : place (.node 7) = (4, 0) := rfl
@[simp] theorem y_ident : y.ident = .node 7 := rfl
@[simp] theorem x_ident : x.ident = .node 1 := rfl

theorem placed (b : Nat) (a : Alloc) (h : heap.allocs b = some a) (h0 : b ≠ 0) (hb : b < 5) (hs : a.size ≤ 80) :
    Placed heap b a := by
  refine ⟨h, h0, ?_, ?_, ?_, by omega⟩ <;> simp [heap, BitVec.toNat_ofNat] <;> omega

theorem reads_xy : reads x ++ reads y = [.node 1, .const 0#8, .node 7, .node 7] := rfl

theorem view : View heap place (1, 0) x y 5 := by
  have hT := placed 1 tyAlloc (by simp [heap]) (by decide) (by decide) (by decide)
  have hS := placed 2 subAlloc (by simp [heap]) (by decide) (by decide) (by decide)
  have hZ := placed 3 zeroAlloc (by simp [heap]) (by decide) (by decide) (by decide)
  have hA := placed 4 argAlloc (by simp [heap]) (by decide) (by decide) (by decide)
  have hty : ptrOf (1, 0) = tyPtr := rfl
  have hy : Holds heap place (1, 0) y :=
    .other _ 22#8 argAlloc rfl rfl (by decide) (by decide)
      ⟨by simpa using hA, by simp, by simp [argAlloc], by simp [argAlloc], fun i hi => by
        simp [argAlloc, hty, show 8 + i ≠ 0 by omega, show 8 ≤ 8 + i by omega, show 8 + i < 16 by omega]⟩
  refine ⟨?_, hy, ⟨tyAlloc, 13#32, ⟨hT, by decide, by decide, fun i hi => ?_, by decide⟩⟩, ?_, rfl, ?_, by decide⟩
  · refine .sub 1 false false _ _ subAlloc ⟨by simpa using hS, by simp, by simp [subAlloc], by simp [subAlloc],
      fun i hi => ?_⟩ (by simp) (fun i hi => ?_) (fun i hi => ?_) ?_ hy
    · simp only [place_sub, hty]
      simp [subAlloc, show ¬ 64 + 8 + i < 8 by omega, show ¬ (32 ≤ 64 + 8 + i ∧ 64 + 8 + i < 40) by omega,
        show 64 + 8 + i ≠ 64 by omega, show 72 ≤ 64 + 8 + i by omega, show 64 + 8 + i < 80 by omega,
        show 64 + 8 + i - 72 = i by omega]
    · simp [subAlloc, hi, ptrOf]
    · simp [subAlloc, show ¬ 32 + i < 8 by omega, show 32 ≤ 32 + i by omega, show 32 + i < 40 by omega, ptrOf]
    · refine .const _ zeroAlloc ⟨by simpa using hZ, by simp, by simp [zeroAlloc], by simp [zeroAlloc],
        fun i hi => ?_⟩ (by simp [zeroAlloc]) (fun i hi => ?_) (fun i hi => ?_)
      · simp [zeroAlloc, hty, show 8 + i ≠ 0 by omega, show 8 ≤ 8 + i by omega, show 8 + i < 16 by omega]
      · simp [zeroAlloc, show 32 + i ≠ 0 by omega, show ¬ (8 ≤ 32 + i ∧ 32 + i < 16) by omega,
          show ¬ (24 ≤ 32 + i ∧ 32 + i < 32) by omega, show 32 ≤ 32 + i by omega, show 32 + i < 36 by omega]
      · simp [zeroAlloc, show 24 + i ≠ 0 by omega, show ¬ (8 ≤ 24 + i ∧ 24 + i < 16) by omega,
          show 24 ≤ 24 + i by omega, show 24 + i < 32 by omega]
  · simp [tyAlloc, show 8 ≤ 8 + i by omega, show 8 + i < 12 by omega]
  · rw [reads_xy]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl) j (rfl | rfl | rfl | rfl) h <;>
      first | rfl | (simp [Mem.addr, heap, ptrOf] at h)
  · rw [reads_xy]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl) <;> simp

theorem room : StackRoom heap := by
  intro k hk
  simp only [heap, BitVec.toNat_ofNat]
  omega

/-- On this heap, the compiled function says `X` is the negation of `Y`, as the model does. -/
theorem returns_true :
    ∃ M', KnownNegation._ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb (some (ptrOf (place x.ident)))
        (some (ptrOf (place y.ident))) (some 0#1) (some 1#1) heap = Outcome.ok (some 1#1, M') := by
  obtain ⟨M', h⟩ := isKnownNegation_compiled (by decide) view room
  exact ⟨M', by rw [h]; rfl⟩

end Example

end Binding
