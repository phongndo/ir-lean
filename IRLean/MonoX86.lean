import IRLean.Mono
import IRLean.X86
import IRLean.X86Bits
import IRLean.X86Arith
import IRLean.X86Crypto

/-! # x86's intrinsics keep refinement

The cut lemma asks that the code after a cut keeps refinement, `IRLean/Mono.lean` proves it of the model's generic
operations, and this proves it of every x86 intrinsic the emitter translates: the 250 of `IRLean/X86.lean`,
`X86Bits.lean`, `X86Arith.lean` and `X86Crypto.lean`, which are 41 functions of the model, and `vzeroupper`, which
the emitter translates as nothing.

Each of them is poison in a lane of its result where a lane it's computed from is, and otherwise a function of those
lanes' values, so each keeps refinement. How the proof goes depends on which lanes a result lane reads:

- **The same lane of each operand.** `Mono.map_strict`, `map2_strict` and `map3_strict`: a lane-wise operation built
  from a function that's poison where an operand is keeps refinement. That covers PTERNLOG, PBLENDVB, PAVG, PSIGN,
  PMULHW, PMULHUW, PMULHRSW, GF2P8MULB, PSLLV, PSRLV, PSRAV, AESIMC and AESKEYGENASSIST, and BZHI, BEXTR and CRC32
  on scalars, by `Refine.val_map₂_mono`.
- **Other lanes, at fixed places.** Each has its own lemma, since what it reads is its own: PMADDUBSW, PMADDWD,
  VPDPBUSD, VPDPBUSDS, VPDPWSSD, VPDPWSSDS, PACKSS and PACKUS, PHADD, PHADDS, PHSUB and PHSUBS, PCLMULQDQ, the AES
  rounds, GF2P8AFFINEQB and GF2P8AFFINEINVQB, PSADBW, PTEST and PHMINPOSUW. Those that fold over lanes go through
  `Mono.foldl` and `foldr`.
- **A lane picked by a value.** PSHUFB: the byte of `b` says which byte of `a` to take. Where the source's byte of `b`
  is a value the target's is the same, so they take the same byte.
- **A count or a mask for every lane.** PSLL, PSRL and PSRA by an immediate or by a vector's low quadword, and the
  masked down-converting moves VPMOV, VPMOVS and VPMOVUS: poison in the count or the mask is poison in every lane.

`refine_mono_simd` is `refine_mono` with these, and with the generic lemmas added since it was written. -/

namespace IRLean

namespace Mono

open Refine

/-- A value the source has, poison or the same in the target, split into its two cases. -/
theorem opt_cases {x x' : Option τ} (h : x = none ∨ x' = x) : x = none ∨ ∃ v, x = some v ∧ x' = some v := by
  rcases h with h | h
  · exact .inl h
  · rw [h]
    cases x with
    | none => exact .inl rfl
    | some v => exact .inr ⟨v, rfl, rfl⟩

/-- `opt_cases`, as an eliminator. -/
theorem opt_elim {x x' : Option τ} (h : x = none ∨ x' = x) {P : Prop} (hn : x = none → P)
    (hs : ∀ v, x = some v → x' = some v → P) : P := by
  rcases opt_cases h with h | ⟨v, h, h'⟩
  · exact hn h
  · exact hs v h h'

/-- A value a function reads, where it's poison if the value is, given `h : x = none ∨ x' = x`: where the source's is
poison the goal is closed, and otherwise both sides' are rewritten to the same value. -/
macro "strict_opt " h:term : tactic =>
  `(tactic|
    (refine Mono.opt_elim $h (fun h' => by rw [h']; first | exact True.intro | exact Or.inl rfl)
        (fun _ h' h'' => ?_) <;>
      rw [h', h'']))

/-- The same, from `h : Refine.le x x'` for values. -/
macro "strict_lane " h:term : tactic => `(tactic| strict_opt (Refine.val_iff _ _).1 $h)

namespace X86

variable {n m w u k : Nat}

/-! ### The same lane of each operand -/

theorem pternlog {imm : Nat} {a a' b b' c c' : Vec n w} (ha : Refine.le a a') (hb : Refine.le b b')
    (hc : Refine.le c c') : Refine.le (IRLean.X86.pternlog imm a b c) (IRLean.X86.pternlog imm a' b' c') :=
  map3_strict (by intros; rfl) (by intro a _; cases a <;> rfl) (by intro a b; cases a <;> cases b <;> rfl) ha hb hc

theorem pblendvb {a a' b b' c c' : Vec n 8} (ha : Refine.le a a') (hb : Refine.le b b') (hc : Refine.le c c') :
    Refine.le (IRLean.X86.pblendvb a b c) (IRLean.X86.pblendvb a' b' c') :=
  map3_strict (by intros; rfl) (by intro a _; cases a <;> rfl) (by intro a b; cases a <;> cases b <;> rfl) ha hb hc

theorem pavg {a a' b b' : Vec n w} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pavg a b) (IRLean.X86.pavg a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem psign {a a' b b' : Vec n w} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.psign a b) (IRLean.X86.psign a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem pmulhw {a a' b b' : Vec n 16} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pmulhw a b) (IRLean.X86.pmulhw a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem pmulhuw {a a' b b' : Vec n 16} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pmulhuw a b) (IRLean.X86.pmulhuw a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem pmulhrsw {a a' b b' : Vec n 16} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pmulhrsw a b) (IRLean.X86.pmulhrsw a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem gf2p8mulb {a a' b b' : Vec n 8} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.gf2p8mulb a b) (IRLean.X86.gf2p8mulb a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

/-- PSLLV, PSRLV and PSRAV. -/
theorem shiftLanes {s : IRLean.X86.Shift} {a a' b b' : Vec n w} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.shiftLanes s a b) (IRLean.X86.shiftLanes s a' b') :=
  map2_strict (by intros; rfl) (by intro a; cases a <;> rfl) ha hb

theorem aesimc {a a' : Vec n 64} (ha : Refine.le a a') : Refine.le (IRLean.X86.aesimc a) (IRLean.X86.aesimc a') :=
  map_strict rfl ha

theorem aeskeygenassist {imm : Nat} {a a' : Vec n 64} (ha : Refine.le a a') :
    Refine.le (IRLean.X86.aeskeygenassist imm a) (IRLean.X86.aeskeygenassist imm a') :=
  map_strict rfl ha

theorem bzhi {x x' c c' : Val w} (hx : Refine.le x x') (hc : Refine.le c c') :
    Refine.le (IRLean.X86.bzhi x c) (IRLean.X86.bzhi x' c') :=
  val_map₂_mono (f := IRLean.X86.bzhi) (fun _ => rfl) (fun a => by cases a <;> rfl) hx hc

theorem bextr {x x' c c' : Val w} (hx : Refine.le x x') (hc : Refine.le c c') :
    Refine.le (IRLean.X86.bextr x c) (IRLean.X86.bextr x' c') :=
  val_map₂_mono (f := IRLean.X86.bextr) (fun _ => rfl) (fun a => by cases a <;> rfl) hx hc

theorem crc32 {c : Nat} {x x' : Val c} {d d' : Val k} (hx : Refine.le x x') (hd : Refine.le d d') :
    Refine.le (IRLean.X86.crc32 x d) (IRLean.X86.crc32 x' d') :=
  val_map₂_mono (f := IRLean.X86.crc32) (fun _ => rfl) (fun a => by cases a <;> rfl) hx hd

/-! ### Other lanes, at fixed places -/

theorem pmaddubsw {a a' b b' : Vec m 8} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pmaddubsw n a b) (IRLean.X86.pmaddubsw n a' b') := fun i => by
  simp only [IRLean.X86.pmaddubsw, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane lane ha (2 * i.val)
  strict_lane lane ha (2 * i.val + 1)
  strict_lane lane hb (2 * i.val)
  strict_lane lane hb (2 * i.val + 1)
  exact refl_val _

theorem pmaddwd {a a' b b' : Vec m 16} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pmaddwd n a b) (IRLean.X86.pmaddwd n a' b') := fun i => by
  simp only [IRLean.X86.pmaddwd, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane lane ha (2 * i.val)
  strict_lane lane ha (2 * i.val + 1)
  strict_lane lane hb (2 * i.val)
  strict_lane lane hb (2 * i.val + 1)
  exact refl_val _

/-- The four products VPDPBUSD and VPDPBUSDS add: poison where a byte is, and otherwise the same on both sides. -/
theorem dot4 {a a' b b' : Vec m 8} (ha : Refine.le a a') (hb : Refine.le b b') (i : Nat) :
    IRLean.X86.dot4 a b i = none ∨ IRLean.X86.dot4 a' b' i = IRLean.X86.dot4 a b i := by
  simp only [IRLean.X86.dot4]
  strict_lane lane ha (4 * i)
  strict_lane lane ha (4 * i + 1)
  strict_lane lane ha (4 * i + 2)
  strict_lane lane ha (4 * i + 3)
  strict_lane lane hb (4 * i)
  strict_lane lane hb (4 * i + 1)
  strict_lane lane hb (4 * i + 2)
  strict_lane lane hb (4 * i + 3)
  exact .inr rfl

/-- The two products VPDPWSSD and VPDPWSSDS add. -/
theorem dot2 {a a' b b' : Vec m 16} (ha : Refine.le a a') (hb : Refine.le b b') (i : Nat) :
    IRLean.X86.dot2 a b i = none ∨ IRLean.X86.dot2 a' b' i = IRLean.X86.dot2 a b i := by
  simp only [IRLean.X86.dot2]
  strict_lane lane ha (2 * i)
  strict_lane lane ha (2 * i + 1)
  strict_lane lane hb (2 * i)
  strict_lane lane hb (2 * i + 1)
  exact .inr rfl

theorem vpdpbusd {acc acc' : Vec n 32} {a a' b b' : Vec m 8} (hacc : Refine.le acc acc') (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (IRLean.X86.vpdpbusd acc a b) (IRLean.X86.vpdpbusd acc' a' b') := fun i => by
  simp only [IRLean.X86.vpdpbusd, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane getElem hacc i.val i.isLt
  strict_opt dot4 ha hb i.val
  exact refl_val _

theorem vpdpbusds {acc acc' : Vec n 32} {a a' b b' : Vec m 8} (hacc : Refine.le acc acc') (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (IRLean.X86.vpdpbusds acc a b) (IRLean.X86.vpdpbusds acc' a' b') := fun i => by
  simp only [IRLean.X86.vpdpbusds, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane getElem hacc i.val i.isLt
  strict_opt dot4 ha hb i.val
  exact refl_val _

theorem vpdpwssd {acc acc' : Vec n 32} {a a' b b' : Vec m 16} (hacc : Refine.le acc acc') (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (IRLean.X86.vpdpwssd acc a b) (IRLean.X86.vpdpwssd acc' a' b') := fun i => by
  simp only [IRLean.X86.vpdpwssd, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane getElem hacc i.val i.isLt
  strict_opt dot2 ha hb i.val
  exact refl_val _

theorem vpdpwssds {acc acc' : Vec n 32} {a a' b b' : Vec m 16} (hacc : Refine.le acc acc') (ha : Refine.le a a')
    (hb : Refine.le b b') : Refine.le (IRLean.X86.vpdpwssds acc a b) (IRLean.X86.vpdpwssds acc' a' b') := fun i => by
  simp only [IRLean.X86.vpdpwssds, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane getElem hacc i.val i.isLt
  strict_opt dot2 ha hb i.val
  exact refl_val _

/-- PACKSSWB, PACKSSDW, PACKUSWB and PACKUSDW: each lane is the saturation of one lane, of `a` or of `b`. -/
theorem pack {sat : BitVec u → BitVec w} {a a' b b' : Vec m u} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pack sat n a b) (IRLean.X86.pack sat n a' b') := fun i => by
  simp only [IRLean.X86.pack, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · strict_lane lane ha (↑i / (2 * (128 / u)) * (128 / u) + ↑i % (128 / u))
    exact Reflexive.refl _
  · strict_lane lane hb (↑i / (2 * (128 / u)) * (128 / u) + ↑i % (128 / u))
    exact Reflexive.refl _

theorem packss {a a' b b' : Vec m u} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.packss n w a b) (IRLean.X86.packss n w a' b') := pack ha hb

theorem packus {a a' b b' : Vec m u} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.packus n w a b) (IRLean.X86.packus n w a' b') := pack ha hb

/-- PHADDW, PHADDD, PHADDSW, PHSUBW, PHSUBD and PHSUBSW: `f` of two neighbouring lanes, which has to keep refinement
itself. The emitter gives `Val.add`, `Val.saddSat`, `Val.sub` and `Val.ssubSat`. -/
theorem horizontal {f f' : Val w → Val w → Val w}
    (hf : ∀ x x' y y', Refine.le x x' → Refine.le y y' → Refine.le (f x y) (f' x' y')) {a a' b b' : Vec n w}
    (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.horizontal f a b) (IRLean.X86.horizontal f' a' b') := fun i => by
  simp only [IRLean.X86.horizontal, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · exact hf _ _ _ _ (lane ha _) (lane ha _)
  · exact hf _ _ _ _ (lane hb _) (lane hb _)

/-- PCLMULQDQ: each 128-bit block reads the quadword of each operand the immediate picks, and nothing else. -/
theorem pclmulqdq {imm : Nat} {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pclmulqdq imm a b) (IRLean.X86.pclmulqdq imm a' b') := fun i => by
  simp only [IRLean.X86.pclmulqdq, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane lane ha (2 * (↑i / 2) + if imm.testBit 0 = true then 1 else 0)
  strict_lane lane hb (2 * (↑i / 2) + if imm.testBit 4 = true then 1 else 0)
  exact refl_val _

/-- An AES round: each quadword reads both quadwords of its block of the state, and its own of the round key. -/
theorem aesRound {f : BitVec 128 → BitVec 128} {a a' key key' : Vec n 64} (ha : Refine.le a a')
    (hk : Refine.le key key') :
    Refine.le (IRLean.X86.aesRound f a key) (IRLean.X86.aesRound f a' key') := fun i => by
  simp only [IRLean.X86.aesRound, Fin.getElem_fin, Vector.getElem_ofFn]
  strict_lane lane ha (2 * (↑i / 2))
  strict_lane lane ha (2 * (↑i / 2) + 1)
  strict_lane lane hk ↑i
  exact refl_val _

theorem aesenc {a a' key key' : Vec n 64} (ha : Refine.le a a') (hk : Refine.le key key') :
    Refine.le (IRLean.X86.aesenc a key) (IRLean.X86.aesenc a' key') := aesRound ha hk
theorem aesenclast {a a' key key' : Vec n 64} (ha : Refine.le a a') (hk : Refine.le key key') :
    Refine.le (IRLean.X86.aesenclast a key) (IRLean.X86.aesenclast a' key') := aesRound ha hk
theorem aesdec {a a' key key' : Vec n 64} (ha : Refine.le a a') (hk : Refine.le key key') :
    Refine.le (IRLean.X86.aesdec a key) (IRLean.X86.aesdec a' key') := aesRound ha hk
theorem aesdeclast {a a' key key' : Vec n 64} (ha : Refine.le a a') (hk : Refine.le key key') :
    Refine.le (IRLean.X86.aesdeclast a key) (IRLean.X86.aesdeclast a' key') := aesRound ha hk

/-- GF2P8AFFINEQB and GF2P8AFFINEINVQB: each byte reads that byte of `x` and the eight bytes of its quadword of the
matrix, joined by a fold. -/
theorem affine {f : BitVec 8 → BitVec 8} {imm : Nat} {x x' mat mat' : Vec n 8} (hx : Refine.le x x')
    (hm : Refine.le mat mat') :
    Refine.le (IRLean.X86.affine f imm x mat) (IRLean.X86.affine f imm x' mat') := fun i => by
  simp only [IRLean.X86.affine, Fin.getElem_fin, Vector.getElem_ofFn]
  -- The quadword of the matrix, as each side folds it.
  generalize hr : List.foldr (fun (j : Nat) (acc : Val 64) => _) (some 0#64) (List.range 8) = rows
  generalize hr' : List.foldr (fun (j : Nat) (acc : Val 64) => _) (some 0#64) (List.range 8) = rows'
  have hrows : Refine.le rows rows' := by
    rw [← hr, ← hr']
    refine Mono.foldr (R := Refine.le) (fun j acc acc' hacc => ?_) _ (refl_val _)
    strict_lane lane hm (8 * (↑i / 8) + j)
    strict_lane hacc
    exact refl_val _
  strict_lane getElem hx i.val i.isLt
  strict_lane hrows
  exact refl_val _

theorem gf2p8affineqb {imm : Nat} {x x' mat mat' : Vec n 8} (hx : Refine.le x x') (hm : Refine.le mat mat') :
    Refine.le (IRLean.X86.gf2p8affineqb imm x mat) (IRLean.X86.gf2p8affineqb imm x' mat') := affine hx hm
theorem gf2p8affineinvqb {imm : Nat} {x x' mat mat' : Vec n 8} (hx : Refine.le x x') (hm : Refine.le mat mat') :
    Refine.le (IRLean.X86.gf2p8affineinvqb imm x mat) (IRLean.X86.gf2p8affineinvqb imm x' mat') := affine hx hm

/-- PSADBW: each quadword reads sixteen bytes, through a fold. -/
theorem psadbw {a a' b b' : Vec m 8} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.psadbw n a b) (IRLean.X86.psadbw n a' b') := fun i => by
  simp only [IRLean.X86.psadbw, Fin.getElem_fin, Vector.getElem_ofFn]
  refine Mono.foldl (R := Refine.le) (fun acc acc' j hacc => ?_) _ (refl_val _)
  strict_lane hacc
  strict_lane lane ha (8 * ↑i + j)
  strict_lane lane hb (8 * ↑i + j)
  exact refl_val _

/-- PTEST's flags, from every lane of both operands. -/
theorem ptestFlags {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    IRLean.X86.ptestFlags a b = none ∨ IRLean.X86.ptestFlags a' b' = IRLean.X86.ptestFlags a b := by
  simp only [IRLean.X86.ptestFlags]
  refine Mono.foldl (R := fun x y => x = none ∨ y = x) (fun acc acc' j hacc => ?_) _ (.inr rfl)
  rcases opt_cases hacc with h | ⟨⟨z, c⟩, h, h'⟩
  · rw [h]; exact .inl rfl
  · rw [h, h']
    strict_lane ha j
    strict_lane hb j
    exact .inr rfl

theorem ptestz {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.ptestz a b) (IRLean.X86.ptestz a' b') := by
  simp only [IRLean.X86.ptestz]
  rcases ptestFlags ha hb with h | h <;> rw [h]
  · trivial
  · exact refl_val _
theorem ptestc {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.ptestc a b) (IRLean.X86.ptestc a' b') := by
  simp only [IRLean.X86.ptestc]
  rcases ptestFlags ha hb with h | h <;> rw [h]
  · trivial
  · exact refl_val _
theorem ptestnzc {a a' b b' : Vec n 64} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.ptestnzc a b) (IRLean.X86.ptestnzc a' b') := by
  simp only [IRLean.X86.ptestnzc]
  rcases ptestFlags ha hb with h | h <;> rw [h]
  · trivial
  · exact refl_val _

/-- `Option.map` of a value the source has, poison or the same in the target. -/
theorem opt_map {f : τ → BitVec w} {x y : Option τ} (h : x = none ∨ y = x) :
    Refine.le (x.map f : Val w) (y.map f) := by
  rcases h with h | h <;> rw [h]
  · trivial
  · exact refl_val _

/-- PHMINPOSUW: lanes 0 and 1 read every lane, through a fold, and the others are 0. -/
theorem phminposuw {a a' : Vec n 16} (ha : Refine.le a a') :
    Refine.le (IRLean.X86.phminposuw a) (IRLean.X86.phminposuw a') := fun i => by
  simp only [IRLean.X86.phminposuw, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · refine opt_map (Mono.foldl (R := fun x y => x = none ∨ y = x) (fun acc acc' j hacc => ?_) _ ?_)
    · rcases opt_cases hacc with h | ⟨⟨least, index⟩, h, h'⟩
      · rw [h]; exact .inl rfl
      · rw [h, h']
        strict_lane lane ha (j + 1)
        exact .inr rfl
    · strict_lane lane ha 0
      exact .inr rfl
  · split
    · refine opt_map (Mono.foldl (R := fun x y => x = none ∨ y = x) (fun acc acc' j hacc => ?_) _ ?_)
      · rcases opt_cases hacc with h | ⟨⟨least, index⟩, h, h'⟩
        · rw [h]; exact .inl rfl
        · rw [h, h']
          strict_lane lane ha (j + 1)
          exact .inr rfl
      · strict_lane lane ha 0
        exact .inr rfl
    · exact refl_val _

/-! ### A lane picked by a value -/

/-- PSHUFB: where the source's byte of `b` is a value, the target's is the same, and picks the same byte of `a`. -/
theorem pshufb {a a' b b' : Vec n 8} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (IRLean.X86.pshufb a b) (IRLean.X86.pshufb a' b') := fun i => by
  simp only [IRLean.X86.pshufb, Fin.getElem_fin, Vector.getElem_ofFn]
  rcases opt_cases ((val_iff _ _).1 (lane hb ↑i)) with h | ⟨s, h, h'⟩
  · rw [h]; trivial
  · rw [h, h']
    dsimp only
    strict_lane lane ha (↑i / 16 * 16 + s.toNat % 16)
    exact refl_val _

/-! ### A count or a mask for every lane -/

/-- PSLLI, PSRLI and PSRAI: a poison count is poison in every lane. -/
theorem shiftImm {s : IRLean.X86.Shift} {a a' : Vec n w} {c c' : Val 32} (ha : Refine.le a a')
    (hc : Refine.le c c') : Refine.le (IRLean.X86.shiftImm s a c) (IRLean.X86.shiftImm s a' c') := by
  cases c with
  | none => exact PoisonLeast.poison_le _
  | some c => cases hc; exact map_strict rfl ha

/-- PSLL, PSRL and PSRA: the count is the low quadword of `c`, from its lanes, poison if one of them is. -/
theorem shiftVec {s : IRLean.X86.Shift} {a a' : Vec n w} {c c' : Vec m u} (ha : Refine.le a a')
    (hc : Refine.le c c') : Refine.le (IRLean.X86.shiftVec s a c) (IRLean.X86.shiftVec s a' c') := by
  simp only [IRLean.X86.shiftVec]
  -- The count, as each side folds it from `c`'s lanes.
  generalize hn : List.foldr (fun (j : Nat) (acc : Option Nat) => _) (some 0) (List.range (64 / u)) = count
  generalize hn' : List.foldr (fun (j : Nat) (acc : Option Nat) => _) (some 0) (List.range (64 / u)) = count'
  have hcount : count = none ∨ count' = count := by
    rw [← hn, ← hn']
    refine Mono.foldr (R := fun x y => x = none ∨ y = x) (fun j acc acc' hacc => ?_) _ (.inr rfl)
    strict_lane lane hc j
    rcases hacc with h | h
    · rw [h]; exact .inl rfl
    · rw [h]; exact .inr rfl
  rcases hcount with h | h <;> rw [h]
  · exact PoisonLeast.poison_le _
  · split
    · exact PoisonLeast.poison_le _
    · exact map_strict rfl ha

/-- VPMOV, VPMOVS and VPMOVUS with a mask: a poison mask is poison in every lane, and otherwise each lane below is the
lane of `a` or of `passthru` the mask picks. -/
theorem maskNarrow {f : BitVec u → BitVec w} {a a' : Vec m u} {p p' : Vec n w} {mask mask' : Val k}
    (ha : Refine.le a a') (hp : Refine.le p p') (hmask : Refine.le mask mask') :
    Refine.le (IRLean.X86.maskNarrow f a p mask) (IRLean.X86.maskNarrow f a' p' mask') := by
  cases mask with
  | none => exact PoisonLeast.poison_le _
  | some mask =>
    cases hmask
    intro i
    simp only [IRLean.X86.maskNarrow, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · split
      · strict_lane lane ha ↑i
        exact Reflexive.refl _
      · exact getElem hp i.val i.isLt
    · exact refl_val _

theorem pmov {a a' : Vec m u} {p p' : Vec n w} {mask mask' : Val k} (ha : Refine.le a a') (hp : Refine.le p p')
    (hmask : Refine.le mask mask') : Refine.le (IRLean.X86.pmov a p mask) (IRLean.X86.pmov a' p' mask') :=
  maskNarrow ha hp hmask
theorem pmovs {a a' : Vec m u} {p p' : Vec n w} {mask mask' : Val k} (ha : Refine.le a a') (hp : Refine.le p p')
    (hmask : Refine.le mask mask') : Refine.le (IRLean.X86.pmovs a p mask) (IRLean.X86.pmovs a' p' mask') :=
  maskNarrow ha hp hmask
theorem pmovus {a a' : Vec m u} {p p' : Vec n w} {mask mask' : Val k} (ha : Refine.le a a') (hp : Refine.le p p')
    (hmask : Refine.le mask mask') : Refine.le (IRLean.X86.pmovus a p mask) (IRLean.X86.pmovus a' p' mask') :=
  maskNarrow ha hp hmask

end X86

/-! ### Structs -/

theorem fst [Refine α] [Refine β] {p p' : α × β} (h : Refine.le p p') : Refine.le p.1 p'.1 := h.1
theorem snd [Refine α] [Refine β] {p p' : α × β} (h : Refine.le p p') : Refine.le p.2 p'.2 := h.2
theorem pair [Refine α] [Refine β] {a a' : α} {b b' : β} (ha : Refine.le a a') (hb : Refine.le b b') :
    Refine.le (a, b) (a', b') := ⟨ha, hb⟩

end Mono

/-- A step `refine_mono_simd` takes when none of its own lemmas matches. Modules that import this one add
alternatives with `macro_rules`, as `IRLean/MemRefineOps.lean` does for memory's lemmas on values; with none, it
fails. -/
syntax "refine_mono_ext" : tactic

macro_rules
  | `(tactic| refine_mono_ext) => `(tactic| fail "no lemma for this operation")

/-- `refine_mono`, with the lemmas since: x86's intrinsics, `IRLean/Lanes.lean`'s forms, floating point, `sdiv`,
`srem`, the funnel shifts, the overflow intrinsics, `Vec.reduce`, scalable vectors' lane moves, and a struct's fields. Each lemma is matched by the
operation's name, as `refine_mono` does, and what neither closes is left. Floating point's lemmas are for the same
choice on both sides. `refine_mono_ext` is tried last, so a module can add lemmas. -/
macro "refine_mono_simd" : tactic =>
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
    | refine Mono.map2 (fun _ _ _ _ _ _ => ?_) ?_ ?_ | refine Mono.map (fun _ _ _ => ?_) ?_
    | refine Mono.fshl ?_ ?_ ?_ | refine Mono.fshr ?_ ?_ ?_ | refine Mono.sdiv ?_ ?_ | refine Mono.srem ?_ ?_
    | refine Mono.uaddWithOverflow ?_ ?_ | refine Mono.saddWithOverflow ?_ ?_
    | refine Mono.usubWithOverflow ?_ ?_ | refine Mono.ssubWithOverflow ?_ ?_
    | refine Mono.umulWithOverflow ?_ ?_ | refine Mono.smulWithOverflow ?_ ?_ | refine Mono.withOverflow ?_ ?_
    | refine Mono.fst ?_ | refine Mono.snd ?_ | refine Mono.pair ?_ ?_
    | refine Mono.reduce (fun _ _ _ _ _ _ => ?_) ?_
    | refine Mono.map3 (fun _ _ _ _ _ _ _ _ _ => ?_) ?_ ?_ ?_
    | refine Mono.map2Pair (fun _ _ _ _ _ _ => ?_) ?_ ?_
    | refine Mono.mapOutcome2 (fun _ _ _ _ _ _ => ?_) ?_ ?_
    | refine Mono.fneg ?_ | refine Mono.fabs ?_ | refine Mono.selected ?_ | refine Mono.isFPClass ?_
    | refine Mono.nofpclass ?_ | refine Mono.fconv ?_ | refine Mono.fptoui ?_ | refine Mono.fptosi ?_
    | refine Mono.fptouiSat ?_ | refine Mono.fptosiSat ?_ | refine Mono.uitofp ?_ | refine Mono.sitofp ?_
    | refine Mono.copysign ?_ ?_ | refine Mono.fcmp ?_ ?_ | refine Mono.fadd ?_ ?_ | refine Mono.fsub ?_ ?_
    | refine Mono.fmul ?_ ?_ | refine Mono.fdiv ?_ ?_ | refine Mono.frem ?_ ?_
    | refine Mono.lanes1 (fun _ _ _ _ => ?_) ?_ | refine Mono.lanes2 (fun _ _ _ _ _ _ _ => ?_) ?_ ?_
    | refine Mono.reverse ?_ | refine Mono.insertSub ?_ ?_ | refine Mono.extractSub ?_ | refine Mono.splat0 ?_
    | refine Mono.X86.pternlog ?_ ?_ ?_ | refine Mono.X86.pblendvb ?_ ?_ ?_ | refine Mono.X86.pavg ?_ ?_
    | refine Mono.X86.psign ?_ ?_ | refine Mono.X86.pmulhw ?_ ?_ | refine Mono.X86.pmulhuw ?_ ?_
    | refine Mono.X86.pmulhrsw ?_ ?_ | refine Mono.X86.gf2p8mulb ?_ ?_ | refine Mono.X86.shiftLanes ?_ ?_
    | refine Mono.X86.aesimc ?_ | refine Mono.X86.aeskeygenassist ?_ | refine Mono.X86.bzhi ?_ ?_
    | refine Mono.X86.bextr ?_ ?_ | refine Mono.X86.crc32 ?_ ?_ | refine Mono.X86.pmaddubsw ?_ ?_
    | refine Mono.X86.pmaddwd ?_ ?_ | refine Mono.X86.vpdpbusd ?_ ?_ ?_ | refine Mono.X86.vpdpbusds ?_ ?_ ?_
    | refine Mono.X86.vpdpwssd ?_ ?_ ?_ | refine Mono.X86.vpdpwssds ?_ ?_ ?_ | refine Mono.X86.packss ?_ ?_
    | refine Mono.X86.packus ?_ ?_ | refine Mono.X86.pack ?_ ?_
    | refine Mono.X86.horizontal (fun _ _ _ _ _ _ => ?_) ?_ ?_ | refine Mono.X86.pclmulqdq ?_ ?_
    | refine Mono.X86.aesenc ?_ ?_ | refine Mono.X86.aesenclast ?_ ?_ | refine Mono.X86.aesdec ?_ ?_
    | refine Mono.X86.aesdeclast ?_ ?_ | refine Mono.X86.aesRound ?_ ?_ | refine Mono.X86.gf2p8affineqb ?_ ?_
    | refine Mono.X86.gf2p8affineinvqb ?_ ?_ | refine Mono.X86.affine ?_ ?_ | refine Mono.X86.psadbw ?_ ?_
    | refine Mono.X86.ptestz ?_ ?_ | refine Mono.X86.ptestc ?_ ?_ | refine Mono.X86.ptestnzc ?_ ?_
    | refine Mono.X86.phminposuw ?_ | refine Mono.X86.pshufb ?_ ?_ | refine Mono.X86.shiftImm ?_ ?_
    | refine Mono.X86.shiftVec ?_ ?_ | refine Mono.X86.pmov ?_ ?_ ?_ | refine Mono.X86.pmovs ?_ ?_ ?_
    | refine Mono.X86.pmovus ?_ ?_ ?_ | refine Mono.X86.maskNarrow ?_ ?_ ?_
    | refine_mono_ext))

end IRLean
