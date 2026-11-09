import Vnni

open IRLean Llama.Vnni

/-! Saved by prototypes/lemma-reuse/q4k.py. -/

namespace LemmaReuse.Store

/-- What s02's rewrite computes from its operands is what clang's code does, given the facts. -/
theorem core_25cc0c39f5 (x0 : Vec 64 8) (x1 : Vec 64 8) (x2 : Vec 64 8) (x3 : Vec 64 8) (x4 : Vec 64 8) (x5 : Vec 64 8) (x6 : Vec 64 8) (x7 : Vec 64 8) (x8 : Vec 64 8) (x9 : Vec 64 8) (x10 : Vec 64 8) (x11 : Vec 64 8) (x12 : Vec 64 8) (x13 : Vec 64 8) (x14 : Vec 64 8) (x15 : Vec 64 8) (x16 : Vec 32 16)
    (h0 : Nibbles x0) (h2 : Nibbles x2) (h4 : Nibbles x4) (h6 : Nibbles x6) (h8 : Nibbles x8) (h10 : Nibbles x10) (h12 : Nibbles x12) (h14 : Nibbles x14) (h16 : Pairs x16) :
    (Vec.map2 (fun a b => Val.mul a b) (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (X86.vpdpbusd (Vector.replicate 16 (some 0#32)) x0 x1) x2 x3) x4 x5) x6 x7) x8 x9) x10 x11) x12 x13) x14 x15) (Vec.map2 (fun a b => Val.ashr a b) (Vec.map2 (fun a b => Val.shl a b) (Vec.join 16 32 2 x16) #v[(some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32)]) #v[(some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32), (some 16#32)])) =
      (X86.pmaddwd 16 (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (Vec.map2 (fun a b => Val.add a b) (X86.pmaddubsw 32 x0 x1) (X86.pmaddubsw 32 x2 x3)) (X86.pmaddubsw 32 x4 x5)) (X86.pmaddubsw 32 x6 x7)) (X86.pmaddubsw 32 x8 x9)) (X86.pmaddubsw 32 x10 x11)) (X86.pmaddubsw 32 x12 x13)) (X86.pmaddubsw 32 x14 x15)) x16) := by
  refine final (k := 8) ?_ (by decide) ?_ ?_
  vnni_inv
  all_goals first | assumption | vnni_facts

end LemmaReuse.Store
