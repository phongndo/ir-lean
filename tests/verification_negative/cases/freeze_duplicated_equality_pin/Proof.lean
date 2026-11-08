import Opt
open IRLean

/-- Equal on every input. Both stop at a frozen poison, so equality holds there too, though LLVM's tgt can
return anything where src returns 0. -/
theorem tgt_refines_src (x : Val 8) : Opt.tgt x = Opt.src x := by
  cases x <;> simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
