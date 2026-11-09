import Opt
open IRLean

/-- Equal on every input, for one way of choosing. Until F3 both stopped at a frozen poison, so this held there too,
though LLVM's tgt can return anything where src returns 0. Now it's false: where tgt's two `freeze`s choose 0 and 1,
it returns 255. -/
theorem tgt_refines_src (x : Val 8) :
    Opt.tgt x (fun p => if p = [2] then 1 else 0) = Opt.src x (fun p => if p = [2] then 1 else 0) := by
  cases x <;> simp [Opt.src, Opt.tgt, Opt.src.step, Opt.tgt.step, run, llvm]
