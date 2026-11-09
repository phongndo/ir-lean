import IRLean.LLVMHeap

/-! Prints the layout and the opcodes `IRLean.LLVMHeap` uses, as `-D` flags for `layout_probe.cpp`, so the probe
checks the numbers the proofs use. -/

open IRLean.LLVMHeap in
#eval IO.println <| " ".intercalate <|
  (Layout.all.map fun (k, v) => s!"-DLAYOUT_{k}={v}") ++ (BinOp.all.map fun (k, op) => s!"-DOPCODE_{k}={op.opcode}")
