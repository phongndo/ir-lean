; tests/store_test.py's reuse example: a shift left with nuw and back by the same amount, which InstSimplify folds
; to %x (llvm/lib/Analysis/InstructionSimplify.cpp, line 1448, at llvmorg-23.1.3).
define i256 @f(i256 %x, i256 %s) {
  %a = shl nuw i256 %x, %s
  %r = lshr i256 %a, %s
  ret i256 %r
}
