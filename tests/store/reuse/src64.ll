; tests/store_test.py's reuse example: a shift left with nuw and back by the same amount, which InstSimplify folds
; to %x (llvm/lib/Analysis/InstructionSimplify.cpp, line 1448, at llvmorg-23.1.3).
define i64 @f(i64 %x, i64 %s) {
  %a = shl nuw i64 %x, %s
  %r = lshr i64 %a, %s
  ret i64 %r
}
