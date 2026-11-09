; incorrect
; `fabs nsz -0.0` to `-0.0`, as InstSimplify folds it for fp128: `nsz` may flip the operand's sign, and either way
; fabs gives 0.0.
define fp128 @src() {
  %r = call nsz fp128 @llvm.fabs.f128(fp128 0xL00000000000000008000000000000000)
  ret fp128 %r
}
define fp128 @tgt() {
  ret fp128 0xL00000000000000008000000000000000
}
declare fp128 @llvm.fabs.f128(fp128)
