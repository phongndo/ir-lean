; correct
; `fcmp uno x, 0.0` to `is.fpclass(x, nan)`, where 3 names both kinds of NaN.
define i1 @src(bfloat %x) {
  %r = fcmp uno bfloat %x, 0.0
  ret i1 %r
}
define i1 @tgt(bfloat %x) {
  %r = call i1 @llvm.is.fpclass.bf16(bfloat %x, i32 3)
  ret i1 %r
}
declare i1 @llvm.is.fpclass.bf16(bfloat, i32)
