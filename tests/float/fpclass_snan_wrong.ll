; incorrect
; `is.fpclass(x, snan)` to `fcmp uno x, 0.0`: a quiet NaN is unordered but not signaling.
define i1 @src(float %x) {
  %r = call i1 @llvm.is.fpclass.f32(float %x, i32 1)
  ret i1 %r
}
define i1 @tgt(float %x) {
  %r = fcmp uno float %x, 0.0
  ret i1 %r
}
declare i1 @llvm.is.fpclass.f32(float, i32)
