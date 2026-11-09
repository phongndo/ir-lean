; correct
; `fcmp olt (fabs x), 0.0` to `false`: no magnitude is below zero.
define i1 @src(float %x) {
  %a = call float @llvm.fabs.f32(float %x)
  %r = fcmp olt float %a, 0.0
  ret i1 %r
}
define i1 @tgt(float %x) {
  ret i1 false
}
declare float @llvm.fabs.f32(float)
