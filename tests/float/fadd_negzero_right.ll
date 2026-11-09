; correct
; `fadd x, -0.0` to `x`, as InstSimplify folds it: where x is a NaN, the source may return it unchanged.
define float @src(float %x) {
  %r = fadd float %x, -0.0
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
