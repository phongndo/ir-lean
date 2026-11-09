; correct
; `fadd nsz x, 0.0` to `x`, as InstSimplify folds it: `nsz` may flip the 0.0 to -0.0, and x + -0.0 is x.
define float @src(float %x) {
  %r = fadd nsz float %x, 0.0
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
