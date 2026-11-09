; correct
; `fsub nsz 0.0, x` to `fneg x`, as InstCombine folds it: `nsz` may flip the 0.0 to -0.0, and -0.0 - x is fneg x.
define float @src(float %x) {
  %r = fsub nsz float 0.0, %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg float %x
  ret float %r
}
