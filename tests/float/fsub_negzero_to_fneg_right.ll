; correct
; `fsub -0.0, x` to `fneg x`, as InstCombine folds it: where x is a NaN, the source may return it unchanged with
; its sign flipped.
define float @src(float %x) {
  %r = fsub float -0.0, %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg float %x
  ret float %r
}
