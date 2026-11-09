; correct
; `fdiv x, 2.0` to `fmul x, 0.5`, as InstCombine folds a division by a power of two: one rounding of the same value.
define float @src(float %x) {
  %r = fdiv float %x, 2.0
  ret float %r
}
define float @tgt(float %x) {
  %r = fmul float %x, 0.5
  ret float %r
}
