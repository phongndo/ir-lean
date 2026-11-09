; incorrect
; `fdiv x, x` to `1.0`: 0.0 / 0.0 is a NaN.
define float @src(float %x) {
  %r = fdiv float %x, %x
  ret float %r
}
define float @tgt(float %x) {
  ret float 1.0
}
