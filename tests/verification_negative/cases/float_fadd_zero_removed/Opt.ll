; fadd x, 0.0 -> x: wrong, since -0.0 + 0.0 is +0.0. The model has no floating point, and the emitter
; refuses it.
define float @src(float %x) {
  %r = fadd float %x, 0.0
  ret float %r
}

define float @tgt(float %x) {
  ret float %x
}
