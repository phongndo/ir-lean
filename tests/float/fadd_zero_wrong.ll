; incorrect
; `fadd x, 0.0` to `x`: -0.0 + 0.0 is 0.0, not -0.0.
define float @src(float %x) {
  %r = fadd float %x, 0.0
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
