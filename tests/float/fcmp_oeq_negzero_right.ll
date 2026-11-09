; correct
; `fcmp oeq x, -0.0` to `fcmp oeq x, 0.0`: zeros of either sign are equal.
define i1 @src(float %x) {
  %r = fcmp oeq float %x, -0.0
  ret i1 %r
}
define i1 @tgt(float %x) {
  %r = fcmp oeq float %x, 0.0
  ret i1 %r
}
