; incorrect
; `select (fcmp oeq x, 0.0), 0.0, x` to `x`: at -0.0 the source gives 0.0 and the target -0.0.
define float @src(float %x) {
  %c = fcmp oeq float %x, 0.0
  %r = select i1 %c, float 0.0, float %x
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
