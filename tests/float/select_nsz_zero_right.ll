; correct
; `select nsz (fcmp oeq x, 0.0), 0.0, x` to `x`: at -0.0 the source may give -0.0, since `nsz` applies to the result.
define float @src(float %x) {
  %c = fcmp oeq float %x, 0.0
  %r = select nsz i1 %c, float 0.0, float %x
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
