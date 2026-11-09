; incorrect
; `select c, x, y` to `select nnan c, x, y`: the target is poison where it selects a NaN, and the source isn't.
define float @src(i1 %c, float %x, float %y) {
  %r = select i1 %c, float %x, float %y
  ret float %r
}
define float @tgt(i1 %c, float %x, float %y) {
  %r = select nnan i1 %c, float %x, float %y
  ret float %r
}
