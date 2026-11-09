; incorrect
; `fcmp olt x, y` to `fcmp ult x, y`: at a NaN the source is false and the target true.
define i1 @src(float %x, float %y) {
  %r = fcmp olt float %x, %y
  ret i1 %r
}
define i1 @tgt(float %x, float %y) {
  %r = fcmp ult float %x, %y
  ret i1 %r
}
