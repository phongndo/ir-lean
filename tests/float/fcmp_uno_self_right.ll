; correct
; `fcmp uno x, x` to `fcmp uno x, 0.0`, as InstCombine canonicalizes: both say whether x is a NaN.
define i1 @src(double %x) {
  %r = fcmp uno double %x, %x
  ret i1 %r
}
define i1 @tgt(double %x) {
  %r = fcmp uno double %x, 0.0
  ret i1 %r
}
