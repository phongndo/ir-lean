; incorrect
; `fcmp oeq x, x` to `true`: a NaN isn't equal to itself.
define i1 @src(double %x) {
  %r = fcmp oeq double %x, %x
  ret i1 %r
}
define i1 @tgt(double %x) {
  ret i1 true
}
