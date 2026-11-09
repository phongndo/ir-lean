; incorrect
; `fdiv x, x` to `1.0`: 0.0 / 0.0 is a NaN.
define double @src(double %x) {
  %r = fdiv double %x, %x
  ret double %r
}
define double @tgt(double %x) {
  ret double 1.0
}
