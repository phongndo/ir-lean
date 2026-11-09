; correct
; `fmul x, 1.0` to `x`, NaNs and subnormals included.
define double @src(double %x) {
  %r = fmul double %x, 1.0
  ret double %r
}
define double @tgt(double %x) {
  ret double %x
}
