; incorrect
; `fmul x, 0.0` to `0.0`: -1.0 times 0.0 is -0.0.
define half @src(half %x) {
  %r = fmul half %x, 0.0
  ret half %r
}
define half @tgt(half %x) {
  ret half 0.0
}
