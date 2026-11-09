; incorrect
; `fneg x` to `fneg nnan x`: the target is poison at a NaN, where the source has a value.
define float @src(float %x) {
  %r = fneg float %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg nnan float %x
  ret float %r
}
