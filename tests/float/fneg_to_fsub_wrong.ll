; incorrect
; `fneg x` to `fsub -0.0, x`: where x is a NaN, the target may return the preferred NaN, and the source keeps x's
; payload.
define float @src(float %x) {
  %r = fneg float %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fsub float -0.0, %x
  ret float %r
}
