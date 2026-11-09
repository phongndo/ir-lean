; correct
; `fadd x, y` to `fadd y, x`: where the source takes a NaN from one operand, the target takes it from the other.
define float @src(float %x, float %y) {
  %r = fadd float %x, %y
  ret float %r
}
define float @tgt(float %x, float %y) {
  %r = fadd float %y, %x
  ret float %r
}
