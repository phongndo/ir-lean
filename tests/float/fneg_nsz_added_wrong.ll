; incorrect
; `fneg x` to `fneg nsz x`: at 0.0 the target may give 0.0, where the source gives only -0.0.
define float @src(float %x) {
  %r = fneg float %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg nsz float %x
  ret float %r
}
