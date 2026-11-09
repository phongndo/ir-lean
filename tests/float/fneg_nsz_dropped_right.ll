; correct
; `fneg nsz x` to `fneg x`: dropping `nsz` only takes a zero's other sign away.
define float @src(float %x) {
  %r = fneg nsz float %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg float %x
  ret float %r
}
