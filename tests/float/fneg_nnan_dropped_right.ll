; correct
; `fneg nnan x` to `fneg x`: dropping a flag only takes poison away.
define float @src(float %x) {
  %r = fneg nnan float %x
  ret float %r
}
define float @tgt(float %x) {
  %r = fneg float %x
  ret float %r
}
