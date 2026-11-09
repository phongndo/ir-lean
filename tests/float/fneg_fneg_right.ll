; correct
; `fneg (fneg x)` to `x`, as InstCombine's fneg.ll folds it: both flip the sign bit and nothing else.
define float @src(float %x) {
  %a = fneg float %x
  %b = fneg float %a
  ret float %b
}
define float @tgt(float %x) {
  ret float %x
}
