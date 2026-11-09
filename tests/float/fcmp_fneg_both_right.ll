; correct
; `fcmp olt (fneg x), (fneg y)` to `fcmp ogt x, y`, as fcmp.ll folds it, NaNs and zeros included.
define i1 @src(float %x, float %y) {
  %a = fneg float %x
  %b = fneg float %y
  %r = fcmp olt float %a, %b
  ret i1 %r
}
define i1 @tgt(float %x, float %y) {
  %r = fcmp ogt float %x, %y
  ret i1 %r
}
