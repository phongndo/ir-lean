; correct
; `fcmp olt 1.0, x` to `fcmp ogt x, 1.0`, the constant moved right, as InstCombine canonicalizes.
define i1 @src(float %x) {
  %r = fcmp olt float 1.0, %x
  ret i1 %r
}
define i1 @tgt(float %x) {
  %r = fcmp ogt float %x, 1.0
  ret i1 %r
}
