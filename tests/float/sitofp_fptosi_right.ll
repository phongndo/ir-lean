; correct
; `fptosi (sitofp x)` to `x` for an i16, which a float holds exactly, as InstCombine folds it.
define i16 @src(i16 %x) {
  %a = sitofp i16 %x to float
  %r = fptosi float %a to i16
  ret i16 %r
}
define i16 @tgt(i16 %x) {
  ret i16 %x
}
