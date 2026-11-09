; incorrect
; `uitofp x` to `uitofp nneg x`: the target is poison where x's sign bit is set.
define float @src(i32 %x) {
  %r = uitofp i32 %x to float
  ret float %r
}
define float @tgt(i32 %x) {
  %r = uitofp nneg i32 %x to float
  ret float %r
}
