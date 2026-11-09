; incorrect
; `select nnan c, x, NaN` to poison: `nnan` applies to the selected value only, so where c is true it's x.
define float @src(i1 %c, float %x) {
  %r = select nnan i1 %c, float %x, float 0x7FF8000000000000
  ret float %r
}
define float @tgt(i1 %c, float %x) {
  ret float poison
}
