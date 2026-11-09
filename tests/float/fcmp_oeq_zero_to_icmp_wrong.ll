; incorrect
; `fcmp oeq x, 0.0` to `icmp eq (bitcast x), 0`: -0.0 equals 0.0, but its bits are not zero.
define i1 @src(float %x) {
  %r = fcmp oeq float %x, 0.0
  ret i1 %r
}
define i1 @tgt(float %x) {
  %a = bitcast float %x to i32
  %r = icmp eq i32 %a, 0
  ret i1 %r
}
