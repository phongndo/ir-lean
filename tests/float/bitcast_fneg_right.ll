; correct
; `bitcast (fneg x)` to `xor (bitcast x), sign`: fneg flips the sign bit and keeps every NaN as it was.
define i32 @src(float %x) {
  %a = fneg float %x
  %r = bitcast float %a to i32
  ret i32 %r
}
define i32 @tgt(float %x) {
  %a = bitcast float %x to i32
  %r = xor i32 %a, -2147483648
  ret i32 %r
}
