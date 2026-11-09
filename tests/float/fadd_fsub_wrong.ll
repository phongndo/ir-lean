; incorrect
; `fsub (fadd x, y), y` to `x`: 1.0 + 2^24 rounds to 2^24 in a float, and taking 2^24 away leaves 0.0.
define float @src(float %x, float %y) {
  %a = fadd float %x, %y
  %r = fsub float %a, %y
  ret float %r
}
define float @tgt(float %x, float %y) {
  ret float %x
}
