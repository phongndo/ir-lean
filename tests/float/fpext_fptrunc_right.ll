; correct
; `fptrunc (fpext x)` to `x`: widening is exact, and a NaN payload comes back as it went.
define float @src(float %x) {
  %a = fpext float %x to double
  %r = fptrunc double %a to float
  ret float %r
}
define float @tgt(float %x) {
  ret float %x
}
