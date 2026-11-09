; tests/binding.py's input: instcombine rewrites `0 - (0 - x)` to `x` around a call outside the module with effects,
; which stays. Both sides make the same call, so they end with the same trace.
declare void @use(i8)

define i8 @f(i8 noundef %x) {
  %n = sub i8 0, %x
  call void @use(i8 %n)
  %r = sub i8 0, %n
  ret i8 %r
}
