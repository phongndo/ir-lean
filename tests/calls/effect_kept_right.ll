; correct
; A rewrite around a call with effects, which stays: `0 - (0 - x)` to `x`. What InstCombine does.
declare void @use(i8)

define i8 @src(i8 %x) {
  %n = sub i8 0, %x
  call void @use(i8 %n)
  %r = sub i8 0, %n
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %n = sub i8 0, %x
  call void @use(i8 %n)
  ret i8 %x
}
