; correct
; A rewrite around a variadic call with effects, which stays: `x + 0` to `x` in its arguments. What InstCombine does.
declare void @log(i32, ...)

define void @src(i8 %x) {
  %y = add i8 %x, 0
  call void (i32, ...) @log(i32 1, i8 %y)
  ret void
}

define void @tgt(i8 %x) {
  call void (i32, ...) @log(i32 1, i8 %x)
  ret void
}
