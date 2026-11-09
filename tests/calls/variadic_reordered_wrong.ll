; incorrect
; Swapping the arguments after the fixed one of a variadic call with effects: the traces differ in them.
declare void @log(i32, ...)

define void @src(i8 %x, i8 %y) {
  call void (i32, ...) @log(i32 2, i8 %x, i8 %y)
  ret void
}

define void @tgt(i8 %x, i8 %y) {
  call void (i32, ...) @log(i32 2, i8 %y, i8 %x)
  ret void
}
