; incorrect
; Changing the argument of a call with effects: the traces differ in it.
declare void @use(i8)

define void @src(i8 %x) {
  call void @use(i8 %x)
  ret void
}

define void @tgt(i8 %x) {
  %y = add i8 %x, 1
  call void @use(i8 %y)
  ret void
}
