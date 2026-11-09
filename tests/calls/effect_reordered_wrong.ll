; incorrect
; Swapping two calls with effects: the traces differ in order.
declare void @use(i8)

define void @src(i8 %x, i8 %y) {
  call void @use(i8 %x)
  call void @use(i8 %y)
  ret void
}

define void @tgt(i8 %x, i8 %y) {
  call void @use(i8 %y)
  call void @use(i8 %x)
  ret void
}
