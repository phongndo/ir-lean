; incorrect
; Dropping a call with effects that will return and can't unwind: it still writes what the caller's caller can see, so
; the traces differ.
declare void @use(i8) willreturn nounwind

define i8 @src(i8 %x) {
  call void @use(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
