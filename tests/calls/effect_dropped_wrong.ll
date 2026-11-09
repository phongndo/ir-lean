; incorrect
; Dropping a call with effects: the source's trace has a call the target's doesn't.
declare void @use(i8)

define i8 @src(i8 %x) {
  call void @use(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
