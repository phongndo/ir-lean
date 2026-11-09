; incorrect
; Adding a call with effects: the target's trace has a call the source's doesn't.
declare void @use(i8)

define i8 @src(i8 %x) {
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  call void @use(i8 %x)
  ret i8 %x
}
