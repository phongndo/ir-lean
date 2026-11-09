; incorrect
; Calling a function with effects twice where the source calls it once: the target's trace has one more call.
declare void @use(i8)

define void @src(i8 %x) {
  call void @use(i8 %x)
  ret void
}

define void @tgt(i8 %x) {
  call void @use(i8 %x)
  call void @use(i8 %x)
  ret void
}
