; incorrect
; Moving a call that only reads after a call with effects: the call with effects may write what it reads.
declare i8 @peek(i8) memory(read) willreturn nounwind
declare void @use(i8)

define i8 @src(i8 %x) {
  %p = call i8 @peek(i8 %x)
  call void @use(i8 %x)
  ret i8 %p
}

define i8 @tgt(i8 %x) {
  call void @use(i8 %x)
  %p = call i8 @peek(i8 %x)
  ret i8 %p
}
