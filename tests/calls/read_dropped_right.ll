; correct
; An unused call that only reads, will return and can't unwind, dropped. What InstCombine does.
declare i8 @peek(i8) memory(read) willreturn nounwind

define i8 @src(i8 %x) {
  %p = call i8 @peek(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
