; correct
; A call that accesses no memory, will return and can't unwind, with its result unused, dropped. What InstCombine does.
declare i8 @f(i8) memory(none) willreturn nounwind

define i8 @src(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
