; incorrect
; Changing an argument: the callee may answer the two differently.
declare i8 @f(i8) memory(none) willreturn nounwind

define i8 @src(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %y = add i8 %x, 1
  %r = call i8 @f(i8 %y)
  ret i8 %r
}
