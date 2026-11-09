; incorrect
; Adding a call that isn't `speculatable`: where it's undefined, the target is and the source isn't.
declare i8 @f(i8) memory(none) willreturn nounwind

define i8 @src(i8 %x) {
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %x
}
