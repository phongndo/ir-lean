; incorrect
; Dropping a call that may never come back: where it doesn't, the source never finishes, and the target returns.
declare i8 @f(i8) memory(none) nounwind

define i8 @src(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
