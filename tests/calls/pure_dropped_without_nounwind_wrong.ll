; incorrect
; alive2: correct: Alive2 has no unwinding, so its calls can't unwind
; Dropping a call that may unwind: where it does, the source unwinds, and the target returns.
declare i8 @f(i8) memory(none) willreturn

define i8 @src(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
