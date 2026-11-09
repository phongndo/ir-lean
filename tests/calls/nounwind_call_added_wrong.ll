; incorrect
; alive2: correct: Alive2 has no unwinding, so its calls can't unwind
; Marking a call to a function that calls outside the module `nounwind`: where the call outside unwinds, the source
; unwinds and the target is undefined.
declare i8 @f(i8) memory(none) willreturn

define internal i8 @g(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %r
}

define i8 @src(i8 %x) {
  %r = call i8 @g(i8 %x)
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %r = call i8 @g(i8 %x) nounwind
  ret i8 %r
}
