; incorrect
; alive2: correct: Alive2 has no unwinding, so its calls can't unwind
; Swapping two calls that may unwind: where both do, the source unwinds from @f and the target from @g.
declare i8 @f(i8) memory(none) willreturn
declare i8 @g(i8) memory(none) willreturn

define i8 @src(i8 %x) {
  %a = call i8 @f(i8 %x)
  %b = call i8 @g(i8 %x)
  %c = sub i8 %a, %b
  ret i8 %c
}

define i8 @tgt(i8 %x) {
  %b = call i8 @g(i8 %x)
  %a = call i8 @f(i8 %x)
  %c = sub i8 %a, %b
  ret i8 %c
}
