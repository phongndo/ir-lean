; incorrect
; alive2: correct: Alive2 gives two calls to a function that accesses no memory, with the same arguments, the same answer
; One call used twice, to two calls: LangRef's `memory(none)` doesn't promise the same answer, so the target can give
; 255 where the source gives 0.
declare i8 @f(i8) memory(none) willreturn nounwind

define i8 @src(i8 %x) {
  %a = call i8 @f(i8 %x)
  %c = sub i8 %a, %a
  ret i8 %c
}

define i8 @tgt(i8 %x) {
  %a = call i8 @f(i8 %x)
  %b = call i8 @f(i8 %x)
  %c = sub i8 %a, %b
  ret i8 %c
}
