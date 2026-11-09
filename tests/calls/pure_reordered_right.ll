; correct
; Two calls that will return and can't unwind, swapped: the source picks each the answer the target got.
declare i8 @f(i8) memory(none) willreturn nounwind
declare i8 @g(i8) memory(none) willreturn nounwind

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
