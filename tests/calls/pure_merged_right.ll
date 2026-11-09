; correct
; Two calls with the same argument, merged: the source picks the same answer for both. What early-cse then
; instcombine do.
declare i8 @f(i8) memory(none)

define i8 @src(i8 %x) {
  %a = call i8 @f(i8 %x)
  %b = call i8 @f(i8 %x)
  %c = sub i8 %a, %b
  ret i8 %c
}

define i8 @tgt(i8 %x) {
  %a = call i8 @f(i8 %x)
  ret i8 0
}
