; incorrect
define i8 @src(i8 %x) {
  ret i8 0
}
define i8 @tgt(i8 %x) {
  %a = sub i8 %x, %x
  ret i8 %a
}
