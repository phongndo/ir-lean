; incorrect
define i8 @src(i8 %x) {
  %a = freeze i8 %x
  %r = sub i8 %a, %a
  ret i8 %r
}
define i8 @tgt(i8 %x) {
  %a = freeze i8 %x
  %b = freeze i8 %x
  %r = sub i8 %a, %b
  ret i8 %r
}
