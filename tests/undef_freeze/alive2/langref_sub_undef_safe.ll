; correct
define i8 @src(i8 %x) {
  %a = sub i8 %x, undef
  ret i8 %a
}
define i8 @tgt(i8 %x) {
  ret i8 undef
}
