; correct
define i8 @src(i8 %x) {
  ret i8 %x
}
define i8 @tgt(i8 %x) {
  %a = freeze i8 %x
  ret i8 %a
}
