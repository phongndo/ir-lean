; incorrect
define i8 @src(i8 noundef %x) {
  ret i8 0
}
define i8 @tgt(i8 noundef %x) {
  %a = add i8 %x, undef
  %r = sub i8 %a, %a
  ret i8 %r
}
