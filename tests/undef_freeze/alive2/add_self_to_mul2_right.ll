; correct
define i8 @src(i8 %x) {
  %a = add i8 %x, %x
  ret i8 %a
}
define i8 @tgt(i8 %x) {
  %a = mul i8 %x, 2
  ret i8 %a
}
