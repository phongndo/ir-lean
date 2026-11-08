; correct
define i8 @src() {
  %a = xor i8 undef, undef
  ret i8 %a
}
define i8 @tgt() {
  ret i8 undef
}
