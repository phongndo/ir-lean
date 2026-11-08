; incorrect
define i8 @src() {
  %a = freeze i8 undef
  ret i8 %a
}
define i8 @tgt() {
  ret i8 undef
}
