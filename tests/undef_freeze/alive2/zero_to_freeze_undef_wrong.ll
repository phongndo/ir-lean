; incorrect
define i8 @src() {
  ret i8 0
}
define i8 @tgt() {
  %a = freeze i8 undef
  ret i8 %a
}
