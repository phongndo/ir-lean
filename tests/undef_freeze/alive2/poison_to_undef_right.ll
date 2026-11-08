; correct
define i8 @src() {
  ret i8 poison
}
define i8 @tgt() {
  ret i8 undef
}
