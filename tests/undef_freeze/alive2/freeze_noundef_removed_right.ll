; correct
define i8 @src(i8 noundef %x) {
  %a = freeze i8 %x
  ret i8 %a
}
define i8 @tgt(i8 noundef %x) {
  ret i8 %x
}
