; correct
define i8 @src(i1 %x, i8 noundef %y) {
  %a = select i1 %x, i8 %y, i8 undef
  ret i8 %a
}
define i8 @tgt(i1 %x, i8 noundef %y) {
  ret i8 %y
}
