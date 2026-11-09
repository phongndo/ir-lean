; correct
define i8 @src(i8 %y) {
  %a = select i1 undef, i8 42, i8 %y
  ret i8 %a
}
define i8 @tgt(i8 %y) {
  ret i8 42
}
