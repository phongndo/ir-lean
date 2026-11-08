; Dropping nsw: right. Where src overflows it returns poison, which allows any value.
define i8 @src(i8 %x) {
  %r = add nsw i8 %x, 1
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}
