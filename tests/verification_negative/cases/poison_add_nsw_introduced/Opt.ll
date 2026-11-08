; Adding nsw to an add that can overflow: wrong. At x = 127, src returns -128 and tgt returns poison.
define i8 @src(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %r = add nsw i8 %x, 1
  ret i8 %r
}
