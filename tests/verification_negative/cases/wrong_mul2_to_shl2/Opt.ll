; InstCombine-style: mul X, 2 -> shl X, 2: wrong, it multiplies by 4.
define i8 @src(i8 %x) {
  %r = mul i8 %x, 2
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %r = shl i8 %x, 2
  ret i8 %r
}
