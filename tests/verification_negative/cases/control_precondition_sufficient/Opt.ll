; (x << 1) >> 1 -> x: right only where x's top bit is clear, that is for x < 128.
define i8 @src(i8 %x) {
  %s = shl i8 %x, 1
  %r = lshr i8 %s, 1
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
