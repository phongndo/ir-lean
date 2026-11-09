; Two candidate outputs for the same src. The proof is about tgt_good, and the claim is about tgt_bad.
define i8 @src(i8 %x) {
  %r = mul i8 %x, 2
  ret i8 %r
}

define i8 @tgt_good(i8 %x) {
  %r = shl i8 %x, 1
  ret i8 %r
}

define i8 @tgt_bad(i8 %x) {
  %r = shl i8 %x, 2
  ret i8 %r
}
