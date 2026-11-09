; Adding a freeze: right in LLVM, since a frozen poison is one of the values poison allows. Until F3 the model
; stopped at freeze of poison instead of choosing, so this couldn't be certified. Now it can.
define i8 @src(i8 %x) {
  ret i8 %x
}

define i8 @tgt(i8 %x) {
  %r = freeze i8 %x
  ret i8 %r
}
