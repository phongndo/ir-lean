; Folding x - x to undef instead of 0: wrong, since undef can be any value and src is always 0. The model
; has no undef, and the emitter refuses it.
define i8 @src(i8 %x) {
  %r = sub i8 %x, %x
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  ret i8 undef
}
