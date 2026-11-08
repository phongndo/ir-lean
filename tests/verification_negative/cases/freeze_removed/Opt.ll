; Removing a freeze of a value that can be poison: wrong. LLVM's src returns some fixed value for a poison
; x, and tgt returns poison.
define i8 @src(i8 %x) {
  %r = freeze i8 %x
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  ret i8 %x
}
