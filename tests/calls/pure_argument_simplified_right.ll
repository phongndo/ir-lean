; correct
; Rewrites around a call: its argument simplified to the same value, and an `add` of 0 to its result removed. What
; InstCombine does.
declare i8 @f(i8) memory(none)

define i8 @src(i8 %x) {
  %y = xor i8 %x, -1
  %z = xor i8 %y, -1
  %r = call i8 @f(i8 %z)
  %s = add i8 %r, 0
  ret i8 %s
}

define i8 @tgt(i8 %x) {
  %r = call i8 @f(i8 %x)
  ret i8 %r
}
