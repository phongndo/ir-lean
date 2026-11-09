; correct
; Undefined behavior after a call with effects, to poison: where the call comes back, the source is undefined, and
; where it doesn't, both end in it. What InstCombine does.
declare void @use(i8)

define i8 @src(i8 %x) {
  call void @use(i8 %x)
  %r = udiv i8 %x, 0
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  call void @use(i8 %x)
  ret i8 poison
}
