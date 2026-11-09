; incorrect
; Dropping a call with effects before undefined behavior: where the call never comes back, the source is defined, and
; ends in it.
declare void @use(i8)

define i8 @src(i8 %x) {
  call void @use(i8 %x)
  %r = udiv i8 %x, 0
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  ret i8 poison
}
