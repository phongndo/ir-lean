; correct
; Two loads of the same bytes with nothing between them, to one.
define i32 @src(ptr %p) {
  %x = load i32, ptr %p, align 4
  %y = load i32, ptr %p, align 4
  %r = sub i32 %x, %y
  ret i32 %r
}

define i32 @tgt(ptr %p) {
  %x = load i32, ptr %p, align 4
  %r = sub i32 %x, %x
  ret i32 %r
}
