; incorrect
; Removing a store that a load reads: the load gives what was there before.
define i32 @src(ptr %p, i32 %a) {
  store i32 %a, ptr %p, align 4
  %r = load i32, ptr %p, align 4
  ret i32 %r
}

define i32 @tgt(ptr %p, i32 %a) {
  %r = load i32, ptr %p, align 4
  ret i32 %r
}
