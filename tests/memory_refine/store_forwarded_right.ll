; correct
; Forwarding a store to the load after it: the load gives what was stored.
define i32 @src(ptr %p, i32 %a) {
  store i32 %a, ptr %p, align 4
  %r = load i32, ptr %p, align 4
  ret i32 %r
}

define i32 @tgt(ptr %p, i32 %a) {
  store i32 %a, ptr %p, align 4
  ret i32 %a
}
