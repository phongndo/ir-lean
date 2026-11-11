; incorrect
; Adding a load from memory the source never touched: where the pointer can't be read, the target is undefined.
define i32 @src(ptr %p, i32 %a) {
  ret i32 %a
}

define i32 @tgt(ptr %p, i32 %a) {
  %x = load i32, ptr %p, align 4
  ret i32 %a
}
