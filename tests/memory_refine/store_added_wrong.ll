; incorrect
; Adding a store: the target leaves a value in memory the source left alone.
define i32 @src(ptr %p, i32 %a) {
  ret i32 %a
}

define i32 @tgt(ptr %p, i32 %a) {
  store i32 %a, ptr %p, align 4
  ret i32 %a
}
