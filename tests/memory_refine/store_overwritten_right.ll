; correct
; Removing a store that's overwritten before anything reads it.
define void @src(ptr %p, i32 %a, i32 %b) {
  store i32 %a, ptr %p, align 4
  store i32 %b, ptr %p, align 4
  ret void
}

define void @tgt(ptr %p, i32 %a, i32 %b) {
  store i32 %b, ptr %p, align 4
  ret void
}
