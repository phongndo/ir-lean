; incorrect
; Swapping two stores through pointers that may be the same: where they are, the other value is left.
define void @src(ptr %p, ptr %q, i32 %a, i32 %b) {
  store i32 %a, ptr %p, align 4
  store i32 %b, ptr %q, align 4
  ret void
}

define void @tgt(ptr %p, ptr %q, i32 %a, i32 %b) {
  store i32 %b, ptr %q, align 4
  store i32 %a, ptr %p, align 4
  ret void
}
