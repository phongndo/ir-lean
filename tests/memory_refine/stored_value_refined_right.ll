; correct
; Storing a value where the source stored poison: `add nuw` to `add`, and the memories differ in the bytes written.
define void @src(ptr %p, i32 %a) {
  %s = add nuw i32 %a, 1
  store i32 %s, ptr %p, align 4
  ret void
}

define void @tgt(ptr %p, i32 %a) {
  %s = add i32 %a, 1
  store i32 %s, ptr %p, align 4
  ret void
}
