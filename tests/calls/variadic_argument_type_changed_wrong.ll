; incorrect
; Passing a variadic callee `(i128 1, i64 2)` where the source passes `(i64 1, i64 2)`: the same lanes, read by the
; callee as other types.
declare void @v(...)

define void @src() {
  call void (...) @v(i64 1, i64 2)
  ret void
}

define void @tgt() {
  call void (...) @v(i128 1, i64 2)
  ret void
}
