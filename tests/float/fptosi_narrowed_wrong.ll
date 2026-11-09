; incorrect
; `trunc (fptosi x to i32) to i8` to `fptosi x to i8`: 200.0 doesn't fit in an i8, so the target is poison.
define i8 @src(float %x) {
  %a = fptosi float %x to i32
  %r = trunc i32 %a to i8
  ret i8 %r
}
define i8 @tgt(float %x) {
  %r = fptosi float %x to i8
  ret i8 %r
}
