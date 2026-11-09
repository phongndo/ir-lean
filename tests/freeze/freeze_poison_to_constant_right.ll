; correct
; `freeze poison` to a constant: the source can choose it.
define i8 @src(i8 %x) {
  %a = freeze i8 poison
  ret i8 %a
}
define i8 @tgt(i8 %x) {
  ret i8 42
}
