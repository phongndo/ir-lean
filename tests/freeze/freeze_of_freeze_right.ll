; correct
; `freeze (freeze x)` to `freeze x`: the outer freeze keeps the value the inner one gave.
define i8 @src(i8 %x) {
  %a = freeze i8 %x
  %b = freeze i8 %a
  ret i8 %b
}
define i8 @tgt(i8 %x) {
  %a = freeze i8 %x
  ret i8 %a
}
