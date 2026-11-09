; correct
; Duplicating a `freeze` of something that can't be poison changes nothing.
define i8 @src(i8 %x) {
  %f = freeze i8 %x
  %y = add i8 %f, 1
  %a = freeze i8 %y
  %r = sub i8 %a, %a
  ret i8 %r
}
define i8 @tgt(i8 %x) {
  %f = freeze i8 %x
  %y = add i8 %f, 1
  %a = freeze i8 %y
  %b = freeze i8 %y
  %r = sub i8 %a, %b
  ret i8 %r
}
