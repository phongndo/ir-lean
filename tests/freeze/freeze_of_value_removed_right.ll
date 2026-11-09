; correct
; `freeze y` to `y` where `y` can't be poison: it's computed without flags from a frozen value.
define i8 @src(i8 %x) {
  %f = freeze i8 %x
  %y = add i8 %f, 1
  %z = freeze i8 %y
  ret i8 %z
}
define i8 @tgt(i8 %x) {
  %f = freeze i8 %x
  %y = add i8 %f, 1
  ret i8 %y
}
