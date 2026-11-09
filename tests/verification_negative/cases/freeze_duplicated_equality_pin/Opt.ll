; Duplicating a freeze: wrong. src freezes x once, so a - a is 0. tgt freezes it twice, and for a poison x
; the two can differ, so tgt can return anything. In the model each freeze reads its own place in the run's
; choice, so they can differ there too.
define i8 @src(i8 %x) {
  %a = freeze i8 %x
  %r = sub i8 %a, %a
  ret i8 %r
}

define i8 @tgt(i8 %x) {
  %a = freeze i8 %x
  %b = freeze i8 %x
  %r = sub i8 %a, %b
  ret i8 %r
}
