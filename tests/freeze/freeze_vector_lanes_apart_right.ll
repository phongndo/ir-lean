; correct
; One `freeze` of a vector of poison, two lanes apart: each lane chooses on its own, so lane 0 less lane 1 can be
; anything, 255 among it.
define i8 @src(i8 %x) {
  %a = freeze <2 x i8> poison
  %l0 = extractelement <2 x i8> %a, i64 0
  %l1 = extractelement <2 x i8> %a, i64 1
  %d = sub i8 %l0, %l1
  ret i8 %d
}
define i8 @tgt(i8 %x) {
  ret i8 255
}
