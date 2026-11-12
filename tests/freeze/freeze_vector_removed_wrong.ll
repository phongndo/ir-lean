; incorrect
; `freeze %x` of a vector to `%x`: where a lane of `%x` is poison, the source's is a value, and the target's isn't.
define <2 x i8> @src(<2 x i8> %x) {
  %a = freeze <2 x i8> %x
  ret <2 x i8> %a
}
define <2 x i8> @tgt(<2 x i8> %x) {
  ret <2 x i8> %x
}
