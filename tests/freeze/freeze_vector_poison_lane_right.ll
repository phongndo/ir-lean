; correct
; A vector's poison lane, frozen, to a constant: that lane can choose it, and the other keeps its value.
define <2 x i8> @src(<2 x i8> %x) {
  %a = freeze <2 x i8> <i8 poison, i8 1>
  ret <2 x i8> %a
}
define <2 x i8> @tgt(<2 x i8> %x) {
  ret <2 x i8> <i8 42, i8 1>
}
