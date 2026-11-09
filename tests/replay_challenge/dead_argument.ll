; tests/replay_challenge.py's input where the pass changes f's signature: deadargelim drops f's unused argument,
; as f is internal and g is its only caller, so no claim can relate f before and after.
define internal i8 @f(i8 noundef %x, i8 noundef %unused) {
  %r = add i8 %x, 1
  ret i8 %r
}

define i8 @g(i8 noundef %a) {
  %r = call i8 @f(i8 %a, i8 7)
  ret i8 %r
}
