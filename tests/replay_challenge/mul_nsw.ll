; tests/replay_challenge.py's input with a flag: instcombine turns the nsw multiply by 2 into an nsw shift by 1,
; which is poison on exactly the same inputs, so the two are equal in IRLean's semantics.
define i8 @f(i8 noundef %x) {
  %r = mul nsw i8 %x, 2
  ret i8 %r
}
