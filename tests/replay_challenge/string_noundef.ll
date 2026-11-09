; tests/replay_challenge.py's input with a string attribute spelled like noundef. It isn't the attribute, so a
; caller can pass undef, which IRLean doesn't model.
define i8 @f(i8 "noundef" %x) {
  %r = add i8 %x, 0
  ret i8 %r
}
