; tests/binding.py's input for an argument a caller can pass as undef, which IRLean doesn't model.
define i8 @f(i8 %x) {
  %r = add i8 %x, 0
  ret i8 %r
}
