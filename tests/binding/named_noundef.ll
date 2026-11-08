; tests/binding.py's input for an argument named like the attribute, without it: a caller can pass undef.
define i8 @f(i8 %noundef) {
  %r = add i8 %noundef, 0
  ret i8 %r
}
