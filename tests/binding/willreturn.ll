; tests/binding.py's input for a target with a promise IRLean trusts instead of checking.
define i8 @f(i8 %x) willreturn {
  %r = add i8 %x, 0
  ret i8 %r
}
