; tests/binding.py's input for a function that reads memory, where the model has more undefined behavior than LLVM.
define i8 @f(ptr %p) {
  %v = load i8, ptr %p
  %r = add i8 %v, 0
  ret i8 %r
}
