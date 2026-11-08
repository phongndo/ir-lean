; tests/binding.py's input for a function ir-lean leaves out: it refuses floating point.
define float @f(float %x) {
  %r = fadd float %x, -0.0
  ret float %r
}
