; tests/binding.py's input for a function ir-lean leaves out: it refuses `reassoc`, whose semantics rewrite
; expressions of several instructions.
define float @f(float %x) {
  %r = fadd reassoc float %x, -0.0
  ret float %r
}
