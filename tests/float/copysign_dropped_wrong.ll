; incorrect
; `copysign(x, y)` to `x`: the sign comes from y.
define half @src(half %x, half %y) {
  %r = call half @llvm.copysign.f16(half %x, half %y)
  ret half %r
}
define half @tgt(half %x, half %y) {
  ret half %x
}
declare half @llvm.copysign.f16(half, half)
