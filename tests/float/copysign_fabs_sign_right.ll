; correct
; `copysign(x, fabs y)` to `fabs x`: the sign it copies is clear.
define half @src(half %x, half %y) {
  %a = call half @llvm.fabs.f16(half %y)
  %b = call half @llvm.copysign.f16(half %x, half %a)
  ret half %b
}
define half @tgt(half %x, half %y) {
  %b = call half @llvm.fabs.f16(half %x)
  ret half %b
}
declare half @llvm.fabs.f16(half)
declare half @llvm.copysign.f16(half, half)
