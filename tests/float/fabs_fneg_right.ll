; correct
; `fabs (fneg x)` to `fabs x`, as fabs.ll folds it.
define double @src(double %x) {
  %a = fneg double %x
  %b = call double @llvm.fabs.f64(double %a)
  ret double %b
}
define double @tgt(double %x) {
  %b = call double @llvm.fabs.f64(double %x)
  ret double %b
}
declare double @llvm.fabs.f64(double)
