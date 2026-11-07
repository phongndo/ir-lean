; What tests/superopt.py found for __clzsi2, which tests/llvm/Rewrites.lean proves does the same.
target triple = "x86_64-unknown-linux-gnu"

declare i32 @llvm.ctlz.i32(i32, i1)

define i32 @__clzsi2(i32 noundef %a) {
entry:
  %r0 = call i32 @llvm.ctlz.i32(i32 %a, i1 false)
  ret i32 %r0
}
