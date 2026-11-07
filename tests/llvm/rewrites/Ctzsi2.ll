; What tests/superopt.py found for __ctzsi2, which tests/llvm/Rewrites.lean proves does the same.
target triple = "x86_64-unknown-linux-gnu"

declare i32 @llvm.cttz.i32(i32, i1)

define i32 @__ctzsi2(i32 noundef %a) {
entry:
  %r0 = call i32 @llvm.cttz.i32(i32 %a, i1 false)
  ret i32 %r0
}
