; What tests/superopt.py found for __paritysi2, which tests/llvm/Rewrites.lean proves does the same.
target triple = "x86_64-unknown-linux-gnu"

declare i32 @llvm.ctpop.i32(i32)

define i32 @__paritysi2(i32 noundef %a) {
entry:
  %r0 = call i32 @llvm.ctpop.i32(i32 %a)
  %r1 = and i32 1, %r0
  ret i32 %r1
}
