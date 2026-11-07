; What tests/superopt.py found for __popcountsi2, which tests/llvm/Rewrites.lean proves does the same.
target triple = "x86_64-unknown-linux-gnu"

declare i32 @llvm.ctpop.i32(i32)

define i32 @__popcountsi2(i32 noundef %a) {
entry:
  %r0 = call i32 @llvm.ctpop.i32(i32 %a)
  ret i32 %r0
}
