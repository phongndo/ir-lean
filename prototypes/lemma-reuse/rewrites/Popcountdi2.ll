; What tests/superopt.py's search finds for __popcountdi2, with a truncation to the
; result's width. prototypes/lemma-reuse/lemmas.py proves it does what clang left.
target triple = "x86_64-unknown-linux-gnu"

declare i64 @llvm.ctpop.i64(i64)

define i32 @__popcountdi2(i64 noundef %a) {
entry:
  %r0 = call i64 @llvm.ctpop.i64(i64 %a)
  %t = trunc i64 %r0 to i32
  ret i32 %t
}
