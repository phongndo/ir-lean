; What tests/superopt.py's search finds for __popcountti2, with a truncation to the
; result's width. prototypes/lemma-reuse/lemmas.py proves it does what clang left.
target triple = "x86_64-unknown-linux-gnu"

declare i128 @llvm.ctpop.i128(i128)

define i32 @__popcountti2(i128 noundef %a) {
entry:
  %r0 = call i128 @llvm.ctpop.i128(i128 %a)
  %t = trunc i128 %r0 to i32
  ret i32 %t
}
