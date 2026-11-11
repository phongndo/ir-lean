; incorrect
; alive2: correct: the target allocates nothing, and the relation asks both memories for the same next allocation
; Removing an `alloca` that nothing reads, with the store to it. It's right in LLVM. The model has no claim for it yet:
; the source's memory has numbered one more allocation than the target's, and `Mem.le` compares that number, so the
; theorem says the relation doesn't hold, which is about the relation and not the rewrite. docs/refinement.md.
define i32 @src(i32 %a) {
  %s = alloca i32, align 4
  store i32 %a, ptr %s, align 4
  ret i32 %a
}

define i32 @tgt(i32 %a) {
  ret i32 %a
}
