; tests/passes_test.py's input for a proof that can't finish in time: instcombine factors x*y + x*z into
; x*(y+z), and the scorer's automation leaves bv_decide 64-bit multiplication on both sides, which SAT takes far
; longer than a few seconds on. Under a wall clock that short, the instance has to be unknown, never failed,
; refused or bound.
; RUN: opt < %s -passes=instcombine -S | FileCheck %s

define i64 @distributes(i64 noundef %x, i64 noundef %y, i64 noundef %z) {
  %a = mul i64 %x, %y
  %b = mul i64 %x, %z
  %r = add i64 %a, %b
  ret i64 %r
}
