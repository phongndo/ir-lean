; tests/passes_test.py's input, a regression test the way LLVM writes them: instcombine changes three functions
; here. @guarded gets `nuw` under its branch's guard and @round_trip folds to its argument, which the scorer's
; automation proves equal; @loads reads memory, and @maybe_undef can take undef, which the model can't judge.
; RUN: opt < %s -passes=instcombine -S | FileCheck %s

define i8 @guarded(i8 noundef %x, i8 noundef %y) {
entry:
  %c = icmp ult i8 %x, %y
  br i1 %c, label %a, label %b
a:
  %s = sub i8 %y, %x
  %t = add i8 %s, 0
  ret i8 %t
b:
  ret i8 0
}

define i8 @round_trip(i8 noundef %x) {
  %a = add i8 %x, 1
  %b = sub i8 %a, 1
  ret i8 %b
}

define i8 @loads(ptr noundef %p) {
  %v = load i8, ptr %p
  %r = add i8 %v, 0
  ret i8 %r
}

define i8 @maybe_undef(i8 %x) {
  %r = add i8 %x, 0
  ret i8 %r
}

define i8 @unchanged(i8 noundef %x) {
  ret i8 %x
}
