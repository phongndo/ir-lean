; tests/passes_test.py's input for a RUN line with an option a bundle can't represent: the run is unsupported,
; never scored as if the option weren't there.
; RUN: opt < %s -passes=instcombine -instcombine-max-num-phis=1 -S | FileCheck %s
; RUN: not opt < %s -passes=instcombine -S
; RUN: opt < %s -passes='function(instcombine)' -S

define i8 @f(i8 noundef %x) {
  %r = add i8 %x, 0
  ret i8 %r
}
