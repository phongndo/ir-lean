; bench/instcombine/stage1.py's CI fixture: InstCombine's rewrites of these, as `ci` checks them against
; expect.json. Each function is one pair.
; RUN: opt < %s -passes=instcombine -S

; Every argument is noundef, so tools/binding.py can bind a certificate for it.
define i8 @add_sub(i8 noundef %x) {
  %a = add i8 %x, 1
  %b = sub i8 %a, 1
  ret i8 %b
}

; From InstCombine's add.ll, with noundef added: two adds and a mask become an or and an add.
define i32 @masked(i32 noundef %x, i32 noundef %y) {
  %a = add i32 %x, 1
  %b = and i32 %y, -2
  %r = add i32 %a, %b
  ret i32 %r
}

; The same, as add.ll has it. An argument can be undef, so this is proved for every value or poison, through
; tools/verify.py, and isn't a certificate.
define i32 @masked_loose(i32 %x, i32 %y) {
  %a = add i32 %x, 1
  %b = and i32 %y, -2
  %r = add i32 %a, %b
  ret i32 %r
}

; Memory, which the model doesn't judge as a refinement.
define i8 @forward(ptr %p, i8 %v) {
  store i8 %v, ptr %p, align 1
  %r = load i8, ptr %p, align 1
  ret i8 %r
}

; A freeze of a noundef argument is the argument, so InstCombine drops it. The source's run makes a choice and
; the target's doesn't, so the claim lifts the target with IRLean.Outcomes.det, as tools/binding_check.lean does.
define i8 @drop_freeze(i8 noundef %x) {
  %f = freeze i8 %x
  %r = add i8 %f, 1
  ret i8 %r
}
