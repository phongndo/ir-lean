; tests/replay_challenge.py's poison and flag pairs: each is a rewrite from ID_src to ID_tgt, right or wrong in
; LLVM. pairs.json says which, and on which inputs, as worked out by hand from LangRef. Alive2 and IRLean are then
; each asked, and have to agree with it. No argument is noundef, so a poison argument counts too. Nothing loops, so
; every input finishes.

; Both are poison exactly when x * 2 overflows as a signed number: right.
define i8 @mul_nsw_shl_nsw_src(i8 %x) {
  %r = mul nsw i8 %x, 2
  ret i8 %r
}

define i8 @mul_nsw_shl_nsw_tgt(i8 %x) {
  %r = shl nsw i8 %x, 1
  ret i8 %r
}

; For x in -64..-1, x * 2 doesn't overflow as a signed number, and shifting out x's set top bit is poison under
; nuw: wrong at 192..255.
define i8 @mul_nsw_shl_nuw_src(i8 %x) {
  %r = mul nsw i8 %x, 2
  ret i8 %r
}

define i8 @mul_nsw_shl_nuw_tgt(i8 %x) {
  %r = shl nuw i8 %x, 1
  ret i8 %r
}

; Dropping a flag only removes poison: right.
define i8 @add_drop_nuw_src(i8 %x) {
  %r = add nuw i8 %x, 1
  ret i8 %r
}

define i8 @add_drop_nuw_tgt(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}

; Adding nuw makes 255 + 1 poison, where the source wraps to 0: wrong at 255.
define i8 @add_add_nuw_src(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}

define i8 @add_add_nuw_tgt(i8 %x) {
  %r = add nuw i8 %x, 1
  ret i8 %r
}

; or disjoint is poison where x is odd, and is x + 1 elsewhere: right.
define i8 @or_disjoint_add_src(i8 %x) {
  %r = or disjoint i8 %x, 1
  ret i8 %r
}

define i8 @or_disjoint_add_tgt(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}

; The other way, an odd x makes the target poison where the source has a value: wrong at every odd x.
define i8 @add_or_disjoint_src(i8 %x) {
  %r = add i8 %x, 1
  ret i8 %r
}

define i8 @add_or_disjoint_tgt(i8 %x) {
  %r = or disjoint i8 %x, 1
  ret i8 %r
}

; zext nneg is poison for a negative x, and equals sext elsewhere: right.
define i16 @zext_nneg_sext_src(i8 %x) {
  %r = zext nneg i8 %x to i16
  ret i16 %r
}

define i16 @zext_nneg_sext_tgt(i8 %x) {
  %r = sext i8 %x to i16
  ret i16 %r
}

; The other way, a negative x makes the target poison: wrong at 128..255.
define i16 @sext_zext_nneg_src(i8 %x) {
  %r = sext i8 %x to i16
  ret i16 %r
}

define i16 @sext_zext_nneg_tgt(i8 %x) {
  %r = zext nneg i8 %x to i16
  ret i16 %r
}

; Both exact forms are poison exactly when x isn't a multiple of 4: right.
define i8 @udiv_exact_lshr_exact_src(i8 %x) {
  %r = udiv exact i8 %x, 4
  ret i8 %r
}

define i8 @udiv_exact_lshr_exact_tgt(i8 %x) {
  %r = lshr exact i8 %x, 2
  ret i8 %r
}

; Adding exact makes the target poison where x isn't a multiple of 4: wrong there.
define i8 @udiv_lshr_exact_src(i8 %x) {
  %r = udiv i8 %x, 4
  ret i8 %r
}

define i8 @udiv_lshr_exact_tgt(i8 %x) {
  %r = lshr exact i8 %x, 2
  ret i8 %r
}

; samesign is poison where x and 5 have different signs, that is where x is negative, and ult and slt agree
; elsewhere: right.
define i1 @icmp_samesign_slt_src(i8 %x) {
  %r = icmp samesign ult i8 %x, 5
  ret i1 %r
}

define i1 @icmp_samesign_slt_tgt(i8 %x) {
  %r = icmp slt i8 %x, 5
  ret i1 %r
}

; Adding samesign makes the target poison for a negative x, where the source is false: wrong at 128..255.
define i1 @icmp_add_samesign_src(i8 %x) {
  %r = icmp ult i8 %x, 5
  ret i1 %r
}

define i1 @icmp_add_samesign_tgt(i8 %x) {
  %r = icmp samesign ult i8 %x, 5
  ret i1 %r
}

; A shift by 8 or more is poison, which 0 refines. Not equal, since the target has a value where the source is
; poison: right as a refinement, and an equality claim can't certify it.
define i8 @shl_overshift_zero_src(i8 %x) {
  %r = shl i8 1, %x
  ret i8 %r
}

define i8 @shl_overshift_zero_tgt(i8 %x) {
  %c = icmp ult i8 %x, 8
  %s = shl i8 1, %x
  %r = select i1 %c, i8 %s, i8 0
  ret i8 %r
}

; ctlz with is_zero_poison is poison at 0, where the target gives 8: right.
define i8 @ctlz_drop_zero_poison_src(i8 %x) {
  %r = call i8 @llvm.ctlz.i8(i8 %x, i1 true)
  ret i8 %r
}

define i8 @ctlz_drop_zero_poison_tgt(i8 %x) {
  %r = call i8 @llvm.ctlz.i8(i8 %x, i1 false)
  ret i8 %r
}

; The other way: wrong at 0 only.
define i8 @ctlz_add_zero_poison_src(i8 %x) {
  %r = call i8 @llvm.ctlz.i8(i8 %x, i1 false)
  ret i8 %r
}

define i8 @ctlz_add_zero_poison_tgt(i8 %x) {
  %r = call i8 @llvm.ctlz.i8(i8 %x, i1 true)
  ret i8 %r
}

; abs with int_min_poison is poison at -128, where the source returns -128: wrong at 128 only.
define i8 @abs_add_int_min_poison_src(i8 %x) {
  %r = call i8 @llvm.abs.i8(i8 %x, i1 false)
  ret i8 %r
}

define i8 @abs_add_int_min_poison_tgt(i8 %x) {
  %r = call i8 @llvm.abs.i8(i8 %x, i1 true)
  ret i8 %r
}

; Right when x can't be undef, and wrong when it can: x & 0 is 0, or poison, and an undef x can be a different
; value at each use, so x ^ x can be anything. IRLean has no undef, so it agrees with the first. This is why
; tools/binding.py needs every argument noundef.
define i8 @and_zero_xor_self_src(i8 %x) {
  %r = and i8 %x, 0
  ret i8 %r
}

define i8 @and_zero_xor_self_tgt(i8 %x) {
  %r = xor i8 %x, %x
  ret i8 %r
}

declare i8 @llvm.ctlz.i8(i8, i1)

declare i8 @llvm.abs.i8(i8, i1)
