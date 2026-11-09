import IRLean.Generic.Arith

open IRLean IRLean.Generic

/-- False: in `i1`, `shl x, 1` is poison and `add x, x` isn't. This drops `add_self`'s width hypothesis, and
`tests/generic_rewrites.sh` checks that it fails to check. -/
theorem add_self_any_width {w : Nat} (a : Val w) : Val.add a a = Val.shl a (some 1#w) :=
  add_self a false false (by omega)
