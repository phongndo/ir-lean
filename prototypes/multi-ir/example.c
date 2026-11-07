/* PROTOTYPE, research only: the minimal example for docs/multi-ir.md. Not part of any test or claim. */

/* The same loop as tests/real/bi_reverse.c, so its existing proof is the reference. */
unsigned popcount(unsigned x) {
  unsigned c = 0;
  while (x) {
    c += x & 1;
    x >>= 1;
  }
  return c;
}

/* Signed addition only on one arm. A compiler that computes it on both arms has to say what overflow
   then means: LLVM IR keeps `add nsw`, since overflow is only poison, and GIMPLE can't, since
   overflow there is undefined at the addition itself. */
int pick(int c, int a, int b) { return c ? a + b : 0; }
