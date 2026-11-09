#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef unsigned char bytes32 __attribute__((vector_size(32)));
extern bytes32 src(uint32_t);
extern bytes32 tgt(uint32_t);

static int check(uint32_t x) {
  bytes32 a = src(x), b = tgt(x);
  unsigned char av[32], bv[32];
  memcpy(av, &a, sizeof av);
  memcpy(bv, &b, sizeof bv);
  for (unsigned j = 0; j < 32; ++j) {
    unsigned expected = (x >> j) & 1 ? 0 : 240;
    if (av[j] != expected || bv[j] != expected) {
      fprintf(stderr, "x=%08x lane=%u src=%u tgt=%u expected=%u\n", x, j, av[j], bv[j], expected);
      return 1;
    }
  }
  return 0;
}

int main(void) {
  if (check(0) || check(UINT32_MAX))
    return 1;
  for (unsigned bit = 0; bit < 32; ++bit)
    if (check(UINT32_C(1) << bit) || check(~(UINT32_C(1) << bit)))
      return 1;
  uint32_t x = UINT32_C(0xb4e027a1);
  for (unsigned i = 0; i < 1000000; ++i) {
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    if (check(x))
      return 1;
  }
  puts("Both exact helper lowerings match the byte reference on 1000066 inputs, all 32 lanes.");
  return 0;
}
