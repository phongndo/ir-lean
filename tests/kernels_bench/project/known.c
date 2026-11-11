// The synthetic project's own test of kernel.c against a known answer. `make known` compiles its own copy of
// kernel.c, in own/, and links this with it, as xxHash's `make test-inline-dispatch` compiles its own
// xxh_x86dispatch.c in tests/: bench/kernels/harness.py has to put the candidate's object there.
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

uint64_t kernel(const uint8_t *p, size_t n, uint64_t h);

int main(void) {
  uint8_t buffer[4096];
  uint64_t x = 0x9e3779b97f4a7c15ULL;
  for (size_t i = 0; i < sizeof buffer; i++) {
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    buffer[i] = (uint8_t)x;
  }
  uint64_t got = kernel(buffer, sizeof buffer, 0xcbf29ce484222325ULL);
  if (got != 0x3afa5581390eef7fULL) {
    printf("kernel: %016llx, and the known answer is 3afa5581390eef7f\n", (unsigned long long)got);
    return 1;
  }
  printf("kernel: the known answer\n");
  return 0;
}
