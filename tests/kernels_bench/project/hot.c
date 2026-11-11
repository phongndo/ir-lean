// The synthetic project's program: `hot sum N` or `hot mix N` hashes a 64 KiB buffer through kernel.c, and
// prints the hash, so a run's output says whether the kernel computed the same thing. N scales the work.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t kernel(const uint8_t *p, size_t n, uint64_t h);

enum { SIZE = 1 << 16 };
static uint8_t buffer[SIZE];

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: hot sum|mix N\n");
    return 2;
  }
  long n = atol(argv[2]);
  uint64_t x = 0x9e3779b97f4a7c15ULL;
  for (size_t i = 0; i < SIZE; i++) {
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    buffer[i] = (uint8_t)x;
  }
  uint64_t h = 0xcbf29ce484222325ULL;
  if (strcmp(argv[1], "sum") == 0) {
    for (long r = 0; r < 64 * n; r++)
      h = kernel(buffer, SIZE, h);
  } else if (strcmp(argv[1], "mix") == 0) {
    for (long r = 0; r < 96 * n; r++)
      h = kernel(buffer + r % 7, SIZE / 2 + r % 13, h ^ (uint64_t)r);
  } else {
    return 2;
  }
  printf("%016llx\n", (unsigned long long)h);
  return 0;
}
