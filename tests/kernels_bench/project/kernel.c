// The synthetic project's hot unit: a hash whose every step waits on the last, so its time is the chain's.
// Compiled with -DEXTRA_LOOP, it runs the chain twice and returns the same hash: a candidate known slower.
// With -DWRONG_RESULT, it returns another hash: a candidate the output check has to refuse.
#include <stddef.h>
#include <stdint.h>

uint64_t kernel(const uint8_t *p, size_t n, uint64_t h) {
  for (size_t i = 0; i < n; i++) {
    h ^= p[i];
    h *= 0x100000001b3ULL;
    h ^= h >> 29;
  }
#ifdef EXTRA_LOOP
  uint64_t g = h;
  for (size_t i = 0; i < n; i++) {
    g ^= p[i];
    g *= 0x100000001b3ULL;
    g ^= g >> 29;
  }
  // Keeps the second chain, which changes nothing the function returns.
  __asm__ volatile("" : : "r"(g));
#endif
#ifdef WRONG_RESULT
  h ^= 1;
#endif
  return h;
}
