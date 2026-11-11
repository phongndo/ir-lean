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

// Functions hot doesn't call, for the checks that compare what each function refers to. With -DOTHER_REFS,
// `pick` loads another table and `scale` multiplies by another constant, by the same instructions. With
// -DOTHER_TABLE, `lookup`'s table holds other numbers, and no instruction changes.
const uint32_t first[4] = {1, 2, 3, 4};
const uint32_t second[4] = {5, 6, 7, 8};
#ifdef OTHER_TABLE
const uint32_t third[4] = {9, 10, 11, 13};
#else
const uint32_t third[4] = {9, 10, 11, 12};
#endif

uint32_t pick(size_t i) {
#ifdef OTHER_REFS
  return second[i & 3];
#else
  return first[i & 3];
#endif
}

double scale(double x) {
#ifdef OTHER_REFS
  return x * 5.0;
#else
  return x * 3.0;
#endif
}

uint32_t lookup(size_t i) { return third[i & 3]; }
