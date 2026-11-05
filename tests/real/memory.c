// Pointers, arrays, structs, globals and the memory intrinsics, reachable from functions that only
// take integers, so tests/differential.py can call them. The noinline attributes keep the pointer
// arguments in the IR.
#include <stddef.h>
#define NOINLINE __attribute__((noinline))

static const unsigned short table[8] = {3, 1, 4, 1, 5, 9, 2, 6};
static unsigned counter = 7;

struct pair {
    unsigned char tag;
    unsigned value;
    unsigned long long big;
};

NOINLINE unsigned long long sum_bytes(const unsigned char *p, size_t n) {
    unsigned long long s = 0;
    for (size_t i = 0; i < n; i++)
        s += p[i];
    return s;
}

NOINLINE void fill(unsigned char *p, size_t n, unsigned seed) {
    for (size_t i = 0; i < n; i++) {
        seed = seed * 1664525u + 1013904223u;
        p[i] = (unsigned char)(seed >> 24);
    }
}

NOINLINE void swap_ends(unsigned *p, size_t n) {
    unsigned *q = p + n - 1;
    while (p < q) {
        unsigned t = *p;
        *p++ = *q;
        *q-- = t;
    }
}

NOINLINE unsigned store_struct(struct pair *s, unsigned v) {
    s->tag = (unsigned char)v;
    s->value = v * 3;
    s->big = (unsigned long long)v << 33;
    return s->tag + s->value + (unsigned)(s->big >> 32);
}

unsigned long long test_sum(unsigned seed, unsigned len) {
    unsigned char buf[64];
    size_t n = len % 65;
    fill(buf, n, seed);
    return sum_bytes(buf, n);
}

unsigned test_swap(unsigned a, unsigned b) {
    unsigned v[5] = {a, b, a ^ b, a + b, a - b};
    swap_ends(v, 5);
    return v[0] * 7 + v[1] * 5 + v[2] * 3 + v[3];
}

unsigned test_struct(unsigned v) {
    struct pair s;
    return store_struct(&s, v);
}

unsigned test_table(unsigned i) { return table[i & 7] + table[(i >> 3) & 7]; }

// Puts the global back, because tests/differential.py expects each call to start the same way.
unsigned test_global(unsigned v) {
    unsigned old = counter;
    counter = old + v;
    unsigned r = counter;
    counter = old;
    return r;
}

unsigned long long test_memory_intrinsics(unsigned seed, unsigned n) {
    unsigned char a[32], b[32];
    size_t k = n % 33;
    __builtin_memset(a, (int)seed, sizeof a);
    __builtin_memcpy(b, a, sizeof b);
    fill(a, k, seed);
    __builtin_memcpy(b, a, k);
    return sum_bytes(b, sizeof b);
}

// Stores a pointer in memory and reads it back through two levels.
NOINLINE unsigned read_through(unsigned **pp) { return **pp; }

unsigned test_pointer_in_memory(unsigned v) {
    unsigned x = v;
    unsigned *p = &x;
    return read_through(&p) + 1;
}

long long test_pointer_difference(unsigned i, unsigned j) {
    unsigned char a[16];
    unsigned char *p = a + (i & 15), *q = a + (j & 15);
    return p - q;
}

int test_pointer_compare(unsigned i, unsigned j) {
    unsigned a[8];
    return (a + (i & 7)) < (a + (j & 7));
}
