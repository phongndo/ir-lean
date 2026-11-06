// Function pointers and pointers held in globals, reachable from functions that only take integers,
// so tests/differential.py can call them. Everything allocated is freed, so running the Lean and
// native versions side by side stays simple.
#include <stdlib.h>
#include <string.h>
#define NOINLINE __attribute__((noinline))

NOINLINE static unsigned add_one(unsigned x) { return x + 1; }
NOINLINE static unsigned twice(unsigned x) { return x * 2; }
NOINLINE static unsigned negate(unsigned x) { return 0u - x; }
// Uses memory where the others don't, so a pointer of this type reaches both kinds of function.
static unsigned last;
NOINLINE static unsigned remember(unsigned x) {
  unsigned old = last;
  last = x;
  last = old;
  return old ^ x;
}

typedef unsigned (*op)(unsigned);
static op const ops[4] = {add_one, twice, negate, remember};
static const char *const names[3] = {"one", "three", ""};
static const char hello[] = "hello";
static const char *const inner = hello + 2;

struct entry {
  const char *name;
  op function;
  unsigned weight;
};
static const struct entry table[2] = {{"first", add_one, 3}, {"second!", twice, 5}};

NOINLINE unsigned call_table(unsigned which, unsigned x) { return ops[which % 4](x); }

NOINLINE static unsigned apply_twice(op f, unsigned x) { return f(f(x)); }
unsigned pass_pointer(unsigned which, unsigned x) { return apply_twice(ops[which % 4], x); }

unsigned compare_pointers(unsigned a, unsigned b) { return ops[a % 4] == ops[b % 4]; }

unsigned name_length(unsigned which) { return (unsigned)strlen(names[which % 3]); }

unsigned offset_pointer(unsigned i) { return (unsigned char)inner[i % 4]; }

unsigned table_entry(unsigned which, unsigned x) {
  const struct entry *e = &table[which % 2];
  return e->function(x) + e->weight + (unsigned)strlen(e->name);
}

unsigned heap_sum(unsigned n, unsigned seed) {
  n %= 40;
  unsigned *p = malloc(sizeof(unsigned) * (n + 1));
  if (!p)
    return 0xffffffffu;
  for (unsigned i = 0; i <= n; i++)
    p[i] = seed * i;
  unsigned total = 0;
  for (unsigned i = 0; i <= n; i++)
    total += p[i];
  free(p);
  free(NULL);
  return total;
}

// Recursion that goes through a pointer: `down` calls itself through this table.
NOINLINE static unsigned down(unsigned n);
static op const self[1] = {down};
NOINLINE static unsigned down(unsigned n) { return n == 0 ? 7 : self[0](n - 1) + 1; }
unsigned recurse_pointer(unsigned n) { return down(n % 20); }
