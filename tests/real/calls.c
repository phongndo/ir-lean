// Calls and recursion that survive -O2: the noinline attributes keep the calls in the IR.
#define NOINLINE __attribute__((noinline))

NOINLINE unsigned twice(unsigned x) { return x * 2; }

NOINLINE unsigned add_twice(unsigned a, unsigned b) { return twice(a) + twice(b); }

// Not a tail call, so -O2 can't turn this into a loop.
NOINLINE unsigned fib(unsigned n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }

// Mutual recursion, kept from collapsing into one function by the noinline.
NOINLINE unsigned is_odd(unsigned n);

NOINLINE unsigned is_even(unsigned n) { return n == 0 ? 1 : is_odd(n - 1) + 0; }

NOINLINE unsigned is_odd(unsigned n) { return n == 0 ? 0 : is_even(n - 1) ^ 0; }

NOINLINE unsigned collatz_steps(unsigned long long n) {
  unsigned steps = 0;
  while (n > 1 && steps < 1000) {
    n = n % 2 ? 3 * n + 1 : n / 2;
    ++steps;
  }
  return steps;
}

unsigned checked_div(unsigned a, unsigned b) { return b ? a / b : 0; }

int sat_add(int a, int b) {
  int r;
  if (__builtin_add_overflow(a, b, &r))
    return a < 0 ? -2147483647 - 1 : 2147483647;
  return r;
}

unsigned char classify(unsigned char c) {
  switch (c) {
  case 'a':
    return 1;
  case 'b':
    return 2;
  case 'z':
    return 26;
  case 0:
    return 0;
  default:
    return 255;
  }
}
