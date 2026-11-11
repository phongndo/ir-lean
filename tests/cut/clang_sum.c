unsigned sum(const unsigned *p, unsigned n) {
  unsigned acc = 0;
  for (unsigned i = 0; i < n; i++) acc += p[i] * 3u;
  return acc;
}
