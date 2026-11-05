unsigned bi_reverse(unsigned code, int len) {
    __builtin_assume(len >= 1);
    __builtin_assume(len <= 31);
    unsigned res = 0;
    do {
        res |= code & 1;
        code >>= 1, res <<= 1;
    } while (--len > 0);
    return res >> 1;
}

unsigned popcount(unsigned x) {
    unsigned c = 0;
    while (x) {
        c += x & 1;
        x >>= 1;
    }
    return c;
}
