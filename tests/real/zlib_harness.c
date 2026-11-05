// Calls real zlib from functions that only take integers, so tests/differential.py can compare them
// against native code. The input repeats enough to compress, and is small because the semantics are
// slow to run. It's linked with all of zlib before translating, and each function is there to reach
// part of zlib the others don't.
#define _LARGEFILE64_SOURCE 1
#include "zlib.h"

#define HARNESS_INPUT 64

static unsigned strlen_of(const char *p) {
    unsigned n = 0;
    while (p[n])
        n++;
    return n;
}

static void fill(unsigned char *p, unsigned n, unsigned seed) {
    for (unsigned i = 0; i < n; i++) {
        seed = seed * 1664525u + 1013904223u;
        p[i] = (unsigned char)((seed >> 28) & 7) + 'a';
    }
}

unsigned harness_adler32(unsigned seed, unsigned n, unsigned start) {
    unsigned char in[256];
    n %= sizeof in;
    fill(in, n, seed);
    return (unsigned)adler32(start, in, n);
}

unsigned harness_crc32(unsigned seed, unsigned n, unsigned start) {
    unsigned char in[256];
    n %= sizeof in;
    fill(in, n, seed);
    return (unsigned)crc32(start, in, n);
}

unsigned harness_combine(unsigned a, unsigned b, unsigned n) {
    return (unsigned)(adler32_combine(a, b, n) ^ crc32_combine(a, b, n));
}

unsigned harness_bound(unsigned n) {
    return (unsigned)(compressBound(n) ^ (zlibCompileFlags() << 7));
}

// Compresses and uncompresses, returning a checksum of both results, so anything wrong shows up.
unsigned harness_roundtrip(unsigned seed, unsigned n, unsigned level) {
    unsigned char in[HARNESS_INPUT], packed[HARNESS_INPUT + 128], out[HARNESS_INPUT];
    uLongf packed_len = sizeof packed, out_len = sizeof out;
    n %= HARNESS_INPUT;
    fill(in, n, seed);
    int r = compress2(packed, &packed_len, in, n, (int)(level % 10));
    if (r != Z_OK)
        return 0xE0000000u | (unsigned)(r & 0xff);
    r = uncompress(out, &out_len, packed, packed_len);
    if (r != Z_OK)
        return 0xF0000000u | (unsigned)(r & 0xff);
    return (unsigned)(crc32(0, packed, (unsigned)packed_len) ^ adler32(1, out, (unsigned)out_len));
}

// Feeds `inflate` a damaged stream: it must report the damage, not run off the end.
unsigned harness_damaged(unsigned seed, unsigned n, unsigned where) {
    unsigned char in[HARNESS_INPUT], packed[HARNESS_INPUT + 128], out[HARNESS_INPUT];
    uLongf packed_len = sizeof packed, out_len = sizeof out;
    n %= HARNESS_INPUT;
    fill(in, n, seed);
    if (compress(packed, &packed_len, in, n) != Z_OK)
        return 0xE0000000u;
    packed[where % packed_len] ^= (unsigned char)(1u << (where % 8));
    int r = uncompress(out, &out_len, packed, packed_len);
    return (unsigned)(r & 0xff) << 24 ^ (unsigned)out_len;
}

// Sums what a stream produced, so any difference in it shows up in the result.
static unsigned digest(const unsigned char *p, unsigned n, unsigned status) {
    return (unsigned)(crc32(0, p, n) ^ adler32(1, p, n)) + status * 16777619u;
}

// A small window, so `deflate` has to slide it, at any level and strategy, inflated back into a large
// buffer so `inflate_fast` runs.
static unsigned slide_and_back(unsigned seed, unsigned n, int level, int strategy) {
    unsigned char in[1000], packed[1300], out[1000];
    z_stream d = {0}, i = {0};
    n = 780 + n % 40;
    fill(in, n, seed);
    if (deflateInit2(&d, level, Z_DEFLATED, 9, 1, strategy) != Z_OK)
        return 0xE1000000u;
    d.next_in = in;
    d.avail_in = n;
    d.next_out = packed;
    d.avail_out = sizeof packed;
    int r = deflate(&d, Z_FINISH);
    unsigned packed_len = (unsigned)d.total_out;
    deflateEnd(&d);
    if (r != Z_STREAM_END)
        return 0xE2000000u | (unsigned)(r & 0xff);
    if (inflateInit2(&i, 15) != Z_OK)
        return 0xE3000000u;
    i.next_in = packed;
    i.avail_in = packed_len;
    i.next_out = out;
    i.avail_out = sizeof out;
    r = inflate(&i, Z_FINISH);
    unsigned out_len = (unsigned)i.total_out;
    inflateEnd(&i);
    return digest(packed, packed_len, 1) ^ digest(out, out_len, (unsigned)(r & 0xff));
}

// Levels are low, because higher ones take far too long in the semantics.
unsigned harness_slow_fast_level(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 1, Z_DEFAULT_STRATEGY);
}

unsigned harness_slow_lazy_level(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 4, Z_DEFAULT_STRATEGY);
}

unsigned harness_slow_stored(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 0, Z_DEFAULT_STRATEGY);
}

unsigned harness_slow_filtered(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 4, Z_FILTERED);
}

unsigned harness_slow_huffman(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 1, Z_HUFFMAN_ONLY);
}

unsigned harness_slow_rle(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 1, Z_RLE);
}

unsigned harness_slow_fixed(unsigned seed, unsigned n) {
    return slide_and_back(seed, n, 1, Z_FIXED);
}

// A preset dictionary, both ways.
unsigned harness_dictionary(unsigned seed, unsigned n) {
    unsigned char dict[32], got[64], in[HARNESS_INPUT], packed[HARNESS_INPUT + 128], out[HARNESS_INPUT];
    z_stream d = {0}, i = {0};
    uInt got_len = 0;
    n %= HARNESS_INPUT;
    fill(dict, sizeof dict, seed);
    fill(in, n, seed);
    if (deflateInit(&d, Z_DEFAULT_COMPRESSION) != Z_OK)
        return 0xE1000000u;
    deflateSetDictionary(&d, dict, sizeof dict);
    deflateGetDictionary(&d, got, &got_len);
    d.next_in = in;
    d.avail_in = n;
    d.next_out = packed;
    d.avail_out = sizeof packed;
    deflate(&d, Z_FINISH);
    unsigned packed_len = (unsigned)d.total_out;
    deflateEnd(&d);
    if (inflateInit(&i) != Z_OK)
        return 0xE2000000u;
    i.next_in = packed;
    i.avail_in = packed_len;
    i.next_out = out;
    i.avail_out = sizeof out;
    int r = inflate(&i, Z_NO_FLUSH);
    unsigned first = (unsigned)(r & 0xff);
    if (r == Z_NEED_DICT) {
        inflateSetDictionary(&i, dict, sizeof dict);
        r = inflate(&i, Z_FINISH);
    }
    uInt got_i = 0;
    inflateGetDictionary(&i, got, &got_i);
    unsigned out_len = (unsigned)i.total_out;
    inflateEnd(&i);
    return digest(out, out_len, first) ^ digest(packed, packed_len, (unsigned)(r & 0xff)) ^ got_len ^ got_i;
}

// The rest of the `deflate` calls, with flushes that write each kind of block.
unsigned harness_deflate_calls(unsigned seed, unsigned n, unsigned level) {
    unsigned char in[HARNESS_INPUT], packed[HARNESS_INPUT + 256];
    z_stream d = {0}, copy = {0};
    unsigned pending = 0, status = 0;
    int bits = 0;
    n %= HARNESS_INPUT;
    fill(in, n, seed);
    if (deflateInit(&d, (int)(level % 10)) != Z_OK)
        return 0xE1000000u;
    deflateTune(&d, 4, 4, 8, 4);
    status += (unsigned)deflatePrime(&d, 3, 5);
    d.next_in = in;
    d.avail_in = n / 2;
    d.next_out = packed;
    d.avail_out = sizeof packed;
    status += (unsigned)deflate(&d, Z_SYNC_FLUSH);
    status += (unsigned)deflatePending(&d, &pending, &bits);
    status += (unsigned)deflateParams(&d, (int)((level + 3) % 10), Z_DEFAULT_STRATEGY);
    d.avail_in = n - n / 2;
    status += (unsigned)deflate(&d, Z_BLOCK);
    status += (unsigned)deflate(&d, Z_FULL_FLUSH);
    status += (unsigned)deflate(&d, Z_PARTIAL_FLUSH);
    status += (unsigned)deflateCopy(&copy, &d);
    status += (unsigned)deflate(&d, Z_FINISH);
    unsigned used = 0;
    status += (unsigned)deflateUsed(&d, (int *)&used);
    unsigned bound = (unsigned)deflateBound(&d, n);
    status += (unsigned)deflateReset(&d);
    unsigned result = digest(packed, (unsigned)sizeof packed - d.avail_out, status) ^ pending ^ bound ^ used;
    deflateEnd(&d);
    deflateEnd(&copy);
    return result;
}

// A gzip stream with a header, and the rest of the `inflate` calls.
unsigned harness_inflate_calls(unsigned seed, unsigned n, unsigned where) {
    unsigned char in[HARNESS_INPUT], packed[HARNESS_INPUT + 256], out[HARNESS_INPUT];
    Bytef name[] = "name", comment[] = "note", extra[] = "extra", got_name[8], got_comment[8], got_extra[8];
    gz_header head = {0}, got = {0};
    z_stream d = {0}, i = {0}, copy = {0};
    unsigned status = 0;
    n %= HARNESS_INPUT;
    fill(in, n, seed);
    head.name = name;
    head.comment = comment;
    head.extra = extra;
    head.extra_len = 5;
    head.hcrc = 1;
    if (deflateInit2(&d, 6, Z_DEFLATED, 15 + 16, 8, Z_DEFAULT_STRATEGY) != Z_OK)
        return 0xE1000000u;
    status += (unsigned)deflateSetHeader(&d, &head);
    d.next_in = in;
    d.avail_in = n;
    d.next_out = packed;
    d.avail_out = sizeof packed;
    deflate(&d, Z_FINISH);
    unsigned packed_len = (unsigned)d.total_out;
    deflateEnd(&d);
    got.name = got_name;
    got.name_max = sizeof got_name;
    got.comment = got_comment;
    got.comm_max = sizeof got_comment;
    got.extra = got_extra;
    got.extra_max = sizeof got_extra;
    if (inflateInit2(&i, 15 + 32) != Z_OK)
        return 0xE2000000u;
    status += (unsigned)inflateGetHeader(&i, &got);
    status += (unsigned)inflateValidate(&i, 1);
    i.next_in = packed;
    i.avail_in = packed_len / 2;
    i.next_out = out;
    i.avail_out = sizeof out;
    status += (unsigned)inflate(&i, Z_BLOCK);
    long mark = inflateMark(&i);
    status += (unsigned)inflateSyncPoint(&i);
    status += (unsigned)inflateCodesUsed(&i);
    status += (unsigned)inflateCopy(&copy, &i);
    i.avail_in = packed_len - packed_len / 2;
    status += (unsigned)inflate(&i, Z_FINISH);
    inflateEnd(&copy);
    status += (unsigned)inflateUndermine(&i, 0);
    status += (unsigned)inflateReset2(&i, 15);
    status += (unsigned)inflatePrime(&i, 3, 5);
    i.next_in = packed;
    i.avail_in = packed_len;
    packed[where % packed_len] ^= 0x55;
    status += (unsigned)inflateSync(&i);
    unsigned out_len = HARNESS_INPUT - i.avail_out;
    inflateEnd(&i);
    return digest(out, out_len, status) ^ (unsigned)mark ^ got.extra_len ^ digest(got_name, 4, got.done);
}

// `inflateBack`, which reads and writes through callbacks.
struct back_state {
    unsigned char *next;
    unsigned left;
    unsigned total;
    unsigned sum;
};

static unsigned back_in(void *desc, z_const unsigned char **buf) {
    struct back_state *s = desc;
    unsigned n = s->left;
    *buf = s->next;
    s->left = 0;
    return n;
}

static int back_out(void *desc, unsigned char *buf, unsigned n) {
    struct back_state *s = desc;
    s->total += n;
    s->sum = (unsigned)adler32(s->sum, buf, n);
    return 0;
}

unsigned harness_back(unsigned seed, unsigned n) {
    unsigned char in[HARNESS_INPUT], packed[HARNESS_INPUT + 128], window[32768];
    z_stream d = {0}, i = {0};
    struct back_state s = {packed, 0, 0, 1};
    n %= HARNESS_INPUT;
    fill(in, n, seed);
    if (deflateInit2(&d, 6, Z_DEFLATED, -15, 8, Z_DEFAULT_STRATEGY) != Z_OK)
        return 0xE1000000u;
    d.next_in = in;
    d.avail_in = n;
    d.next_out = packed;
    d.avail_out = sizeof packed;
    deflate(&d, Z_FINISH);
    s.left = (unsigned)d.total_out;
    deflateEnd(&d);
    if (inflateBackInit(&i, 15, window) != Z_OK)
        return 0xE2000000u;
    int r = inflateBack(&i, back_in, &s, back_out, &s);
    inflateBackEnd(&i);
    return s.sum ^ s.total ^ ((unsigned)(r & 0xff) << 24);
}

unsigned harness_misc(unsigned x, unsigned y) {
    unsigned char in[32], packed[128], out[32];
    z_size_t packed_len = sizeof packed, out_len = sizeof out;
    fill(in, sizeof in, x);
    unsigned status = (unsigned)compress_z(packed, &packed_len, in, sizeof in);
    status += (unsigned)uncompress_z(out, &out_len, packed, packed_len);
    status += (unsigned)strlen_of(zError((int)(x % 8) - 6)) + (unsigned)strlen_of(zlibVersion());
    return status ^ digest(out, (unsigned)out_len, 1) ^ (unsigned)get_crc_table()[x & 255] ^
           (unsigned)adler32_combine64(x, y, x) ^ (unsigned)crc32_combine64(x, y, y) ^
           (unsigned)crc32_combine_op(x, y, crc32_combine_gen64(x));
}
