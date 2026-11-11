// libsodium's bulk-encryption workload in the kernel corpus, decision 7 of 2026-11-10: docs/kernels.md.
//
// libsodium's documented crypto_secretstream example, with memory in place of its files:
// https://doc.libsodium.org/secret-key_cryptography/secretstream. XChaCha20-Poly1305 in 4096-byte chunks,
// the last one tagged final. It encrypts MIB mebibytes of a fixed pattern under a key and a header drawn
// from fixed seeds, pulls each chunk back with libsodium's decryption and compares it with what went in,
// and prints the BLAKE2b-256 of the header and every encrypted chunk, so that two builds' results can be
// compared bit for bit. Nothing in it is random.
//
// usage: secretstream [MIB]    MIB is 1024 unless given. Exits 1 if a chunk doesn't decrypt to what went in.
#include <sodium.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHUNK_SIZE 4096

static const unsigned char key_seed[randombytes_SEEDBYTES] = "ir-lean kernel corpus: key";
static const unsigned char header_seed[randombytes_SEEDBYTES] = "ir-lean kernel corpus: header";

// What init_push draws the header from: the same bytes every time.
static void fixed_buf(void *const buf, const size_t size) {
  randombytes_buf_deterministic(buf, size, header_seed);
}
static uint32_t fixed_random(void) {
  uint32_t r;
  fixed_buf(&r, sizeof r);
  return r;
}
static const char *fixed_name(void) { return "fixed"; }
static randombytes_implementation fixed = {fixed_name, fixed_random, NULL, NULL, fixed_buf, NULL};

int main(int argc, char **argv) {
  unsigned char m[CHUNK_SIZE], d[CHUNK_SIZE], c[CHUNK_SIZE + crypto_secretstream_xchacha20poly1305_ABYTES];
  unsigned char key[crypto_secretstream_xchacha20poly1305_KEYBYTES];
  unsigned char header[crypto_secretstream_xchacha20poly1305_HEADERBYTES];
  unsigned char hash[crypto_generichash_BYTES], tag, pulled;
  char hex[2 * crypto_generichash_BYTES + 1];
  crypto_secretstream_xchacha20poly1305_state push, pull;
  crypto_generichash_state h;
  unsigned long long clen, mlen;
  const unsigned long long chunks = (argc > 1 ? strtoull(argv[1], NULL, 10) : 1024) * (1 << 20) / CHUNK_SIZE;

  randombytes_set_implementation(&fixed);
  if (chunks == 0 || sodium_init() != 0) {
    return 2;
  }
  randombytes_buf_deterministic(key, sizeof key, key_seed);
  for (size_t j = 0; j < CHUNK_SIZE; j++) {
    m[j] = (unsigned char)(j * 2654435761u >> 24);
  }
  crypto_secretstream_xchacha20poly1305_init_push(&push, header, key);
  crypto_secretstream_xchacha20poly1305_init_pull(&pull, header, key);
  crypto_generichash_init(&h, NULL, 0, sizeof hash);
  crypto_generichash_update(&h, header, sizeof header);
  for (unsigned long long i = 0; i < chunks; i++) {
    memcpy(m, &i, sizeof i);
    tag = i + 1 == chunks ? crypto_secretstream_xchacha20poly1305_TAG_FINAL : 0;
    crypto_secretstream_xchacha20poly1305_push(&push, c, &clen, m, sizeof m, NULL, 0, tag);
    crypto_generichash_update(&h, c, clen);
    if (crypto_secretstream_xchacha20poly1305_pull(&pull, d, &mlen, &pulled, c, clen, NULL, 0) != 0 ||
        pulled != tag || mlen != sizeof m || memcmp(d, m, sizeof m) != 0) {
      fprintf(stderr, "chunk %llu doesn't decrypt to what went in\n", i);
      return 1;
    }
  }
  crypto_generichash_final(&h, hash, sizeof hash);
  printf("%s  %llu bytes in %llu chunks\n", sodium_bin2hex(hex, sizeof hex, hash, sizeof hash),
         chunks * CHUNK_SIZE, chunks);
  return 0;
}
