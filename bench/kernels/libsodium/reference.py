#!/usr/bin/env python3
"""What bench/kernels/libsodium/secretstream.c prints, computed without libsodium: its known answer.
docs/kernels.md.

libsodium's own test of crypto_secretstream checks a round trip under a random key, and has no known answers,
so this is one. ChaCha20 and Poly1305 are written here from RFC 8439, HChaCha20 from the XChaCha draft,
draft-irtf-cfrg-xchacha-03, and BLAKE2b from RFC 7693, each checked against its document's test vector first.
The stream is built as libsodium's crypto_secretstream_xchacha20poly1305_push builds it, at the pin in
bench/kernels/manifest.toml, from the same seeds and pattern as the driver. Pure Python, so slow: about a
second a mebibyte on z, where the driver does a gibibyte in about two.

usage: bench/kernels/libsodium/reference.py [MIB]    MIB is 1, unless given; the driver's is 1024
"""

from __future__ import annotations

import struct
import sys

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF
CHUNK = 4096
TAG_FINAL = 3
SIGMA = "expand 32-byte k"
# randombytes_buf_deterministic's nonce, in libsodium's randombytes.c.
DRG = b"LibsodiumDRG"


def rotl32(x: int, n: int) -> int:
    return ((x << n) & M32) | (x >> (32 - n))


def chacha_rounds(s: list[int]) -> None:
    """ChaCha20's 20 rounds on a state of 16 words, RFC 8439, 2.3."""

    def quarter(a: int, b: int, c: int, d: int) -> None:
        s[a] = (s[a] + s[b]) & M32
        s[d] = rotl32(s[d] ^ s[a], 16)
        s[c] = (s[c] + s[d]) & M32
        s[b] = rotl32(s[b] ^ s[c], 12)
        s[a] = (s[a] + s[b]) & M32
        s[d] = rotl32(s[d] ^ s[a], 8)
        s[c] = (s[c] + s[d]) & M32
        s[b] = rotl32(s[b] ^ s[c], 7)

    for _ in range(10):
        quarter(0, 4, 8, 12)
        quarter(1, 5, 9, 13)
        quarter(2, 6, 10, 14)
        quarter(3, 7, 11, 15)
        quarter(0, 5, 10, 15)
        quarter(1, 6, 11, 12)
        quarter(2, 7, 8, 13)
        quarter(3, 4, 9, 14)


def chacha_block(key: bytes, counter: int, nonce: bytes) -> bytes:
    """A 64-byte block of ChaCha20's key stream, with a 12-byte nonce, RFC 8439, 2.3."""
    start = [*struct.unpack("<4I", SIGMA.encode()), *struct.unpack("<8I", key), counter & M32]
    start += struct.unpack("<3I", nonce)
    s = list(start)
    chacha_rounds(s)
    return struct.pack("<16I", *((a + b) & M32 for a, b in zip(s, start, strict=True)))


def chacha_xor(key: bytes, nonce: bytes, counter: int, data: bytes) -> bytes:
    """`data` encrypted with ChaCha20 from block `counter`, RFC 8439, 2.4."""
    out = bytearray()
    for i in range(0, len(data), 64):
        stream = chacha_block(key, counter + i // 64, nonce)
        out += bytes(x ^ y for x, y in zip(data[i : i + 64], stream, strict=False))
    return bytes(out)


def hchacha(key: bytes, nonce: bytes) -> bytes:
    """HChaCha20 of a 16-byte nonce: the subkey XChaCha20 encrypts with, draft-irtf-cfrg-xchacha-03, 2.2."""
    s = [*struct.unpack("<4I", SIGMA.encode()), *struct.unpack("<8I", key), *struct.unpack("<4I", nonce)]
    chacha_rounds(s)
    return struct.pack("<8I", *s[0:4], *s[12:16])


def poly1305(key: bytes, message: bytes) -> bytes:
    """Poly1305 of `message` under a one-time 32-byte key, RFC 8439, 2.5."""
    r = int.from_bytes(key[:16], "little") & 0x0FFFFFFC0FFFFFFC0FFFFFFC0FFFFFFF
    p = (1 << 130) - 5
    acc = 0
    for i in range(0, len(message), 16):
        acc = (acc + int.from_bytes(message[i : i + 16] + b"\x01", "little")) * r % p
    return ((acc + int.from_bytes(key[16:], "little")) & ((1 << 128) - 1)).to_bytes(16, "little")


IV = (
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179,
)
# The columns, then the diagonals, of BLAKE2b's 4 by 4 state, which each round mixes in turn.
MIXES = (
    (0, 4, 8, 12),
    (1, 5, 9, 13),
    (2, 6, 10, 14),
    (3, 7, 11, 15),
    (0, 5, 10, 15),
    (1, 6, 11, 12),
    (2, 7, 8, 13),
    (3, 4, 9, 14),
)
PERMUTATIONS = (
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
    (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
    (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4),
    (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8),
    (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13),
    (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9),
    (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11),
    (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10),
    (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5),
    (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0),
)


class Blake2b:
    """Unkeyed BLAKE2b, RFC 7693, with a digest of `size` bytes, fed a piece at a time."""

    def __init__(self, size: int) -> None:
        self.size = size
        self.h = list(IV)
        self.h[0] ^= 0x01010000 ^ size
        self.count = 0
        self.pending = b""

    def compress(self, block: bytes, last: bool) -> None:
        def rotr(x: int, n: int) -> int:
            return (x >> n) | ((x << (64 - n)) & M64)

        m = struct.unpack("<16Q", block)
        v = [*self.h, *IV]
        v[12] ^= self.count & M64
        v[13] ^= self.count >> 64
        if last:
            v[14] ^= M64
        for r in range(12):
            s = PERMUTATIONS[r % 10]
            for i, (a, b, c, d) in enumerate(MIXES):
                v[a] = (v[a] + v[b] + m[s[2 * i]]) & M64
                v[d] = rotr(v[d] ^ v[a], 32)
                v[c] = (v[c] + v[d]) & M64
                v[b] = rotr(v[b] ^ v[c], 24)
                v[a] = (v[a] + v[b] + m[s[2 * i + 1]]) & M64
                v[d] = rotr(v[d] ^ v[a], 16)
                v[c] = (v[c] + v[d]) & M64
                v[b] = rotr(v[b] ^ v[c], 63)
        self.h = [h ^ v[i] ^ v[i + 8] for i, h in enumerate(self.h)]

    def update(self, data: bytes) -> None:
        self.pending += data
        # The last block is compressed differently, so one is always kept back.
        while len(self.pending) > 128:
            self.count += 128
            self.compress(self.pending[:128], False)
            self.pending = self.pending[128:]

    def digest(self) -> bytes:
        self.count += len(self.pending)
        self.compress(self.pending.ljust(128, b"\0"), True)
        return struct.pack("<8Q", *self.h)[: self.size]


def check_vectors() -> None:
    """Each primitive against its document's test vector."""
    key = bytes(range(32))
    block = chacha_block(key, 1, bytes.fromhex("000000090000004a00000000"))
    assert block.hex().startswith("10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e"), "8439"
    sunscreen = (
        b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, "
        b"sunscreen would be it."
    )
    encrypted = chacha_xor(key, bytes.fromhex("000000000000004a00000000"), 1, sunscreen)
    assert encrypted.hex().endswith("5af90bbf74a35be6b40b8eedf2785e42874d"), "RFC 8439, 2.4.2"
    one_time = bytes.fromhex("85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
    tag = poly1305(one_time, b"Cryptographic Forum Research Group")
    assert tag.hex() == "a8061dc1305136c6c22b8baf0c0127a9", "RFC 8439, 2.5.2"
    subkey = hchacha(key, bytes.fromhex("000000090000004a0000000031415927"))
    assert subkey.hex() == "82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc", "xchacha 2.2.1"
    h = Blake2b(64)
    h.update(b"abc")
    assert h.digest().hex() == (
        "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
        "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
    ), "RFC 7693, appendix A"


def seed(text: str) -> bytes:
    """A seed as the driver writes one: a string, padded with zeros to 32 bytes."""
    return text.encode().ljust(32, b"\0")


def secretstream(mib: int) -> str:
    """The line secretstream.c prints for MIB mebibytes."""
    # randombytes_buf_deterministic is ChaCha20 from the seed, with the nonce "LibsodiumDRG".
    key = chacha_xor(seed("ir-lean kernel corpus: key"), DRG, 0, bytes(32))
    header = chacha_xor(seed("ir-lean kernel corpus: header"), DRG, 0, bytes(24))
    # init_push: the stream's key is HChaCha20 of the header's first 16 bytes, and its nonce a 4-byte counter
    # from 1, then the header's last 8 bytes.
    k = hchacha(key, header[:16])
    counter, inonce = 1, bytearray(header[16:])
    digest = Blake2b(32)
    digest.update(header)
    m = bytearray((j * 2654435761 >> 24) & 0xFF for j in range(CHUNK))
    chunks = mib * (1 << 20) // CHUNK
    for i in range(chunks):
        m[:8] = struct.pack("<Q", i)
        tag = TAG_FINAL if i + 1 == chunks else 0
        nonce = struct.pack("<I", counter) + bytes(inonce)
        # push: Poly1305's key from block 0, the tag in a block of its own, block 1, then the message from 2,
        # and the MAC over the tag's block, the ciphertext, padding and both lengths. No additional data.
        one_time = chacha_block(k, 0, nonce)[:32]
        tag_block = chacha_xor(k, nonce, 1, bytes([tag]) + bytes(63))
        c = chacha_xor(k, nonce, 2, bytes(m))
        padding = bytes((0x10 - 64 + len(c)) & 0xF)
        mac = poly1305(one_time, tag_block + c + padding + struct.pack("<QQ", 0, 64 + len(c)))
        digest.update(tag_block[:1] + c + mac)
        for j in range(8):
            inonce[j] ^= mac[j]
        counter = (counter + 1) & M32
        # A counter that wraps rekeys the stream, which a gibibyte doesn't reach.
        assert counter != 0
    return f"{digest.digest().hex()}  {chunks * CHUNK} bytes in {chunks} chunks"


def main(argv: list[str]) -> int:
    if len(argv) > 1 or (argv and not argv[0].isdigit()) or (argv and int(argv[0]) < 1):
        print(__doc__, file=sys.stderr)
        return 2
    check_vectors()
    print(secretstream(int(argv[0]) if argv else 1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
