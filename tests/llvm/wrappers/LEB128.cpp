// Gives LLVM's inline functions in llvm/Support/LEB128.h names, so they can be compiled and proved about.
// Each of these only calls one, which clang inlines, so the code is LLVM's.
#include "llvm/Support/LEB128.h"

using namespace llvm;

extern "C" {
uint64_t decodeuleb128(const uint8_t *p) { return decodeULEB128(p); }
unsigned encodeuleb128(uint64_t Value, uint8_t *p) { return encodeULEB128(Value, p); }
}
