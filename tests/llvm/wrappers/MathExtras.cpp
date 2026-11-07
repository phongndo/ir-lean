// Gives LLVM's inline functions in llvm/Support/MathExtras.h names, so they can be compiled and proved about.
// Each of these only calls one, which clang inlines, so the code is LLVM's.
#include "llvm/Support/MathExtras.h"

using namespace llvm;

extern "C" {
uint32_t hi32(uint64_t V) { return Hi_32(V); }
uint32_t lo32(uint64_t V) { return Lo_32(V); }
uint64_t make64(uint32_t H, uint32_t L) { return Make_64(H, L); }
bool ismask64(uint64_t V) { return isMask_64(V); }
bool isshiftedmask64(uint64_t V) { return isShiftedMask_64(V); }
bool ispowerof2_64(uint64_t V) { return isPowerOf2_64(V); }
unsigned log2_64(uint64_t V) { return Log2_64(V); }
unsigned log2_64_ceil(uint64_t V) { return Log2_64_Ceil(V); }
uint64_t minalign(uint64_t A, uint64_t B) { return MinAlign(A, B); }
uint64_t nextpowerof2(uint64_t A) { return NextPowerOf2(A); }
uint64_t powerof2ceil(uint64_t A) { return PowerOf2Ceil(A); }
bool isuintn(unsigned N, uint64_t X) { return isUIntN(N, X); }
bool isintn(unsigned N, int64_t X) { return isIntN(N, X); }
uint64_t maxuintn(uint64_t N) { return maxUIntN(N); }
int64_t minintn(int64_t N) { return minIntN(N); }
int64_t maxintn(int64_t N) { return maxIntN(N); }
int64_t signextend64(uint64_t X, unsigned B) { return SignExtend64(X, B); }
uint64_t abs_diff(uint64_t A, uint64_t B) { return AbsoluteDifference(A, B); }
uint64_t saturatingadd(uint64_t A, uint64_t B) { return SaturatingAdd(A, B); }
uint32_t masktrailingones32(unsigned N) { return maskTrailingOnes<uint32_t>(N); }
uint64_t masktrailingones64(unsigned N) { return maskTrailingOnes<uint64_t>(N); }
uint64_t maskleadingones64(unsigned N) { return maskLeadingOnes<uint64_t>(N); }
uint64_t masktrailingzeros64(unsigned N) { return maskTrailingZeros<uint64_t>(N); }
uint64_t maskleadingzeros64(unsigned N) { return maskLeadingZeros<uint64_t>(N); }
uint32_t reversebits32(uint32_t V) { return reverseBits(V); }
uint64_t reversebits64(uint64_t V) { return reverseBits(V); }
}
