// CMake generates this for building LLVM, and it isn't installed. This is all CRC.cpp needs of it: LLVM's own
// CRC-32, not zlib's, as in a build without zlib. The installed llvm-config.h says zlib, from however Nix
// built its LLVM.
#undef LLVM_ENABLE_ZLIB
#define LLVM_ENABLE_ZLIB 0
