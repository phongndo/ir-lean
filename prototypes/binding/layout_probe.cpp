// Checks, on objects the pinned libLLVM builds, the layout facts `HeapView.lean` takes as its
// definition of what a `Value *` holds. Each fact is one the compiled `llvm::isKnownNegation` reads:
//
// - the byte at offset 0 of a `Value` is its value ID, and a `sub` instruction's is 46 and a
//   `ConstantInt`'s is 5;
// - a binary operator's operands are the `Value *` at offsets -64 and -32, its two `Use`s;
// - a `ConstantInt` of at most 64 bits has its width as a 32-bit word at offset 32, and its value at
//   offset 24;
// - a `Value`'s type is the pointer at offset 8, and the low byte of the 32-bit word at offset 8 of a
//   `Type` is its type ID, which is 18 or 19 only for a vector.
//
// It reads raw memory, which C++ doesn't define. That's the point: it shows what this build's
// objects hold, on this target, and nothing more. Prints one line per fact and exits 1 if any fails.
//
// Build: clang++ layout_probe.cpp $(llvm-config --cxxflags --ldflags --libs core) -o layout_probe

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

using namespace llvm;

namespace {

int Failures = 0;

void fact(const char *What, bool Holds) {
  std::printf("%s %s\n", Holds ? "ok  " : "FAIL", What);
  Failures += !Holds;
}

template <typename T> T at(const void *P, long Offset) {
  T V;
  std::memcpy(&V, static_cast<const char *>(P) + Offset, sizeof V);
  return V;
}

} // namespace

int main() {
  LLVMContext Ctx;
  Module M("probe", Ctx);
  for (unsigned W : {1u, 8u, 32u, 64u, 128u}) {
    IntegerType *Ty = IntegerType::get(Ctx, W);
    Function *F = Function::Create(FunctionType::get(Ty, {Ty, Ty}, false), Function::ExternalLinkage,
                                   "f" + std::to_string(W), M);
    IRBuilder<> B(BasicBlock::Create(Ctx, "entry", F));
    Value *A = F->getArg(0), *Bv = F->getArg(1);
    // 7 doesn't fit in i1, which `ConstantInt::get` asserts only in a build with assertions: see below.
    uint64_t K = W == 1 ? 1 : 7;
    Constant *Zero = ConstantInt::get(Ty, 0), *Seven = ConstantInt::get(Ty, K);
    // The IRBuilder would fold a constant operand, so the instructions are made directly.
    auto *Neg = BinaryOperator::CreateSub(Zero, A, "neg", B.GetInsertBlock());
    auto *Sub = BinaryOperator::CreateSub(A, Bv, "sub", B.GetInsertBlock());
    auto *Xor = BinaryOperator::CreateXor(A, Bv, "xor", B.GetInsertBlock());
    auto *Add = BinaryOperator::CreateAdd(Sub, Neg, "add", B.GetInsertBlock());
    B.CreateRet(Add);
    std::string Wd = "i" + std::to_string(W) + ": ";

    fact((Wd + "a sub's value ID is 46, the byte at offset 0").c_str(),
         Sub->getValueID() == 46 && at<uint8_t>(Sub, 0) == 46 && at<uint8_t>(Neg, 0) == 46);
    fact((Wd + "Value::InstructionVal + Instruction::Sub is 46").c_str(),
         Value::InstructionVal + Instruction::Sub == 46);
    fact((Wd + "an xor's and an add's value IDs aren't 46").c_str(),
         at<uint8_t>(Xor, 0) != 46 && at<uint8_t>(Add, 0) != 46 && at<uint8_t>(Xor, 0) == Xor->getValueID());
    fact((Wd + "an argument's value ID isn't 46 or 5").c_str(),
         at<uint8_t>(A, 0) == A->getValueID() && at<uint8_t>(A, 0) != 46 && at<uint8_t>(A, 0) != 5);
    fact((Wd + "a ConstantInt's value ID is 5").c_str(), Zero->getValueID() == Value::ConstantIntVal &&
                                                             Value::ConstantIntVal == 5 &&
                                                             at<uint8_t>(Zero, 0) == 5);
    for (Value *P : {static_cast<Value *>(PoisonValue::get(Ty)), static_cast<Value *>(UndefValue::get(Ty))})
      fact((Wd + "poison's and undef's value IDs aren't 46 or 5").c_str(),
           at<uint8_t>(P, 0) == P->getValueID() && at<uint8_t>(P, 0) != 46 && at<uint8_t>(P, 0) != 5);
    fact((Wd + "operand 0 is the Value * at offset -64, and operand 1 at -32").c_str(),
         at<Value *>(Neg, -64) == Zero && at<Value *>(Neg, -32) == A && at<Value *>(Sub, -64) == A &&
             at<Value *>(Sub, -32) == Bv && at<Value *>(Add, -64) == Sub && at<Value *>(Add, -32) == Neg);
    fact((Wd + "a ConstantInt's width is the 32-bit word at offset 32").c_str(),
         at<uint32_t>(Zero, 32) == W && at<uint32_t>(Seven, 32) == W);
    if (W <= 64)
      fact((Wd + "a ConstantInt's value is the 64-bit word at offset 24").c_str(),
           at<uint64_t>(Zero, 24) == 0 && at<uint64_t>(Seven, 24) == K);
    else
      fact((Wd + "past 64 bits, the word at offset 24 points to the value's words").c_str(),
           at<const uint64_t *>(Seven, 24)[0] == 7 && at<const uint64_t *>(Zero, 24)[0] == 0);
    Type *T = at<Type *>(Sub, 8);
    fact((Wd + "a Value's type is the pointer at offset 8").c_str(),
         T == Ty && at<Type *>(Zero, 8) == Ty && at<Type *>(A, 8) == Ty);
    unsigned ID = at<uint32_t>(T, 8) & 0xff;
    fact((Wd + "the low byte at offset 8 of an integer type is its type ID, and masking bit 0 off isn't 18")
             .c_str(),
         ID == Type::IntegerTyID && (ID & 254) != 18);
  }
  // Every vector type's ID, masked as the compiled code masks it, is 18.
  for (Type *V : {static_cast<Type *>(FixedVectorType::get(IntegerType::get(Ctx, 8), 4)),
                  static_cast<Type *>(ScalableVectorType::get(IntegerType::get(Ctx, 8), 4))})
    fact("a vector type's low byte at offset 8, with bit 0 masked off, is 18",
         (at<uint32_t>(V, 8) & 0xff) == V->getTypeID() && (V->getTypeID() & 254) == 18 &&
             Type::FixedVectorTyID == 18 && Type::ScalableVectorTyID == 19);
  // APInt keeps the bits above its width 0, and the compiled code relies on it: `m_ZeroInt` compares the
  // whole word with 0. Nothing in a build without assertions keeps a caller from breaking that: asking for
  // 7 at i1 asserts in a debug build, and here gives a ConstantInt whose word is 7. So a heap where every
  // word is clean is a hypothesis of the theorem, not something this build guarantees.
  auto *Bad = ConstantInt::get(IntegerType::get(Ctx, 1), 7);
  fact("a ConstantInt made against its precondition breaks APInt's invariant in this build",
       at<uint32_t>(Bad, 32) == 1 && at<uint64_t>(Bad, 24) == 7);
  std::printf("%d failed\n", Failures);
  return Failures != 0;
}
