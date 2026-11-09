// Checks IRLean/LLVMHeap.lean against objects the pinned libLLVM builds: the layout it reads, and what each
// constructor it states does to memory. Gate B1 of docs/binding-approach.md. tests/llvm_heap.sh builds this
// with the layout's numbers as -DLAYOUT_* and the opcodes as -DOPCODE_*, which Lean prints from
// IRLean.LLVMHeap, so the probe checks the numbers the proofs use, not a copy of them.
//
// It reads raw memory, which C++ doesn't define. That's the point: it shows what this build's objects hold,
// on this target, and nothing more. It prints one line per fact and exits 1 if any fails.

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <string>
#include <vector>

#ifndef LAYOUT_VALUE_ID
#error "build this with the -DLAYOUT_* flags tests/llvm_heap.sh prints from IRLean.LLVMHeap"
#endif

using namespace llvm;

namespace {

int Failures = 0;

void fact(const std::string &What, bool Holds) {
  std::printf("%s %s\n", Holds ? "ok  " : "FAIL", What.c_str());
  Failures += !Holds;
}

template <typename T> T at(const void *P, long Offset) {
  T V;
  std::memcpy(&V, static_cast<const char *>(P) + Offset, sizeof V);
  return V;
}

const char *base(const void *P) { return static_cast<const char *>(P); }

// The bytes the view reads of a value: its ID, its type, and a ConstantInt's word and width or a binary
// operator's two operands. And of a type, its word at offset 8.
std::vector<unsigned char> reads(const Value *V) {
  std::vector<unsigned char> B;
  auto take = [&](long Off, long N) {
    for (long I = 0; I < N; ++I)
      B.push_back(at<unsigned char>(V, Off + I));
  };
  take(LAYOUT_VALUE_ID, 1);
  take(LAYOUT_VALUE_TYPE, 8);
  if (isa<ConstantInt>(V)) {
    take(LAYOUT_CONST_WORD, 8);
    take(LAYOUT_CONST_WIDTH, 4);
  }
  if (isa<BinaryOperator>(V)) {
    take(-2 * LAYOUT_USE_SIZE + LAYOUT_USE_VAL, 8);
    take(-LAYOUT_USE_SIZE + LAYOUT_USE_VAL, 8);
  }
  return B;
}

std::vector<unsigned char> typeReads(const Type *T) {
  std::vector<unsigned char> B;
  for (long I = 0; I < 4; ++I)
    B.push_back(at<unsigned char>(T, LAYOUT_TYPE_WORD + I));
  return B;
}

// What the view reads of every value and type seen so far, to check a constructor leaves them alone.
struct Snapshot {
  std::map<const Value *, std::vector<unsigned char>> Values;
  std::map<const Type *, std::vector<unsigned char>> Types;
};

Snapshot snap(const std::vector<Value *> &Vs, const std::vector<Type *> &Ts) {
  Snapshot S;
  for (Value *V : Vs)
    S.Values[V] = reads(V);
  for (Type *T : Ts)
    S.Types[T] = typeReads(T);
  return S;
}

bool same(const Snapshot &S) {
  for (auto &[V, B] : S.Values)
    if (reads(V) != B)
      return false;
  for (auto &[T, B] : S.Types)
    if (typeReads(T) != B)
      return false;
  return true;
}

struct Op {
  const char *Name;
  Instruction::BinaryOps Opc;
  unsigned Lean;
};

} // namespace

int main() {
  LLVMContext Ctx;
  Module M("probe", Ctx);
  std::vector<Value *> Seen;
  std::vector<Type *> Types;

  fact("sizeof(Value), sizeof(Use), sizeof(ConstantInt), sizeof(BinaryOperator), sizeof(Type) are the "
       "layout's",
       sizeof(Value) == LAYOUT_VALUE_SIZE && sizeof(Use) == LAYOUT_USE_SIZE &&
           sizeof(ConstantInt) == LAYOUT_CONST_SIZE && sizeof(BinaryOperator) == LAYOUT_BINOP_SIZE &&
           sizeof(Type) == LAYOUT_TYPE_SIZE && sizeof(IntegerType) == LAYOUT_TYPE_SIZE);
  fact("Value::ConstantIntVal, PoisonValueVal and InstructionVal are the layout's",
       Value::ConstantIntVal == LAYOUT_CONSTANT_INT_VAL && Value::PoisonValueVal == LAYOUT_POISON_VALUE_VAL &&
           Value::InstructionVal == LAYOUT_INSTRUCTION_VAL);
  fact("Type::IntegerTyID, FixedVectorTyID and ScalableVectorTyID are the layout's",
       Type::IntegerTyID == LAYOUT_INTEGER_TY_ID && Type::FixedVectorTyID == LAYOUT_FIXED_VECTOR_TY_ID &&
           Type::ScalableVectorTyID == LAYOUT_SCALABLE_VECTOR_TY_ID);
  const Op Ops[] = {{"add", Instruction::Add, OPCODE_ADD},    {"sub", Instruction::Sub, OPCODE_SUB},
                    {"mul", Instruction::Mul, OPCODE_MUL},    {"udiv", Instruction::UDiv, OPCODE_UDIV},
                    {"sdiv", Instruction::SDiv, OPCODE_SDIV}, {"urem", Instruction::URem, OPCODE_UREM},
                    {"srem", Instruction::SRem, OPCODE_SREM}, {"shl", Instruction::Shl, OPCODE_SHL},
                    {"lshr", Instruction::LShr, OPCODE_LSHR}, {"ashr", Instruction::AShr, OPCODE_ASHR},
                    {"and", Instruction::And, OPCODE_AND},    {"or", Instruction::Or, OPCODE_OR},
                    {"xor", Instruction::Xor, OPCODE_XOR}};
  for (const Op &O : Ops)
    fact(std::string("Instruction::") + O.Name + " is BinOp's opcode for it", O.Opc == O.Lean);

  for (unsigned W : {1u, 8u, 32u, 64u}) {
    std::string Wd = "i" + std::to_string(W) + ": ";
    IntegerType *Ty = IntegerType::get(Ctx, W);
    Types.push_back(Ty);
    fact(Wd + "an IntegerType's word at offset 8 is its width above its ID",
         at<uint32_t>(Ty, LAYOUT_TYPE_WORD) == W * 256 + LAYOUT_INTEGER_TY_ID);
    Function *F = Function::Create(FunctionType::get(Ty, {Ty, Ty}, false), Function::ExternalLinkage,
                                   "f" + std::to_string(W), M);
    BasicBlock *BB = BasicBlock::Create(Ctx, "entry", F);
    Value *A = F->getArg(0), *B = F->getArg(1);
    Seen.push_back(A);
    Seen.push_back(B);
    fact(Wd + "an argument's ID is the byte at offset 0, and not a ConstantInt's, poison's or an operator's",
         at<uint8_t>(A, LAYOUT_VALUE_ID) == A->getValueID() && A->getValueID() != LAYOUT_CONSTANT_INT_VAL &&
             A->getValueID() != LAYOUT_POISON_VALUE_VAL &&
             !(A->getValueID() >= LAYOUT_INSTRUCTION_VAL + 14 &&
               A->getValueID() < LAYOUT_INSTRUCTION_VAL + 32));
    fact(Wd + "a value's type is the pointer at offset 8", at<Type *>(A, LAYOUT_VALUE_TYPE) == Ty);

    // ConstantInt::get, within its precondition.
    uint64_t X = W == 1 ? 1 : 7;
    Snapshot S = snap(Seen, Types);
    ConstantInt *C = ConstantInt::get(Ty, X);
    fact(Wd + "ConstantInt::get leaves what the view reads of every value and type alone", same(S));
    fact(Wd + "ConstantInt::get makes ID 5, its type at 8, the word at 24, the width at 32",
         at<uint8_t>(C, LAYOUT_VALUE_ID) == LAYOUT_CONSTANT_INT_VAL &&
             at<Type *>(C, LAYOUT_VALUE_TYPE) == Ty && at<uint64_t>(C, LAYOUT_CONST_WORD) == X &&
             at<uint32_t>(C, LAYOUT_CONST_WIDTH) == W);
    fact(Wd + "ConstantInt::get gives the same object for the same type and word",
         ConstantInt::get(Ty, X) == C);
    ConstantInt *Zero = ConstantInt::get(Ty, 0);
    fact(Wd + "and another for another word", Zero != C && at<uint64_t>(Zero, LAYOUT_CONST_WORD) == 0);
    Seen.push_back(C);
    Seen.push_back(Zero);

    // PoisonValue::get.
    S = snap(Seen, Types);
    PoisonValue *P = PoisonValue::get(Ty);
    fact(Wd + "PoisonValue::get leaves what the view reads alone, and makes ID 1 with its type at 8",
         same(S) && at<uint8_t>(P, LAYOUT_VALUE_ID) == LAYOUT_POISON_VALUE_VAL &&
             at<Type *>(P, LAYOUT_VALUE_TYPE) == Ty && PoisonValue::get(Ty) == P);
    Seen.push_back(P);

    // BinaryOperator::Create, for each operator, with operands that already have uses, so each new Use goes
    // on a list whose first Use it has to write.
    for (const Op &O : Ops) {
      Use *HeadA = A->use_empty() ? nullptr : &*A->use_begin();
      S = snap(Seen, Types);
      BinaryOperator *I = BinaryOperator::Create(O.Opc, A, B, "", BB);
      const char *Obj = base(I);
      const void *Use0 = Obj - 2 * LAYOUT_USE_SIZE, *Use1 = Obj - LAYOUT_USE_SIZE;
      fact(Wd + "BinaryOperator::Create(" + O.Name +
               ") leaves what the view reads of every value and type alone",
           same(S));
      fact(Wd + O.Name + ": the ID is InstructionVal plus its opcode, its type at 8",
           at<uint8_t>(I, LAYOUT_VALUE_ID) == LAYOUT_INSTRUCTION_VAL + O.Lean &&
               at<Type *>(I, LAYOUT_VALUE_TYPE) == Ty);
      fact(Wd + O.Name + ": the operands are the Value * of the Uses 64 and 32 bytes before it",
           at<Value *>(Use0, LAYOUT_USE_VAL) == A && at<Value *>(Use1, LAYOUT_USE_VAL) == B &&
               &I->getOperandUse(0) == Use0 && &I->getOperandUse(1) == Use1);
      fact(Wd + O.Name + ": the first operand's UseList, at offset 16, is the new Use",
           at<const void *>(A, LAYOUT_VALUE_USE_LIST) == Use0);
      fact(Wd + O.Name +
               ": the Use that was first has its Prev, at offset 16, written, and nothing else read",
           HeadA == nullptr || at<const void *>(HeadA, LAYOUT_USE_PREV) == base(Use0) + 8);
      Seen.push_back(I);
    }
  }
  for (Type *V : {static_cast<Type *>(FixedVectorType::get(IntegerType::get(Ctx, 8), 4)),
                  static_cast<Type *>(ScalableVectorType::get(IntegerType::get(Ctx, 8), 4))})
    fact("a vector type's ID is the low byte at offset 8",
         (at<uint32_t>(V, LAYOUT_TYPE_WORD) & 0xff) == V->getTypeID() &&
             (V->getTypeID() == LAYOUT_FIXED_VECTOR_TY_ID || V->getTypeID() == LAYOUT_SCALABLE_VECTOR_TY_ID));

  // APInt's clean words, as #74 found: in a build without assertions, ConstantInt::get against its
  // precondition stores the word as given. And since the context finds constants by their APInt, that dirty
  // `1` at i1 is a different object from the clean one, so two `Value *`s hold what is the same constant to
  // the IR.
  IntegerType *I1 = IntegerType::get(Ctx, 1);
  ConstantInt *Dirty = ConstantInt::get(I1, 7), *One = ConstantInt::get(I1, 1);
  fact("ConstantInt::get(i1, 7) holds the word 7, against APInt's invariant, in this build",
       at<uint32_t>(Dirty, LAYOUT_CONST_WIDTH) == 1 && at<uint64_t>(Dirty, LAYOUT_CONST_WORD) == 7);
  fact("and it's another object than ConstantInt::get(i1, 1)", Dirty != One);
  std::printf("%d failed\n", Failures);
  return Failures != 0;
}
