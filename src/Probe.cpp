// ir-lean-probe: a call to every intrinsic the pinned LLVM defines, for tests/ir_features.py to run the
// emitter on, so tests/llvm_scope/ir-features.json's class for each intrinsic is checked against what the
// emitter does.
//
// Each probe is a function that takes the intrinsic's arguments and calls it once. An overloaded intrinsic
// gets up to one probe for each shape of its first overloaded type: integer, vector of integers, scalable
// vector of integers, floating point, vector of floating point, scalable vector of floating point, pointer,
// vector of pointers, and anything else. Every probe passes LLVM's verifier, which checks each intrinsic's
// own rules, such as which arguments have to be constants. An intrinsic no probe can be built for is listed
// on stderr as `unprobed\tNAME\tWHY`.
//
// Probes are named `intrinsic|NAME|SHAPE`, so the emitter's report says which is which.

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/AutoUpgrade.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"

#include <functional>
#include <optional>
#include <string>
#include <vector>

using namespace llvm;
using Intrinsic::IITDescriptor;

namespace {

// How many signatures to try for one shape of one intrinsic before giving up on it.
constexpr unsigned MaxTries = 4000;

enum class Shape {
  Int,
  IntVector,
  IntScalable,
  Float,
  FloatVector,
  FloatScalable,
  Pointer,
  PointerVector,
  Other
};

const char *shapeName(Shape S) {
  switch (S) {
  case Shape::Int:
    return "int";
  case Shape::IntVector:
    return "int vector";
  case Shape::IntScalable:
    return "int scalable vector";
  case Shape::Float:
    return "float";
  case Shape::FloatVector:
    return "float vector";
  case Shape::FloatScalable:
    return "float scalable vector";
  case Shape::Pointer:
    return "pointer";
  case Shape::PointerVector:
    return "pointer vector";
  case Shape::Other:
    return "other";
  }
  return "other";
}

Shape shapeOf(Type *T) {
  Type *E = T->getScalarType();
  bool Scalable = isa<ScalableVectorType>(T);
  bool Vector = T->isVectorTy();
  if (E->isIntegerTy())
    return Scalable ? Shape::IntScalable : Vector ? Shape::IntVector : Shape::Int;
  if (E->isFloatingPointTy())
    return Scalable ? Shape::FloatScalable : Vector ? Shape::FloatVector : Shape::Float;
  if (E->isPointerTy())
    return Vector ? Shape::PointerVector : Shape::Pointer;
  return Shape::Other;
}

// The types tried for an overloaded type, commonest first.
std::vector<Type *> candidates(LLVMContext &C) {
  std::vector<Type *> Out;
  auto Int = [&](unsigned W) { return IntegerType::get(C, W); };
  auto Fixed = [&](Type *E, unsigned N) { return FixedVectorType::get(E, N); };
  auto Scalable = [&](Type *E, unsigned N) { return ScalableVectorType::get(E, N); };
  for (unsigned W : {32, 8, 1, 64, 16, 128})
    Out.push_back(Int(W));
  for (auto [W, N] : std::initializer_list<std::pair<unsigned, unsigned>>{
           {32, 4}, {16, 8},  {8, 16},  {64, 2}, {1, 4},  {32, 8}, {16, 16}, {8, 32},
           {64, 4}, {32, 16}, {16, 32}, {8, 64}, {64, 8}, {1, 8},  {1, 16},  {1, 32},
           {1, 64}, {32, 2},  {8, 8},   {16, 4}, {8, 4},  {1, 2}})
    Out.push_back(Fixed(Int(W), N));
  for (auto [W, N] : std::initializer_list<std::pair<unsigned, unsigned>>{{32, 4},
                                                                          {8, 16},
                                                                          {16, 8},
                                                                          {64, 2},
                                                                          {1, 4},
                                                                          {1, 16},
                                                                          {1, 8},
                                                                          {1, 2},
                                                                          {32, 2},
                                                                          {16, 4},
                                                                          {8, 8},
                                                                          {64, 1}})
    Out.push_back(Scalable(Int(W), N));
  for (Type *F : {Type::getFloatTy(C), Type::getDoubleTy(C), Type::getHalfTy(C), Type::getBFloatTy(C),
                  Type::getFP128Ty(C), Type::getX86_FP80Ty(C), Type::getPPC_FP128Ty(C)})
    Out.push_back(F);
  for (auto [F, N] : std::initializer_list<std::pair<Type *, unsigned>>{{Type::getFloatTy(C), 4},
                                                                        {Type::getDoubleTy(C), 2},
                                                                        {Type::getHalfTy(C), 8},
                                                                        {Type::getBFloatTy(C), 8},
                                                                        {Type::getFloatTy(C), 8},
                                                                        {Type::getDoubleTy(C), 4},
                                                                        {Type::getFloatTy(C), 16},
                                                                        {Type::getDoubleTy(C), 8},
                                                                        {Type::getHalfTy(C), 16},
                                                                        {Type::getHalfTy(C), 32},
                                                                        {Type::getBFloatTy(C), 16},
                                                                        {Type::getBFloatTy(C), 32},
                                                                        {Type::getFloatTy(C), 2},
                                                                        {Type::getHalfTy(C), 4},
                                                                        {Type::getHalfTy(C), 2}})
    Out.push_back(Fixed(F, N));
  for (auto [F, N] : std::initializer_list<std::pair<Type *, unsigned>>{{Type::getFloatTy(C), 4},
                                                                        {Type::getDoubleTy(C), 2},
                                                                        {Type::getHalfTy(C), 8},
                                                                        {Type::getBFloatTy(C), 8},
                                                                        {Type::getFloatTy(C), 2},
                                                                        {Type::getHalfTy(C), 4}})
    Out.push_back(Scalable(F, N));
  for (unsigned AS : {0, 1, 3, 4, 5, 2, 7, 8})
    Out.push_back(PointerType::get(C, AS));
  for (unsigned N : {2, 4, 8, 16})
    Out.push_back(Fixed(PointerType::get(C, 0), N));
  Out.push_back(Scalable(PointerType::get(C, 0), 2));
  Out.push_back(Scalable(PointerType::get(C, 0), 4));
  for (unsigned N : {2, 4, 8, 16})
    Out.push_back(Fixed(PointerType::get(C, 1), N));
  return Out;
}

bool allowedBy(const IITDescriptor &D, Type *T) {
  auto [VC, EC] = D.getOverloadConstraints();
  if (VC == IITDescriptor::VC_Vector && !T->isVectorTy())
    return false;
  if (VC == IITDescriptor::VC_Scalar && T->isVectorTy())
    return false;
  Type *E = T->getScalarType();
  if (EC == IITDescriptor::EC_Integer && !E->isIntegerTy())
    return false;
  if (EC == IITDescriptor::EC_Float && !E->isFloatingPointTy())
    return false;
  if (EC == IITDescriptor::EC_Pointer && !E->isPointerTy())
    return false;
  return true;
}

// LLVM's own decoding, `DecodeFixedType` in lib/IR/Intrinsics.cpp, assumes the overload types fit the table,
// and may crash where they don't. This is the same decoding, giving nullptr instead.
Type *decode(ArrayRef<IITDescriptor> &Infos, ArrayRef<Type *> Tys, LLVMContext &C) {
  if (Infos.empty())
    return nullptr;
  IITDescriptor D = Infos.front();
  Infos = Infos.drop_front();
  auto Overload = [&]() -> Type * {
    unsigned I = D.getOverloadIndex();
    return I < Tys.size() ? Tys[I] : nullptr;
  };
  switch (D.Kind) {
  case IITDescriptor::Void:
    return Type::getVoidTy(C);
  case IITDescriptor::MMX:
    return FixedVectorType::get(IntegerType::get(C, 64), 1);
  case IITDescriptor::AMX:
    return Type::getX86_AMXTy(C);
  case IITDescriptor::Token:
    return Type::getTokenTy(C);
  case IITDescriptor::Metadata:
    return Type::getMetadataTy(C);
  case IITDescriptor::Half:
    return Type::getHalfTy(C);
  case IITDescriptor::BFloat:
    return Type::getBFloatTy(C);
  case IITDescriptor::Float:
    return Type::getFloatTy(C);
  case IITDescriptor::Double:
    return Type::getDoubleTy(C);
  case IITDescriptor::Quad:
    return Type::getFP128Ty(C);
  case IITDescriptor::PPCQuad:
    return Type::getPPC_FP128Ty(C);
  case IITDescriptor::AArch64Svcount:
    return TargetExtType::get(C, "aarch64.svcount");
  case IITDescriptor::WasmExternref:
    return TargetExtType::get(C, "wasm.externref");
  case IITDescriptor::WasmFuncref:
    return TargetExtType::get(C, "wasm.funcref");
  case IITDescriptor::Integer:
    return IntegerType::get(C, D.IntegerWidth);
  case IITDescriptor::Vector: {
    Type *E = decode(Infos, Tys, C);
    if (!E || !VectorType::isValidElementType(E))
      return nullptr;
    return VectorType::get(E, D.VectorWidth);
  }
  case IITDescriptor::Pointer:
    return PointerType::get(C, D.PointerAddressSpace);
  case IITDescriptor::Struct: {
    SmallVector<Type *, 8> Elements;
    for (unsigned I = 0; I != D.StructNumElements; ++I) {
      Type *E = decode(Infos, Tys, C);
      if (!E || !StructType::isValidElementType(E))
        return nullptr;
      Elements.push_back(E);
    }
    return StructType::get(C, Elements);
  }
  case IITDescriptor::Overloaded:
  case IITDescriptor::VecOfAnyPtrsToElt:
  case IITDescriptor::Match:
    return Overload();
  case IITDescriptor::Extend:
  case IITDescriptor::Trunc: {
    Type *T = Overload();
    if (!T || !T->isIntOrIntVectorTy())
      return nullptr;
    unsigned W = T->getScalarSizeInBits();
    if (D.Kind == IITDescriptor::Trunc && (W < 2 || W % 2))
      return nullptr;
    return D.Kind == IITDescriptor::Extend ? T->getExtendedType() : T->getTruncatedType();
  }
  case IITDescriptor::Subdivide2:
  case IITDescriptor::Subdivide4: {
    auto *V = dyn_cast_or_null<VectorType>(Overload());
    bool Two = D.Kind == IITDescriptor::Subdivide2;
    unsigned Parts = Two ? 2 : 4;
    if (!V || !V->getElementType()->isIntegerTy() || V->getScalarSizeInBits() % Parts ||
        V->getScalarSizeInBits() < Parts)
      return nullptr;
    return VectorType::getSubdividedVectorType(V, Two ? 1 : 2);
  }
  case IITDescriptor::OneNthEltsVec: {
    auto *V = dyn_cast_or_null<VectorType>(Overload());
    unsigned N = D.getVectorDivisor();
    if (!V || !N || !V->getElementCount().isKnownMultipleOf(N))
      return nullptr;
    return VectorType::getOneNthElementsVectorType(V, N);
  }
  case IITDescriptor::SameVecWidth: {
    Type *E = decode(Infos, Tys, C);
    Type *T = Overload();
    if (!E || !T)
      return nullptr;
    if (auto *V = dyn_cast<VectorType>(T)) {
      if (!VectorType::isValidElementType(E))
        return nullptr;
      return VectorType::get(E, V->getElementCount());
    }
    return E;
  }
  case IITDescriptor::VecElement: {
    auto *V = dyn_cast_or_null<VectorType>(Overload());
    return V ? V->getElementType() : nullptr;
  }
  case IITDescriptor::VecOfBitcastsToInt: {
    auto *V = dyn_cast_or_null<VectorType>(Overload());
    if (!V || !(V->getElementType()->isIntegerTy() || V->getElementType()->isFloatingPointTy()))
      return nullptr;
    return VectorType::getInteger(V);
  }
  case IITDescriptor::VarArg:
    return nullptr;
  }
  return nullptr;
}

// The intrinsic's type with these overload types, or nullptr if they don't fit it.
FunctionType *typeWith(Intrinsic::ID ID, ArrayRef<Type *> Tys, LLVMContext &C) {
  SmallVector<IITDescriptor, 16> Table;
  auto [Infos, NumArgs, VarArg] = Intrinsic::getIntrinsicInfoTableEntries(ID, Table);
  Type *Ret = decode(Infos, Tys, C);
  if (!Ret)
    return nullptr;
  SmallVector<Type *, 8> Params;
  while (!Infos.empty()) {
    Type *P = decode(Infos, Tys, C);
    if (!P || P->isVoidTy())
      return nullptr;
    Params.push_back(P);
  }
  if (Params.size() != NumArgs)
    return nullptr;
  if (!FunctionType::isValidReturnType(Ret))
    return nullptr;
  for (Type *P : Params)
    if (!FunctionType::isValidArgumentType(P))
      return nullptr;
  FunctionType *FT = FunctionType::get(Ret, Params, VarArg);
  SmallVector<Type *, 4> Matched;
  if (!Intrinsic::isSignatureValid(ID, FT, Matched, nulls()) || ArrayRef<Type *>(Matched) != Tys)
    return nullptr;
  return FT;
}

class Prober {
public:
  Prober(LLVMContext &C, Module &M) : C(C), M(M), Candidates(candidates(C)) {}

  // Builds the probes for one intrinsic. Says why if there are none.
  std::optional<std::string> probe(Intrinsic::ID ID) {
    StringRef Name = Intrinsic::getBaseName(ID);
    Upgraded = false;
    if (!Intrinsic::isOverloaded(ID)) {
      FunctionType *FT = Intrinsic::getType(C, ID);
      if (build(ID, {}, FT, Name, "fixed"))
        return std::nullopt;
      return Upgraded ? UpgradedWhy : "no call to it passes the verifier";
    }
    SmallVector<IITDescriptor, 16> Table;
    auto [Infos, NumArgs, VarArg] = Intrinsic::getIntrinsicInfoTableEntries(ID, Table);
    // The overloaded types, by index, with the descriptor that introduced each, and for a vector of pointers
    // to another's elements, which one.
    std::vector<std::optional<IITDescriptor>> Slots;
    for (const IITDescriptor &D : Infos)
      if (D.Kind == IITDescriptor::Overloaded || D.Kind == IITDescriptor::VecOfAnyPtrsToElt) {
        unsigned I = D.getOverloadIndex();
        if (Slots.size() <= I)
          Slots.resize(I + 1);
        if (!Slots[I])
          Slots[I] = D;
      }
    if (Slots.empty())
      return "it's overloaded, and its table has no overloaded type";
    for (const auto &S : Slots)
      if (!S)
        return "its table leaves an overloaded type undefined";
    unsigned Built = 0;
    for (Shape Want : {Shape::Int, Shape::IntVector, Shape::IntScalable, Shape::Float, Shape::FloatVector,
                       Shape::FloatScalable, Shape::Pointer, Shape::PointerVector, Shape::Other}) {
      std::vector<Type *> Tys(Slots.size(), nullptr);
      unsigned Tries = 0;
      std::function<bool(unsigned)> Assign = [&](unsigned I) -> bool {
        if (I == Slots.size()) {
          if (++Tries > MaxTries)
            return false;
          FunctionType *FT = typeWith(ID, Tys, C);
          return FT && build(ID, Tys, FT, Name, shapeName(Want));
        }
        const IITDescriptor &D = *Slots[I];
        if (D.Kind == IITDescriptor::VecOfAnyPtrsToElt) {
          unsigned Ref = D.getRefOverloadIndex();
          if (Ref >= I || !Tys[Ref] || !Tys[Ref]->isVectorTy())
            return false;
          for (unsigned AS : {0, 1}) {
            Tys[I] = VectorType::get(PointerType::get(C, AS), cast<VectorType>(Tys[Ref])->getElementCount());
            if (Assign(I + 1))
              return true;
          }
          return false;
        }
        for (Type *T : Candidates) {
          if (!allowedBy(D, T) || (I == 0 && shapeOf(T) != Want))
            continue;
          Tys[I] = T;
          if (Assign(I + 1))
            return true;
          if (Tries > MaxTries)
            return false;
        }
        return false;
      };
      Built += Assign(0);
    }
    if (Built)
      return std::nullopt;
    if (Upgraded)
      return UpgradedWhy;
    return "no overload types the generator tries give a call that passes the verifier";
  }

private:
  // A function calling the intrinsic once, kept if it passes the verifier.
  bool build(Intrinsic::ID ID, ArrayRef<Type *> Tys, FunctionType *FT, StringRef Name, StringRef ShapeName) {
    AttributeList Attrs = Intrinsic::getAttributes(C, ID, FT);
    SmallVector<unsigned, 4> Immediates;
    for (unsigned I = 0; I != FT->getNumParams(); ++I)
      if (Attrs.hasParamAttr(I, Attribute::ImmArg))
        Immediates.push_back(I);
    // Every immediate the same value first, then each alone set to another, over the others at zero.
    std::vector<std::vector<int64_t>> Tries;
    for (int64_t V : {0, 1, 2, 3, 4, 8, 16, 7, 15, 31, 255, -1}) {
      Tries.push_back(std::vector<int64_t>(Immediates.size(), V));
      if (Immediates.empty())
        break;
    }
    for (size_t K = 0; K != Immediates.size() && Immediates.size() > 1; ++K)
      for (int64_t V : {1, 2, 3, 4, 8, -1}) {
        std::vector<int64_t> T(Immediates.size(), 0);
        T[K] = V;
        Tries.push_back(T);
      }
    bool HasMetadata = any_of(FT->params(), [](Type *P) { return P->isMetadataTy(); });
    std::vector<const char *> Metas = {"round.dynamic"};
    if (HasMetadata)
      Metas = {"round.dynamic", "fpexcept.strict", "", "tuple"};
    for (const char *Meta : Metas)
      for (bool PoisonArgs : {false, true})
        for (const std::vector<int64_t> &Values : Tries)
          if (attempt(ID, Tys, FT, Name, ShapeName, Immediates, Values, Meta, PoisonArgs))
            return true;
    return false;
  }

  // Whether LLVM's IR reader replaces calls to this declaration with something else, as it does for
  // intrinsics it has retired, so the emitter never sees them. The check renames what it upgrades, so it runs
  // on a copy.
  bool upgradedOnReading(Intrinsic::ID ID, ArrayRef<Type *> Tys) {
    Module Scratch("scratch", C);
    Function *Declaration = Intrinsic::getOrInsertDeclaration(&Scratch, ID, Tys);
    Function *New = nullptr;
    return UpgradeIntrinsicFunction(Declaration, New);
  }

  bool attempt(Intrinsic::ID ID, ArrayRef<Type *> Tys, FunctionType *FT, StringRef Name, StringRef ShapeName,
               ArrayRef<unsigned> Immediates, ArrayRef<int64_t> Values, StringRef Meta, bool PoisonArgs) {
    std::string ProbeName = ("intrinsic|" + Name + "|" + ShapeName).str();
    if (M.getFunction(ProbeName))
      return true;
    if (upgradedOnReading(ID, Tys)) {
      Upgraded = true;
      return false;
    }
    SmallVector<Type *, 8> ArgTypes;
    for (unsigned I = 0; I != FT->getNumParams(); ++I) {
      Type *P = FT->getParamType(I);
      if (!is_contained(Immediates, I) && !PoisonArgs && FunctionType::isValidArgumentType(P) &&
          !P->isMetadataTy() && !P->isTokenTy() && !P->isLabelTy() && !P->isX86_AMXTy())
        ArgTypes.push_back(P);
    }
    Function *Callee = Intrinsic::getOrInsertDeclaration(&M, ID, Tys);
    if (Callee->getFunctionType() != FT)
      return false;
    Function *F = Function::Create(FunctionType::get(Type::getVoidTy(C), ArgTypes, false),
                                   GlobalValue::ExternalLinkage, ProbeName, M);
    IRBuilder<> B(BasicBlock::Create(C, "entry", F));
    SmallVector<Value *, 8> Args;
    unsigned NextArg = 0;
    for (unsigned I = 0; I != FT->getNumParams(); ++I) {
      Type *P = FT->getParamType(I);
      const auto *Imm = find(Immediates, I);
      if (Imm != Immediates.end()) {
        int64_t V = Values[Imm - Immediates.begin()];
        if (P->isIntegerTy())
          Args.push_back(ConstantInt::get(P, V, /*IsSigned=*/true));
        else if (P->isFloatingPointTy())
          Args.push_back(ConstantFP::get(P, double(V)));
        else
          Args.push_back(Constant::getNullValue(P));
      } else if (P->isMetadataTy()) {
        Metadata *MD = Meta == "tuple" ? static_cast<Metadata *>(MDNode::get(C, {MDString::get(C, "")}))
                                       : MDString::get(C, Meta);
        Args.push_back(MetadataAsValue::get(C, MD));
      } else if (P->isTokenTy()) {
        Args.push_back(ConstantTokenNone::get(C));
      } else if (NextArg != ArgTypes.size() && ArgTypes[NextArg] == P && !PoisonArgs && !P->isX86_AMXTy() &&
                 !P->isLabelTy()) {
        Args.push_back(F->getArg(NextArg++));
      } else {
        Args.push_back(PoisonValue::get(P));
      }
    }
    B.CreateCall(Callee, Args);
    B.CreateRetVoid();
    if (!verifyFunction(*F, nullptr))
      return true;
    F->eraseFromParent();
    if (Callee->use_empty())
      Callee->eraseFromParent();
    return false;
  }

  LLVMContext &C;
  Module &M;
  std::vector<Type *> Candidates;
  // Whether a signature tried for the intrinsic being probed is one LLVM's IR reader upgrades.
  bool Upgraded = false;
  const char *UpgradedWhy = "LLVM's IR reader upgrades calls to it to something else";
};

} // namespace

int main(int Argc, char **Argv) {
  std::string Output;
  for (int I = 1; I < Argc; ++I) {
    StringRef A = Argv[I];
    if (A == "-o" && I + 1 < Argc) {
      Output = Argv[++I];
    } else if (A == "-h" || A == "--help") {
      outs()
          << "usage: ir-lean-probe [-o FILE]\n\nPrints a module with a call to every intrinsic LLVM defines, "
             "as described at the top of src/Probe.cpp.\n";
      return 0;
    } else {
      errs() << "ir-lean-probe: unknown argument " << A << "\n";
      return 2;
    }
  }
  LLVMContext C;
  Module M("probes", C);
  // A data layout LLVM's verifier is happy with for every target's intrinsics would need each target's. None
  // is given, which is LLVM's default: little-endian, with 64-bit pointers.
  Prober P(C, M);
  unsigned Probed = 0, Unprobed = 0;
  for (unsigned ID = 1; ID < Intrinsic::num_intrinsics; ++ID) {
    if (std::optional<std::string> Why = P.probe(ID)) {
      errs() << "unprobed\t" << Intrinsic::getBaseName(ID) << "\t" << *Why << "\n";
      ++Unprobed;
    } else {
      ++Probed;
    }
  }
  if (verifyModule(M, &errs())) {
    errs() << "ir-lean-probe: the module doesn't pass LLVM's verifier\n";
    return 1;
  }
  errs() << "ir-lean-probe: " << Probed << " intrinsics probed, " << Unprobed << " not\n";
  if (Output.empty()) {
    M.print(outs(), nullptr);
    return 0;
  }
  std::error_code EC;
  raw_fd_ostream OS(Output, EC, sys::fs::OF_Text);
  if (EC) {
    errs() << "ir-lean-probe: can't write " << Output << ": " << EC.message() << "\n";
    return 1;
  }
  M.print(OS, nullptr);
  return 0;
}
