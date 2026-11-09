// Each function becomes a type with one constructor per basic block, whose fields are the block's
// phi values and the values it needs from earlier blocks, plus a `step` function that runs one
// block. IRLean.run loops over `step`. Recursive functions can't go through that driver, so their
// blocks call each other directly, in a `mutual` block. Under a promise to progress or to return, a
// run that never finishes is judged by IRLean.promised, as IRLean/Promise.lean says. Anything this
// file can't model exactly is refused, so the semantics stay in Lean and this stays a printer.

#include "Emitter.h"

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cctype>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <vector>

using namespace llvm;

namespace ir_lean {
namespace {

// A Lean type holds at most 244 constructors. Recursive functions can't nest their blocks, so this is their
// limit.
constexpr unsigned MaxRecursiveBlocks = 200;
// Larger functions nest their blocks, since what it costs to check a type grows faster than its constructors
// do.
constexpr unsigned MaxFlatBlocks = 32;
constexpr unsigned BlocksPerGroup = 16;
// A type holds 244 groups of 16, so past a round number under that, groups need to be larger.
constexpr unsigned MaxBlocksInSmallGroups = 3200;
constexpr unsigned BlocksPerLargeGroup = 200;

struct Unsupported {
  std::string Why;
};

[[noreturn]] void reject(const std::string &Why) { throw Unsupported{Why}; }

template <typename T> std::string printed(const T &V) {
  std::string S;
  raw_string_ostream OS(S);
  V.print(OS);
  // Instructions print with leading spaces and any metadata, which only makes reports noisier.
  size_t First = S.find_first_not_of(' ');
  return First == std::string::npos ? S : S.substr(First);
}

std::string printedType(Type *T) {
  std::string S;
  raw_string_ostream OS(S);
  T->print(OS);
  return S;
}

// Names the emitted code relies on, and words Lean reserves, can't be used for anything else.
const std::set<std::string> &reservedNames() {
  static const std::set<std::string> Names = [] {
    std::set<std::string> Reserved = {
        // Every token in Lean's table that looks like an identifier, as tests/names.sh checks, and two
        // more that the table doesn't list.
        "module", "this", "Prop", "Sort", "StateRefT", "Type", "_", "abbrev", "add_decl_doc",
        "assert_not_exists", "assert_not_imported", "at", "attribute", "axiom", "bif", "binder_predicate",
        "break", "builtin_cbv_simproc", "builtin_cbv_simproc_decl", "builtin_dsimproc",
        "builtin_dsimproc_decl", "builtin_grind_propagator", "builtin_initialize", "builtin_simproc",
        "builtin_simproc_decl", "by", "by_elab", "calc", "catch", "cbv_eval", "cbv_simproc",
        "cbv_simproc_decl", "class", "coinductive", "coinductive_fixpoint", "continue", "dbg_trace",
        "declare_bitwise_int_theorems", "declare_bitwise_uint_theorems", "declare_command_config_elab",
        "declare_command_config_elab_legacy", "declare_config_elab", "declare_config_elab_legacy",
        "declare_core_config_elab", "declare_eval_bin", "declare_eval_bin_bitwise",
        "declare_eval_bin_bool_pred", "declare_int_theorems", "declare_simp_like_tactic",
        "declare_sint_simprocs", "declare_syntax_cat", "declare_term_config_elab", "declare_uint_simprocs",
        "declare_uint_theorems", "decreasing_by", "def", "def_eval_config_item", "deprecated_module",
        "deprecated_syntax", "deriving", "do", "docs_to_verso", "dsimproc", "dsimproc_decl", "elab",
        "elab_rules", "elab_stx_quot", "else", "end", "eval_prec", "eval_prio", "example", "exists", "export",
        "extends", "finally", "for", "forall", "from", "fun", "generalizing", "grind_annotated",
        "grind_pattern", "grind_propagator", "have", "haveI", "hiding", "idbg", "if", "import", "in",
        "include", "include_str", "inductive", "inductive_fixpoint", "inferInstanceAs", "infix", "infixl",
        "infixr", "init_grind_norm", "init_quot", "initialize", "instance", "leading_parser", "let", "letI",
        "let_delayed", "let_expr", "let_fun", "let_tmp", "local", "logNamedError", "logNamedErrorAt",
        "logNamedWarning", "logNamedWarningAt", "macro", "macro_rules", "match", "match_expr", "matches",
        "max_prec", "meta", "mod_cast", "monotonicity_by", "mut", "mutual", "namespace", "nat_lit",
        "no_index", "nofun", "nomatch", "noncomputable", "nonrec", "norm_cast_add_elim", "notation", "omit",
        "opaque", "open", "partial", "partial_fixpoint", "postfix", "prefix", "private", "protected",
        "public", "recall", "recommended_spelling", "register_builtin_option", "register_error_explanation",
        "register_grind_attr", "register_label_attr", "register_linter_set", "register_option",
        "register_parser_alias", "register_simp_attr", "register_sym_dsimp", "register_sym_simp",
        "register_sym_simp_attr", "register_tactic_tag", "renaming", "repeat", "reprove", "return", "run_cmd",
        "run_elab", "run_meta", "scoped", "seal", "section", "set_library_suggestions", "set_option", "show",
        "show_panel_widgets", "show_term", "show_term_elab", "simproc", "simproc_decl", "sorry", "structure",
        "suffices", "syntax", "tactic_alt", "tactic_extension", "tactic_name", "tactic_tag", "termination_by",
        "test_extern", "then", "theorem", "throwError", "throwErrorAt", "throwNamedError",
        "throwNamedErrorAt", "trailing_parser", "try", "unif_hint", "universe", "unless", "unlock_limits",
        "unsafe", "unseal", "until", "using", "variable", "where", "while", "with", "with_annotate_term",
        "with_weak_namespace", "without_expected_type",
        // Names emitted code uses.
        "Block", "IRLean", "Next", "Outcome", "Val", "andThen", "assume", "br", "branch", "false", "jump",
        "loop", "none", "noundef", "ret", "run", "select", "some", "step", "sw", "true", "unreachable",
        "HasPoison", "Mem", "Ptr", "PtrVal", "initial", "m", "indirect", "Vec", "Vector", "a", "b", "Unit",
        "Nat", "BitVec", "Array", "promised", "runPromised", "Choice", "Outcomes",
        // Names Lean generates for every inductive type.
        "below", "binductionOn", "brecOn", "casesOn", "ctorElim", "ctorElimType", "ctorIdx", "ibelow",
        "injEq", "noConfusion", "noConfusionType", "rec", "recOn", "sizeOf", "toCtorIdx"};
    // The types that hold a function's nested blocks.
    for (unsigned I = 0; I != 244; ++I)
      Reserved.insert("G" + std::to_string(I));
    return Reserved;
  }();
  return Names;
}

// Hands out valid, unique Lean identifiers.
class NameTable {
public:
  std::string make(StringRef Wanted, const char *Fallback) {
    std::string S;
    for (char C : Wanted)
      S += (std::isalnum(static_cast<unsigned char>(C)) || C == '_') ? C : '_';
    if (S.empty())
      S = Fallback + std::to_string(Used.size());
    if (std::isdigit(static_cast<unsigned char>(S[0])))
      S = Fallback + S;
    while (S.front() == '_' && S.size() > 1 && S[1] == '_')
      S.erase(0, 1);
    if (S == "_")
      S = Fallback;
    std::string Candidate = S;
    for (unsigned N = 1; reservedNames().count(Candidate) || !Used.insert(Candidate).second; ++N)
      Candidate = S + "_" + std::to_string(N);
    return Candidate;
  }

private:
  std::set<std::string> Used;
};

std::string leanType(Type *T) {
  if (auto *I = dyn_cast<IntegerType>(T))
    return "Val " + std::to_string(I->getBitWidth());
  if (auto *P = dyn_cast<PointerType>(T)) {
    if (P->getAddressSpace() != 0)
      reject("type " + printedType(T));
    return "PtrVal";
  }
  if (T->isVoidTy())
    return "Unit";
  if (auto *V = dyn_cast<FixedVectorType>(T)) {
    if (!V->getElementType()->isIntegerTy())
      reject("type " + printedType(T));
    return "(Vec " + std::to_string(V->getNumElements()) + " " +
           std::to_string(V->getElementType()->getIntegerBitWidth()) + ")";
  }
  if (auto *S = dyn_cast<StructType>(T)) {
    if (S->isOpaque() || S->getNumElements() == 0)
      reject("type " + printedType(T));
    std::string Out = "(";
    for (unsigned I = 0, E = S->getNumElements(); I != E; ++I)
      Out += (I ? " × " : "") + leanType(S->getElementType(I));
    return Out + ")";
  }
  reject("type " + printedType(T));
}

bool mentionsPointer(Type *T) {
  if (T->isPointerTy())
    return true;
  if (auto *S = dyn_cast<StructType>(T))
    for (Type *E : S->elements())
      if (mentionsPointer(E))
        return true;
  return false;
}

std::string bitVec(const APInt &V) { return toString(V, 10, false) + "#" + std::to_string(V.getBitWidth()); }

std::string poisonOf(Type *T) {
  if (T->isIntegerTy() || T->isPointerTy())
    return "(none : " + leanType(T) + ")";
  return "(HasPoison.poison : " + leanType(T) + ")";
}

std::string zeroOf(Type *T) {
  if (auto *I = dyn_cast<IntegerType>(T))
    return "(some 0#" + std::to_string(I->getBitWidth()) + ")";
  if (T->isPointerTy())
    return "(some Ptr.null)";
  if (auto *V = dyn_cast<FixedVectorType>(T)) {
    leanType(T);
    return "(Vector.replicate " + std::to_string(V->getNumElements()) + " " + zeroOf(V->getElementType()) +
           ")";
  }
  if (auto *S = dyn_cast<StructType>(T)) {
    std::string Out = "(";
    for (unsigned I = 0, E = S->getNumElements(); I != E; ++I)
      Out += (I ? ", " : "") + zeroOf(S->getElementType(I));
    return Out + ")";
  }
  reject("type " + printedType(T));
}

// Whether this definition is certainly the one a program uses. `weak`, `linkonce` and `common` definitions
// can be replaced at link time, `_odr` ones by another translation of the same source that needn't behave
// the same where that source is undefined, and `available_externally` ones by the real one elsewhere.
// A definition another module can replace when it's loaded, as with the `SemanticInterposition` module flag,
// isn't certainly the one either.
bool hasExactLinkage(const GlobalValue &G) {
  return (G.hasExternalLinkage() || G.hasInternalLinkage() || G.hasPrivateLinkage()) && !G.isInterposable();
}

// A `linkonce_odr` or `weak_odr` definition, as C++ gives inline functions and templates. Its IR is still
// this translation's copy of it, so a theorem about that copy means what any other does. What calls it is
// another matter, since the copy a call runs may be another translation's: `emitCall` refuses those calls.
bool hasODRLinkage(const GlobalValue &G) { return G.hasLinkOnceODRLinkage() || G.hasWeakODRLinkage(); }

// The module-wide things functions refer to: its globals and data layout.
class ModuleContext {
public:
  ModuleContext(Module &M, bool NoCode) : DL(M.getDataLayout()), Def(NoCode ? "noncomputable def " : "def ") {
    NameTable GlobalNames;
    unsigned Block = 1;
    // Every global gets its allocation before any initializer is read, since initializers can point
    // at each other.
    for (const GlobalVariable &G : M.globals()) {
      if (!G.hasInitializer()) {
        Rejected[&G] = "external global @" + G.getName().str();
        continue;
      }
      if (G.isThreadLocal()) {
        Rejected[&G] = "thread-local global @" + G.getName().str();
        continue;
      }
      if (!hasExactLinkage(G) || G.isExternallyInitialized()) {
        Rejected[&G] = "global @" + G.getName().str() + ", whose initial value may not be this one";
        continue;
      }
      Global Info;
      Info.Name = GlobalNames.make("g_" + G.getName().str(), "g");
      GlobalNames.make(Info.Name + "_init", "g");
      Info.Block = Block++;
      Info.Size = DL.getTypeAllocSize(G.getValueType());
      Info.ReadOnly = G.isConstant();
      Globals[&G] = std::move(Info);
    }
    for (const Function &F : M) {
      if (!F.hasAddressTaken())
        continue;
      FunctionAddresses[&F] = {GlobalNames.make("fn_" + F.getName().str(), "fn"), Block++};
      if (!F.isDeclaration())
        ByType[F.getFunctionType()].push_back(&F);
    }
    NextBlock = Block;
    // Rejecting a global rejects whatever points at it, so go until nothing changes.
    bool Changed = true;
    while (Changed) {
      Changed = false;
      for (auto It = Globals.begin(); It != Globals.end();) {
        const GlobalVariable *G = It->first;
        Global &Info = It->second;
        Info.Init.clear();
        Info.Relocs.clear();
        try {
          flatten(G->getInitializer(), Info.Init, Info.Relocs);
          ++It;
        } catch (const Unsupported &U) {
          Rejected[G] = "global @" + G->getName().str() + ": " + U.Why;
          It = Globals.erase(It);
          Changed = true;
        }
      }
    }
    for (auto &G : Globals)
      while (!G.second.Init.empty() && G.second.Init.back() == 0)
        G.second.Init.pop_back();
  }

  const DataLayout &DL;
  // What starts a definition in the output.
  const std::string Def;

  std::string constant(const Constant *C) const {
    if (isa<PoisonValue>(C))
      return poisonOf(C->getType());
    if (isa<UndefValue>(C))
      reject("undef");
    if (auto *I = dyn_cast<ConstantInt>(C))
      return "(some " + bitVec(I->getValue()) + ")";
    if (isa<ConstantPointerNull>(C)) {
      leanType(C->getType());
      return "(some Ptr.null)";
    }
    if (isa<ConstantAggregateZero>(C))
      return zeroOf(C->getType());
    if (auto *V = dyn_cast<FixedVectorType>(C->getType())) {
      leanType(V);
      std::string Out = "#v[";
      for (unsigned I = 0, E = V->getNumElements(); I != E; ++I)
        Out += (I ? ", " : "") + constant(C->getAggregateElement(I));
      return Out + "]";
    }
    if (auto *S = dyn_cast<ConstantStruct>(C)) {
      std::string Out = "(";
      for (unsigned I = 0, E = S->getNumOperands(); I != E; ++I)
        Out += (I ? ", " : "") + constant(S->getOperand(I));
      return Out + ")";
    }
    if (C->getType()->isPointerTy()) {
      APInt Offset(64, 0);
      const Value *Base = C->stripAndAccumulateConstantOffsets(DL, Offset, /*AllowNonInbounds=*/true);
      checkConstantGeps(C, Base);
      if (auto *G = dyn_cast<GlobalVariable>(Base)) {
        const std::string &Name = global(G);
        if (Offset.isZero())
          return "(some " + Name + ")";
        return "(some { " + Name + " with offset := " + bitVec(Offset) + " })";
      }
      if (auto *F = dyn_cast<Function>(Base)) {
        auto It = FunctionAddresses.find(F);
        if (It == FunctionAddresses.end())
          reject("constant " + printed(*C));
        if (Offset.isZero())
          return "(some " + It->second.Name + ")";
        return "(some { " + It->second.Name + " with offset := " + bitVec(Offset) + " })";
      }
    }
    reject("constant " + printed(*C));
  }

  // The functions a call through a pointer of this type could reach, among those in this module.
  const std::vector<const Function *> &candidates(const FunctionType *T) const {
    static const std::vector<const Function *> None;
    auto It = ByType.find(T);
    return It == ByType.end() ? None : It->second;
  }

  const std::string &functionAddress(const Function *F) const { return FunctionAddresses.at(F).Name; }

  // Lean definitions for every global and function address, and the memory holding the globals.
  std::string emitGlobals() const {
    std::string Out;
    std::vector<const Global *> Ordered;
    Ordered.reserve(Globals.size());
    for (const auto &G : Globals)
      Ordered.push_back(&G.second);
    std::sort(Ordered.begin(), Ordered.end(),
              [](const Global *A, const Global *B) { return A->Block < B->Block; });
    std::vector<const FunctionAddress *> Addresses;
    Addresses.reserve(FunctionAddresses.size());
    for (const auto &F : FunctionAddresses)
      Addresses.push_back(&F.second);
    std::sort(Addresses.begin(), Addresses.end(),
              [](const FunctionAddress *A, const FunctionAddress *B) { return A->Block < B->Block; });
    for (const Global *G : Ordered)
      Out += Def + G->Name + " : Ptr := ⟨" + std::to_string(G->Block) + ", 0#64, []⟩\n";
    for (const FunctionAddress *F : Addresses)
      Out += Def + F->Name + " : Ptr := ⟨" + std::to_string(F->Block) + ", 0#64, []⟩\n";
    if (!Ordered.empty() || !Addresses.empty())
      Out += '\n';
    for (const Global *G : Ordered) {
      Out += Def + G->Name + "_init : Array Nat := #[";
      for (size_t I = 0; I != G->Init.size(); ++I)
        Out += (I ? "," : "") + std::to_string(G->Init[I]);
      Out += "]\n";
    }
    if (!Ordered.empty())
      Out += '\n';
    Out += "/-- Memory holding this module's globals. -/\n" + Def +
           "initial (base : Nat → BitVec 64 := Mem.spacedOut) : Mem :=\n  Mem.empty base";
    for (const Global *G : Ordered)
      Out += "\n  |>.addGlobal " + std::to_string(G->Block) + " " + std::to_string(G->Size) + " " +
             (G->ReadOnly ? "true" : "false") + " " + G->Name + "_init";
    for (const Global *G : Ordered)
      for (const Reloc &R : G->Relocs)
        Out += "\n  |>.addReloc " + std::to_string(G->Block) + " " + std::to_string(R.Offset) + " ⟨" +
               std::to_string(R.Block) + ", " + bitVec(R.Addend) + ", []⟩";
    Out += "\n  |>.reserve " + std::to_string(NextBlock);
    return Out + "\n\n";
  }

private:
  // A pointer in a global's initial contents.
  struct Reloc {
    uint64_t Offset;
    unsigned Block;
    APInt Addend;
  };
  struct Global {
    std::string Name;
    unsigned Block = 0;
    uint64_t Size = 0;
    bool ReadOnly = false;
    std::vector<unsigned> Init;
    std::vector<Reloc> Relocs;
  };
  struct FunctionAddress {
    std::string Name;
    unsigned Block = 0;
  };

  const std::string &global(const GlobalVariable *G) const {
    auto It = Globals.find(G);
    if (It != Globals.end())
      return It->second.Name;
    auto R = Rejected.find(G);
    reject(R != Rejected.end() ? R->second : "global @" + G->getName().str());
  }

  // A constant pointer is printed as its base and a total offset, which leaves out the rules that a
  // `getelementptr` constant's flags add. That's only right if those rules can't fail: every flagged step
  // has to stay inside `Base`, which also keeps its address from wrapping in any layout LLVM allows. So
  // this refuses anything else, and `inrange`, which says what later accesses may do.
  void checkConstantGeps(const Constant *C, const Value *Base) const {
    std::vector<const GEPOperator *> Geps;
    const Value *V = C;
    while (V != Base) {
      if (auto *G = dyn_cast<GEPOperator>(V)) {
        Geps.push_back(G);
        V = G->getPointerOperand();
      } else if (auto *A = dyn_cast<GlobalAlias>(V)) {
        V = A->getAliasee();
      } else if (auto *O = dyn_cast<Operator>(V)) {
        V = O->getOperand(0);
      } else {
        reject("constant " + printed(*C));
      }
    }
    const auto *G = dyn_cast<GlobalVariable>(Base);
    uint64_t Size = G && Globals.count(G) ? Globals.at(G).Size : 0;
    APInt At(64, 0);
    for (auto It = Geps.rbegin(); It != Geps.rend(); ++It) {
      const GEPOperator &Gep = **It;
      GEPNoWrapFlags Flags = Gep.getNoWrapFlags();
      if (Gep.getInRange())
        reject("constant " + printed(*C));
      bool Checked = Flags != GEPNoWrapFlags::none() && !Gep.hasAllZeroIndices();
      auto Inside = [&] { return !At.isNegative() && At.ule(Size); };
      if (Checked && !Inside())
        reject("constant " + printed(*C) + " with flags that don't plainly hold");
      for (auto I = gep_type_begin(Gep), E = gep_type_end(Gep); I != E; ++I) {
        const auto *Index = dyn_cast<ConstantInt>(I.getOperand());
        if (!Index || Index->getBitWidth() > 64)
          reject("constant " + printed(*C));
        APInt Step(64, 0);
        bool Overflow = false;
        if (StructType *S = I.getStructTypeOrNull())
          Step = APInt(64, DL.getStructLayout(S)->getElementOffset(Index->getZExtValue()));
        else
          Step = Index->getValue().sextOrTrunc(64).smul_ov(APInt(64, I.getSequentialElementStride(DL)),
                                                           Overflow);
        At += Step;
        if (Checked && (Overflow || !Inside() || (Flags.hasNoUnsignedWrap() && Step.isNegative())))
          reject("constant " + printed(*C) + " with flags that don't plainly hold");
      }
    }
  }

  // Appends a constant's bytes, little-endian. 256 stands for an uninitialized byte.
  void flatten(const Constant *C, std::vector<unsigned> &Out, std::vector<Reloc> &Relocs) const {
    if (!DL.isLittleEndian())
      reject("big-endian data");
    Type *T = C->getType();
    uint64_t Size = DL.getTypeAllocSize(T);
    if (isa<UndefValue>(C)) {
      Out.insert(Out.end(), Size, 256);
      return;
    }
    if (C->isNullValue()) {
      Out.insert(Out.end(), Size, 0);
      return;
    }
    if (T->isPointerTy()) {
      APInt Offset(64, 0);
      const Value *Base = C->stripAndAccumulateConstantOffsets(DL, Offset, /*AllowNonInbounds=*/true);
      checkConstantGeps(C, Base);
      unsigned Block = 0;
      if (auto *G = dyn_cast<GlobalVariable>(Base)) {
        global(G);
        Block = Globals.at(G).Block;
      } else if (auto *F = dyn_cast<Function>(Base)) {
        auto It = FunctionAddresses.find(F);
        if (It != FunctionAddresses.end())
          Block = It->second.Block;
      }
      if (!Block)
        reject("initializer " + printed(*C));
      Relocs.push_back({Out.size(), Block, Offset});
      Out.insert(Out.end(), Size, 0);
      return;
    }
    if (auto *I = dyn_cast<ConstantInt>(C)) {
      appendInt(I->getValue(), Size, Out);
      return;
    }
    if (auto *D = dyn_cast<ConstantDataSequential>(C)) {
      if (!D->getElementType()->isIntegerTy())
        reject("constant " + printed(*C));
      for (unsigned I = 0, E = D->getNumElements(); I != E; ++I)
        appendInt(D->getElementAsAPInt(I), DL.getTypeAllocSize(D->getElementType()), Out);
      return;
    }
    if (isa<ConstantArray>(C)) {
      for (const Use &U : C->operands())
        flatten(cast<Constant>(U.get()), Out, Relocs);
      return;
    }
    if (auto *S = dyn_cast<ConstantStruct>(C)) {
      const StructLayout *L = DL.getStructLayout(S->getType());
      size_t Start = Out.size();
      for (unsigned I = 0, E = S->getNumOperands(); I != E; ++I) {
        Out.resize(Start + L->getElementOffset(I), 256);
        flatten(S->getOperand(I), Out, Relocs);
      }
      Out.resize(Start + Size, 256);
      return;
    }
    reject("initializer " + printed(*C));
  }

  static void appendInt(const APInt &V, uint64_t Size, std::vector<unsigned> &Out) {
    for (uint64_t I = 0; I != Size; ++I)
      Out.push_back(8 * I < V.getBitWidth()
                        ? V.extractBitsAsZExtValue(std::min<unsigned>(8, V.getBitWidth() - 8 * I), 8 * I)
                        : 0);
  }

  std::map<const GlobalVariable *, Global> Globals;
  std::map<const GlobalVariable *, std::string> Rejected;
  std::map<const Function *, FunctionAddress> FunctionAddresses;
  std::map<const FunctionType *, std::vector<const Function *>> ByType;
  unsigned NextBlock = 1;
};

const char *libraryFunction(const Function &F);

// Whether loop metadata carries `llvm.loop.mustprogress`, read as LLVM's `findOptionMDForLoopID` does.
bool marksMustProgress(const MDNode *LoopID) {
  if (!LoopID)
    return false;
  for (unsigned I = 1, E = LoopID->getNumOperands(); I < E; ++I) {
    const auto *Option = dyn_cast<MDNode>(LoopID->getOperand(I));
    if (!Option || Option->getNumOperands() == 0)
      continue;
    const auto *Name = dyn_cast<MDString>(Option->getOperand(0));
    if (Name && Name->getString() == "llvm.loop.mustprogress")
      return true;
  }
  return false;
}

// Whether a function, or a loop in it, promises to progress.
bool promisesProgress(const Function &F) {
  if (F.mustProgress())
    return true;
  for (const BasicBlock &BB : F)
    if (const Instruction *T = BB.getTerminator();
        T && marksMustProgress(T->getMetadata(LLVMContext::MD_loop)))
      return true;
  return false;
}

enum class Position { Parameter, Return, CallParameter, CallReturn };

// Attributes on a parameter or return value. These either change what the value means, and are emitted as
// checks below, or are promises `Mem` checks on the function's own parameters. Promises at a call, and the
// rest, are refused: zlib doesn't use them, and the model has no rule for them yet.
void checkValueAttributes(AttributeSet Attrs, const Type *T, Position At, bool MallocResult = false) {
  const char *Where = At == Position::Parameter       ? "parameter"
                      : At == Position::Return        ? "return"
                      : At == Position::CallParameter ? "call parameter"
                                                      : "call return";
  for (Attribute A : Attrs) {
    if (A.isStringAttribute())
      continue;
    switch (A.getKindAsEnum()) {
    case Attribute::NoUndef:
    case Attribute::Range:
    case Attribute::NonNull:
    case Attribute::Alignment:
    case Attribute::Dereferenceable:
      // The checks these emit only take one value, not a vector's lanes.
      if (T->isVectorTy())
        reject(std::string(Where) + " attribute " + A.getAsString() + " on a vector");
      continue;
    // These only describe how a target passes the value, not what it is.
    case Attribute::SExt:
    case Attribute::ZExt:
      continue;
    case Attribute::ReadOnly:
    case Attribute::WriteOnly:
    case Attribute::ReadNone:
    case Attribute::NoFree:
    case Attribute::Initializes:
      if (At != Position::Parameter)
        reject(std::string(Where) + " attribute " + A.getAsString());
      continue;
    // Provenance has a rule about a run, which `Mem` checks. Whether an address is captured depends on what
    // a run with another address would have done, so the model stops at any look at one:
    // `Mem.observeAddress`.
    case Attribute::Captures: {
      CaptureInfo Info = A.getCaptureInfo();
      if (At != Position::Parameter || Info.getRetComponents() != Info.getOtherComponents())
        reject(std::string(Where) + " attribute " + A.getAsString());
      continue;
    }
    // Checked against the result.
    case Attribute::Returned:
      if (At != Position::Parameter || !(T->isPointerTy() || T->isIntegerTy()))
        reject(std::string(Where) + " attribute " + A.getAsString());
      continue;
    case Attribute::NoAlias:
      if (At != Position::Return && !MallocResult)
        reject(std::string(Where) + " attribute " + A.getAsString());
      continue;
    default:
      reject(std::string(Where) + " attribute " + A.getAsString());
    }
  }
}

// What `memory(...)` allows for a kind of memory.
const char *leanAccess(ModRefInfo Info) {
  switch (Info) {
  case ModRefInfo::NoModRef:
    return ".none";
  case ModRefInfo::Ref:
    return ".read";
  case ModRefInfo::Mod:
    return ".write";
  case ModRefInfo::ModRef:
    return ".readwrite";
  }
  reject("memory effects");
}

// The promises a pointer parameter makes, as a `Tag`.
std::string leanTag(AttributeSet Attrs) {
  std::string Out = "{ call := call'";
  auto Set = [&](bool On, const char *Field) {
    if (On)
      Out += std::string(", ") + Field + " := true";
  };
  Set(Attrs.hasAttribute(Attribute::ReadOnly), "readonly");
  Set(Attrs.hasAttribute(Attribute::ReadNone), "readnone");
  Set(Attrs.hasAttribute(Attribute::WriteOnly), "writeonly");
  Set(Attrs.hasAttribute(Attribute::Initializes), "initializes");
  Set(Attrs.hasAttribute(Attribute::NoFree), "nofree");
  if (Attrs.hasAttribute(Attribute::Captures)) {
    CaptureInfo Info = Attrs.getCaptureInfo();
    Set(!capturesAnyProvenance(Info.getOtherComponents()), "expires");
    Set(capturesReadProvenanceOnly(Info.getOtherComponents()), "readAfter");
    Set(!capturesAddress(Info.getOtherComponents()) || capturesAddressIsNullOnly(Info.getOtherComponents()),
        "noAddress");
    Set(capturesAddressIsNullOnly(Info.getOtherComponents()), "nullCheck");
  }
  return Out + " }";
}

// Attributes on a function or a call. Each one here has been reviewed, and anything else is refused, so a
// new attribute can't pass unnoticed.
// `Library` is for the C library functions `Mem` defines, and `GivesUp` for a call to a function outside the
// module that never returns, which stops the model.
void checkFunctionAttributes(AttributeSet Attrs, const std::string &Where, bool Library = false,
                             bool GivesUp = false) {
  for (Attribute A : Attrs) {
    if (A.isStringAttribute()) {
      // Settings for the backend, and which allocator a C library function belongs to.
      static const std::set<std::string> Allowed = {
          "alloc-family",     "frame-pointer", "min-legal-vector-width",      "no-builtins",
          "no-trapping-math", "probe-stack",   "stack-protector-buffer-size", "target-cpu",
          "target-features",  "tune-cpu",      "zero-call-used-regs"};
      if (!Allowed.count(A.getKindAsString().str()))
        reject(Where + " attribute " + A.getAsString());
      continue;
    }
    // `Mem`'s versions of the C library don't call back into the program.
    if (Library && A.getKindAsEnum() == Attribute::NoCallback)
      continue;
    if (GivesUp && A.getKindAsEnum() == Attribute::NoReturn)
      continue;
    switch (A.getKindAsEnum()) {
    // These only change how the code is optimized or lowered.
    case Attribute::AlwaysInline:
    case Attribute::Cold:
    case Attribute::Hot:
    case Attribute::InlineHint:
    case Attribute::MinSize:
    case Attribute::NoInline:
    case Attribute::NoMerge:
    // Only says the callee isn't to be treated as a library function. `emitCall` refuses it on one that is.
    case Attribute::NoBuiltin:
    case Attribute::NoRedZone:
    case Attribute::OptimizeForSize:
    case Attribute::OptimizeNone:
    case Attribute::StackProtect:
    case Attribute::StackProtectReq:
    case Attribute::StackProtectStrong:
    case Attribute::UWTable:
    // The model has no threads and no exceptions, so these always hold.
    case Attribute::NoSync:
    case Attribute::NoUnwind:
    // Promises about the function's behavior, as for the value attributes above, listed in docs/trust.md.
    case Attribute::Memory:
    case Attribute::NoFree:
    case Attribute::NoRecurse:
    // Promises to progress and to return. A run that breaks one is undefined, as
    // `FunctionEmitter::findPromises` and IRLean/Promise.lean say. At a call they're refused, in `emitCall`.
    case Attribute::MustProgress:
    case Attribute::WillReturn:
      continue;
    // What makes `malloc` and `free` the functions `Mem` defines, and nothing else: on anything but those,
    // they'd be promises the model doesn't check.
    case Attribute::AllocKind:
    case Attribute::AllocSize:
      if (!Library)
        reject(Where + " attribute " + A.getAsString());
      continue;
    default:
      reject(Where + " attribute " + A.getAsString());
    }
  }
}

// Wraps `Value` in what `range`, `nonnull` and `align` attributes imply.
std::string withValueChecks(AttributeSet Attrs, const std::string &Value) {
  std::string Out = Value;
  if (Attrs.hasAttribute(Attribute::Range)) {
    const ConstantRange &R = Attrs.getAttribute(Attribute::Range).getValueAsConstantRange();
    Out = "(Val.range " + bitVec(R.getLower()) + " " + bitVec(R.getUpper()) + " " + Out + ")";
  }
  if (Attrs.hasAttribute(Attribute::NonNull))
    Out = "(Mem.nonnull m " + Out + ")";
  if (MaybeAlign A = Attrs.getAlignment())
    Out = "(Mem.aligned m " + std::to_string(A->value()) + " " + Out + ")";
  return Out;
}

bool hasValueChecks(AttributeSet Attrs) {
  return Attrs.hasAttribute(Attribute::Range) || Attrs.hasAttribute(Attribute::NonNull) ||
         Attrs.hasAttribute(Attribute::Alignment);
}

// One line of a block's body.
struct Line {
  enum Kind {
    Let,   // let Name := Expr
    Bind,  // andThen (Expr) fun Name =>
    Guard, // Expr <|
  } K;
  std::string Name;
  std::string Expr;
};

class FunctionEmitter {
public:
  // `PromisedCycle` is for a recursive function in a cycle where some function or loop promises to progress.
  // `Chooses` is for a function whose run can make a choice: one with a `freeze`, or a call to such a
  // function.
  FunctionEmitter(Function &F, std::string LeanName, bool Recursive, bool PromisedCycle, bool UsesMemory,
                  bool Chooses, const DenseMap<const Function *, std::string> &Callees,
                  const std::set<const Function *> &MemoryFunctions,
                  const std::set<const Function *> &ChoosingFunctions,
                  const std::set<const Function *> &ReachesFree, const ModuleContext &Context)
      : F(F), LeanName(std::move(LeanName)), Recursive(Recursive), PromisedCycle(PromisedCycle),
        UsesMemory(UsesMemory), Chooses(Chooses), Callees(Callees), MemoryFunctions(MemoryFunctions),
        ChoosingFunctions(ChoosingFunctions), ReachesFree(ReachesFree), Context(Context) {}

  // Checks the function can be translated, and sets up names and liveness.
  void prepare();
  // The function's namespace: its block type, and `step` unless the function is recursive.
  std::string emitBlocks();
  // For recursive functions: the blocks calling each other, for a `mutual` block.
  std::string emitLoop();
  // The function itself, or in a promised cycle, the raw function members call, inside the `mutual` block.
  std::string emitFunction();
  // In a promised cycle: the function callers outside the cycle see, after the `mutual` block.
  std::string emitPromisedCycleWrapper();
  unsigned blockCount() const { return Blocks.size(); }
  unsigned instructionCount() const { return Instructions; }

private:
  void collectBlocks();
  void nameValues();
  void computeLiveness();
  void findPromises();
  std::string promisedRun(const std::string &Entry);
  std::string promisedCall(const Function *Callee, const std::string &Call);
  std::string signature(const std::string &Name);

  std::string operand(const Value *V);
  std::string flag(bool On, const char *Name) { return On ? std::string(" (") + Name + " := true)" : ""; }
  std::string callArgument(const CallBase &C, unsigned N, std::vector<Line> &Out,
                           bool WithDeclaration = false);
  void checkCallResult(const CallBase &C, std::vector<Line> &Out);
  std::string target(const BasicBlock *From, const BasicBlock *To);
  std::string goTo(const BasicBlock *From, const BasicBlock *To);
  unsigned blocksPerGroup() const {
    return Blocks.size() > MaxBlocksInSmallGroups ? BlocksPerLargeGroup : BlocksPerGroup;
  }
  std::string constructorPath(const BasicBlock *BB, const std::string &Inner);
  std::string emitConstructor(const BasicBlock *BB);
  std::string emitArm(const BasicBlock *BB);
  std::string emitTerminator(const BasicBlock *BB);
  void emitInstruction(const Instruction &I, std::vector<Line> &Out);
  void emitLoad(const LoadInst &L, std::vector<Line> &Out);
  void emitStore(const StoreInst &S, std::vector<Line> &Out);
  void emitGep(const GetElementPtrInst &G, std::vector<Line> &Out);
  void emitAlloca(const AllocaInst &A, std::vector<Line> &Out);
  void checkMetadata(const Instruction &I);
  std::string pointerAsInt(const Value *V);
  void observeAddress(const Value *V, bool NullCheck, std::vector<Line> &Out);
  std::string resultType() const { return UsesMemory ? RetType + " × Mem" : RetType; }
  // The block's next chooser, as `IRLean.Choice` numbers them: a `freeze`, or a call to a function that
  // chooses.
  std::string nextChooser() { return std::to_string(NextChooser++); }
  void emitCall(const CallBase &C, std::vector<Line> &Out);
  bool emitIntrinsic(const IntrinsicInst &C, std::vector<Line> &Out);
  void addLet(const Instruction &I, std::vector<Line> &Out, std::string Expr) {
    Out.push_back({Line::Let, Names.at(&I), std::move(Expr)});
  }
  void addBind(const Instruction &I, std::vector<Line> &Out, std::string Expr) {
    Out.push_back({Line::Bind, I.getType()->isVoidTy() ? "_" : Names.at(&I), std::move(Expr)});
  }
  // A step that changes memory: later instructions see the new memory, under the same name.
  void addMemoryUpdate(std::vector<Line> &Out, std::string Expr) {
    Out.push_back({Line::Bind, "m", std::move(Expr)});
  }

  std::vector<const Value *> blockParams(const BasicBlock *BB) const;

  Function &F;
  std::string LeanName;
  bool Recursive;
  bool PromisedCycle;
  bool UsesMemory;
  bool Chooses;
  // Choosers in the block being emitted are numbered from 1. `c'.sub 0` is the next block's.
  unsigned NextChooser = 1;
  // Blocks under a promise to progress: every block of a function marked `mustprogress` or `willreturn`, and
  // the blocks of each loop marked `llvm.loop.mustprogress` otherwise.
  std::set<const BasicBlock *> Promised;
  // The block being emitted.
  const BasicBlock *Current = nullptr;
  bool HasAlloca = false;
  bool HasCall = false;
  const DenseMap<const Function *, std::string> &Callees;
  const std::set<const Function *> &MemoryFunctions;
  const std::set<const Function *> &ChoosingFunctions;
  const std::set<const Function *> &ReachesFree;
  const ModuleContext &Context;
  std::string RetType;

  std::vector<const BasicBlock *> Blocks;
  DenseMap<const BasicBlock *, unsigned> BlockIndex;
  DenseMap<const BasicBlock *, std::string> BlockNames;
  DenseMap<const Value *, unsigned> ValueIndex;
  std::vector<const Value *> Values;
  std::map<const Value *, std::string> Names;
  std::vector<BitVector> LiveIn;
  unsigned Instructions = 0;
};

void FunctionEmitter::collectBlocks() {
  std::set<const BasicBlock *> Reachable;
  for (const BasicBlock *BB : depth_first(&F.getEntryBlock()))
    Reachable.insert(BB);
  // Function order keeps emitted code in the order someone reading the IR expects.
  for (const BasicBlock &BB : F)
    if (Reachable.count(&BB)) {
      BlockIndex[&BB] = Blocks.size();
      Blocks.push_back(&BB);
    }
}

void FunctionEmitter::nameValues() {
  NameTable ValueNames, BlockTable;
  // Group constructors are named g0, g1, ... so block names mustn't collide with them.
  for (unsigned I = 0, E = Blocks.size() / blocksPerGroup() + 1; I != E; ++I)
    BlockTable.make("g" + std::to_string(I), "g");
  auto Add = [&](const Value *V, const char *Fallback) {
    ValueIndex[V] = Values.size();
    Values.push_back(V);
    Names[V] = ValueNames.make(V->getName(), Fallback);
  };
  for (const Argument &A : F.args())
    Add(&A, "a");
  for (const BasicBlock *BB : Blocks) {
    BlockNames[BB] = BlockTable.make(BB->getName(), "bb");
    for (const Instruction &I : *BB) {
      ++Instructions;
      if (!I.getType()->isVoidTy())
        Add(&I, "v");
    }
  }
}

// Standard backward liveness. A phi's operands count as used at the end of the matching
// predecessor, and a phi itself arrives as a field of its block.
void FunctionEmitter::computeLiveness() {
  unsigned N = Values.size();
  LiveIn.assign(Blocks.size(), BitVector(N));
  std::vector<BitVector> Gen(Blocks.size(), BitVector(N)), Kill(Blocks.size(), BitVector(N));
  auto IsTracked = [&](const Value *V) { return isa<Instruction>(V) || isa<Argument>(V); };
  for (unsigned B = 0; B != Blocks.size(); ++B)
    for (const Instruction &I : *Blocks[B]) {
      if (!isa<PHINode>(I))
        for (const Use &U : I.operands())
          if (IsTracked(U.get()) && !Kill[B].test(ValueIndex.lookup(U.get())))
            Gen[B].set(ValueIndex.lookup(U.get()));
      // A `returned` argument is checked against the result.
      if (isa<ReturnInst>(I))
        for (const Argument &A : F.args())
          if (A.hasReturnedAttr())
            Gen[B].set(ValueIndex.lookup(&A));
      if (!I.getType()->isVoidTy())
        Kill[B].set(ValueIndex.lookup(&I));
    }
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (unsigned B = Blocks.size(); B-- != 0;) {
      BitVector Out(N);
      for (const BasicBlock *S : successors(Blocks[B])) {
        BitVector FromSucc = LiveIn[BlockIndex.lookup(S)];
        for (const PHINode &P : S->phis()) {
          FromSucc.reset(ValueIndex.lookup(&P));
          const Value *In = P.getIncomingValueForBlock(Blocks[B]);
          if (IsTracked(In))
            FromSucc.set(ValueIndex.lookup(In));
        }
        Out |= FromSucc;
      }
      Out.reset(Kill[B]);
      Out |= Gen[B];
      if (Out != LiveIn[B]) {
        LiveIn[B] = std::move(Out);
        Changed = true;
      }
    }
  }
}

// Which blocks are under a promise to progress. A run of the function that stays among them for good, as
// `IRLean.stay` says, is undefined, which LangRef says of a loop marked `llvm.loop.mustprogress` that never
// terminates. Staying among the blocks of all such loops is the same as staying in one of them as long as
// every cycle through those blocks lies inside one such loop, which only irreducible control flow can break,
// so a function where one doesn't is refused.
//
// LangRef puts loop metadata on the branch in a loop's latch, and LLVM's `Loop::getLoopID` reads it only
// there, and only when every latch of the loop carries the same node. Passes copy it elsewhere, onto a split
// exit edge or a rotated loop's header, and there it describes no loop, so it's ignored. Where LangRef
// doesn't settle what it means, it's refused: on one of a loop's latches when they don't all carry it, and
// anywhere off a latch in a function with irreducible control flow, whose cycles aren't loops and have no
// latch to tell it from.
void FunctionEmitter::findPromises() {
  if (F.mustProgress()) {
    Promised.insert(Blocks.begin(), Blocks.end());
    return;
  }
  // A recursive function's runs are judged by the cycle it's in, in `emitPromisedCycleWrapper`.
  if (Recursive)
    return;
  DominatorTree DT(F);
  LoopInfo LI(DT);
  for (const Loop *L : LI.getLoopsInPreorder())
    if (marksMustProgress(L->getLoopID()))
      Promised.insert(L->block_begin(), L->block_end());
  SmallVector<std::pair<const BasicBlock *, const BasicBlock *>, 16> Retreating;
  FindFunctionBackedges(F, Retreating);
  bool Irreducible = any_of(Retreating, [&](const auto &E) { return !DT.dominates(E.second, E.first); });
  for (const BasicBlock *BB : Blocks) {
    const MDNode *ID = BB->getTerminator()->getMetadata(LLVMContext::MD_loop);
    if (!marksMustProgress(ID))
      continue;
    bool Latch = false;
    for (const Loop *L = LI.getLoopFor(BB); L; L = L->getParentLoop()) {
      if (!L->isLoopLatch(BB))
        continue;
      Latch = true;
      if (L->getLoopID() != ID)
        reject("llvm.loop.mustprogress on " + printed(*BB->getTerminator()) +
               ", a latch of a loop whose latches don't all carry it");
    }
    if (!Latch && Irreducible)
      reject("llvm.loop.mustprogress on " + printed(*BB->getTerminator()) +
             ", off a loop's latch, in a function with irreducible control flow");
  }
  // Tarjan's algorithm over the promised blocks, with the edges between them.
  std::vector<const BasicBlock *> Nodes;
  for (const BasicBlock *BB : Blocks)
    if (Promised.count(BB))
      Nodes.push_back(BB);
  std::map<const BasicBlock *, unsigned> Index, LowLink;
  std::vector<const BasicBlock *> Stack;
  std::set<const BasicBlock *> OnStack;
  std::function<void(const BasicBlock *)> Visit = [&](const BasicBlock *BB) {
    unsigned Mine = Index.size();
    Index[BB] = LowLink[BB] = Mine;
    Stack.push_back(BB);
    OnStack.insert(BB);
    bool SelfLoop = false;
    for (const BasicBlock *S : successors(BB)) {
      if (!Promised.count(S))
        continue;
      SelfLoop |= S == BB;
      if (!Index.count(S)) {
        Visit(S);
        LowLink[BB] = std::min(LowLink[BB], LowLink[S]);
      } else if (OnStack.count(S)) {
        LowLink[BB] = std::min(LowLink[BB], Index[S]);
      }
    }
    if (LowLink[BB] != Mine)
      return;
    std::vector<const BasicBlock *> Component;
    const BasicBlock *Member;
    do {
      Member = Stack.back();
      Stack.pop_back();
      OnStack.erase(Member);
      Component.push_back(Member);
    } while (Member != BB);
    if (Component.size() == 1 && !SelfLoop)
      return;
    for (const Loop *L = LI.getLoopFor(BB); L; L = L->getParentLoop())
      if (marksMustProgress(L->getLoopID()) &&
          all_of(Component, [&](const BasicBlock *X) { return L->contains(X); }))
        return;
    reject("a cycle through loops marked llvm.loop.mustprogress that leaves each of them, at block " +
           BlockNames.lookup(BB));
  };
  for (const BasicBlock *BB : Nodes)
    if (!Index.count(BB))
      Visit(BB);
}

std::vector<const Value *> FunctionEmitter::blockParams(const BasicBlock *BB) const {
  std::vector<const Value *> Params;
  for (const PHINode &P : BB->phis())
    Params.push_back(&P);
  const BitVector &Live = LiveIn[BlockIndex.lookup(BB)];
  for (unsigned V : Live.set_bits())
    Params.push_back(Values[V]);
  return Params;
}

std::string FunctionEmitter::operand(const Value *V) {
  if (auto *C = dyn_cast<Constant>(V))
    return Context.constant(C);
  auto It = Names.find(V);
  if (It == Names.end())
    reject("operand " + printed(*V));
  return It->second;
}

// `Inner` is a constructor applied to its fields, named from inside the function's namespace.
std::string FunctionEmitter::constructorPath(const BasicBlock *BB, const std::string &Inner) {
  if (Recursive || Blocks.size() <= MaxFlatBlocks)
    return "(." + Inner + ")";
  return "(.g" + std::to_string(BlockIndex.lookup(BB) / blocksPerGroup()) + " (." + Inner + "))";
}

// How a block continues at `To`: returning it to the driver, or calling it.
std::string FunctionEmitter::goTo(const BasicBlock *From, const BasicBlock *To) {
  if (Recursive)
    return "(" + LeanName + ".loop " + target(From, To) + ")";
  return "jump " + target(From, To);
}

std::string FunctionEmitter::target(const BasicBlock *From, const BasicBlock *To) {
  std::string Inner = BlockNames.lookup(To);
  if (Chooses)
    Inner += " (c'.sub 0)";
  if (UsesMemory)
    Inner += " m";
  for (const PHINode &P : To->phis())
    Inner += " " + operand(P.getIncomingValueForBlock(From));
  for (unsigned V : LiveIn[BlockIndex.lookup(To)].set_bits())
    Inner += " " + Names.at(Values[V]);
  return constructorPath(To, Inner);
}

std::string FunctionEmitter::emitConstructor(const BasicBlock *BB) {
  std::string Out = "  | " + BlockNames.lookup(BB);
  if (Chooses)
    Out += " (c' : Choice)";
  if (UsesMemory)
    Out += " (m : Mem)";
  std::vector<const Value *> Params = blockParams(BB);
  for (size_t I = 0; I != Params.size();) {
    std::string Type = leanType(Params[I]->getType());
    std::string Group;
    for (; I != Params.size() && leanType(Params[I]->getType()) == Type; ++I)
      Group += (Group.empty() ? "" : " ") + Names.at(Params[I]);
    Out += " (" + Group + " : " + Type + ")";
  }
  return Out + "\n";
}

// Metadata is either a hint with no meaning for one run of the program, or can make a result poison
// or undefined. `noundef` on a load is handled by the load, and the rest of that kind are refused.
void FunctionEmitter::checkMetadata(const Instruction &I) {
  SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
  I.getAllMetadataOtherThanDebugLoc(MDs);
  SmallVector<StringRef, 32> Kinds;
  I.getContext().getMDKindNames(Kinds);
  // `tbaa` is refused because the model doesn't have it yet: LangRef makes accesses that alias undefined if
  // their tags say they don't, which takes a tag on every byte to check. Compiling with -fno-strict-aliasing
  // leaves it out. The others that promise pointers don't alias come from `restrict` being inlined, which
  // zlib doesn't use.
  static const std::set<std::string> Harmless = {"llvm.loop",  "prof",       "unpredictable",
                                                 "nosanitize", "noundef",    "heapallocsite",
                                                 "srcloc",     "annotation", "inline_history"};
  for (const auto &MD : MDs)
    if (!Harmless.count(Kinds[MD.first].str()))
      reject("metadata !" + Kinds[MD.first].str() + " on " + printed(I));
}

// An integer that can be stored whole, or a pointer. Other types in memory aren't modeled yet.
static void checkMemoryType(Type *T, const Instruction &I) {
  if (T->isPointerTy())
    return;
  if (T->isIntOrIntVectorTy() && T->getScalarSizeInBits() % 8 == 0)
    return;
  reject("instruction " + printed(I));
}

void FunctionEmitter::emitLoad(const LoadInst &L, std::vector<Line> &Out) {
  if (L.isVolatile() || L.isAtomic())
    reject("instruction " + printed(L));
  checkMemoryType(L.getType(), L);
  std::string Align = std::to_string(L.getAlign().value());
  std::string P = operand(L.getPointerOperand());
  if (L.getType()->isPointerTy())
    addBind(L, Out, "Mem.loadPtr m " + P + " " + Align);
  else if (auto *V = dyn_cast<FixedVectorType>(L.getType())) {
    if (L.hasMetadata(LLVMContext::MD_noundef))
      reject("instruction " + printed(L));
    addBind(L, Out,
            "Mem.loadVec " + std::to_string(V->getNumElements()) + " " +
                std::to_string(V->getScalarSizeInBits()) + " m " + P + " " + Align);
  } else
    addBind(L, Out,
            "Mem.loadInt " + std::to_string(L.getType()->getIntegerBitWidth()) + " m " + P + " " + Align);
  if (L.hasMetadata(LLVMContext::MD_noundef))
    Out.push_back({Line::Guard, "", "noundef " + Names.at(&L)});
}

void FunctionEmitter::emitStore(const StoreInst &S, std::vector<Line> &Out) {
  if (S.isVolatile() || S.isAtomic())
    reject("instruction " + printed(S));
  checkMemoryType(S.getValueOperand()->getType(), S);
  std::string Align = std::to_string(S.getAlign().value());
  Type *T = S.getValueOperand()->getType();
  const char *Fn = T->isPointerTy()  ? "Mem.storePtr m "
                   : T->isVectorTy() ? "Mem.storeVec m "
                                     : "Mem.storeInt m ";
  addMemoryUpdate(Out,
                  Fn + operand(S.getPointerOperand()) + " " + operand(S.getValueOperand()) + " " + Align);
}

// Each non-zero index is a step, whose offset is written out from the data layout, so `Mem.gep` only
// sees a number. Zero indices do nothing, whatever the flags say.
void FunctionEmitter::emitGep(const GetElementPtrInst &G, std::vector<Line> &Out) {
  const DataLayout &DL = Context.DL;
  if (G.getType()->isVectorTy() || DL.getIndexSizeInBits(0) != 64)
    reject("instruction " + printed(G));
  bool InBounds = G.isInBounds();
  bool NoUnsigned = G.hasNoUnsignedWrap();
  bool NoSigned = InBounds || G.hasNoUnsignedSignedWrap();
  std::string Flags = flag(NoUnsigned, "nuw") + flag(NoSigned, "nsw");
  std::vector<std::string> Offsets;
  auto AddConstant = [&](const APInt &Index, uint64_t Size) {
    APInt Scale(64, Size);
    bool SignedMul, UnsignedMul;
    APInt Offset = Index.smul_ov(Scale, SignedMul);
    (void)Index.umul_ov(Scale, UnsignedMul);
    if ((NoSigned && SignedMul) || (NoUnsigned && UnsignedMul))
      Offsets.push_back("(none : Val 64)");
    else if (!Offset.isZero())
      Offsets.push_back("(some " + bitVec(Offset) + ")");
    // `inbounds` needs its base in bounds if any index isn't zero, even if the offset is.
    else if (InBounds && !Index.isZero())
      reject("instruction " + printed(G));
  };
  for (auto It = gep_type_begin(G), E = gep_type_end(G); It != E; ++It) {
    const Value *Index = It.getOperand();
    if (StructType *S = It.getStructTypeOrNull()) {
      unsigned Field = cast<ConstantInt>(Index)->getZExtValue();
      uint64_t FieldOffset = DL.getStructLayout(S)->getElementOffset(Field);
      if (InBounds && Field != 0 && FieldOffset == 0)
        reject("instruction " + printed(G));
      AddConstant(APInt(64, FieldOffset), 1);
      continue;
    }
    // A wider index has its own rules about truncating, and no real code needs one.
    if (It.isVector() || Index->getType()->getIntegerBitWidth() > 64)
      reject("instruction " + printed(G));
    uint64_t Stride = It.getSequentialElementStride(DL);
    if (auto *K = dyn_cast<ConstantInt>(Index)) {
      AddConstant(K->getValue().sext(64), Stride);
      continue;
    }
    if (Stride == 0 && InBounds)
      reject("instruction " + printed(G));
    std::string I = operand(Index);
    if (Index->getType()->getIntegerBitWidth() < 64)
      I = "(Val.sext 64 " + I + ")";
    if (Stride != 1)
      I = "(Val.mul " + I + " (some " + std::to_string(Stride) + "#64)" + Flags + ")";
    Offsets.push_back(I);
  }
  std::string Base = "m " + operand(G.getPointerOperand()) + " ";
  std::string GepFlags =
      flag(InBounds, "inbounds") + flag(NoSigned && !InBounds, "nusw") + flag(NoUnsigned, "nuw");
  if (Offsets.size() > 1) {
    std::string List;
    for (const std::string &Offset : Offsets)
      List += (List.empty() ? "" : ", ") + Offset;
    addLet(G, Out, "Mem.gepSteps " + Base + "[" + List + "]" + GepFlags);
    return;
  }
  addLet(G, Out, "Mem.gep " + Base + (Offsets.empty() ? "(some 0#64)" : Offsets.front()) + GepFlags);
}

void FunctionEmitter::emitAlloca(const AllocaInst &A, std::vector<Line> &Out) {
  TypeSize EachSize = Context.DL.getTypeAllocSize(A.getAllocatedType());
  if (EachSize.isScalable())
    reject("instruction " + printed(A));
  uint64_t Each = EachSize.getFixedValue();
  const Value *Count = A.getArraySize();
  unsigned Width = Count->getType()->getIntegerBitWidth();
  std::string Bytes;
  // An allocation's size in bytes has to fit in 64 bits, and wrapping it would make a smaller one than was
  // asked for. LangRef doesn't say what a larger one does, so a constant one is refused.
  if (const auto *K = dyn_cast<ConstantInt>(Count)) {
    bool Overflow = K->getValue().getActiveBits() > 64;
    APInt Total = Overflow ? APInt(64, 0) : K->getValue().zextOrTrunc(64).umul_ov(APInt(64, Each), Overflow);
    if (Overflow)
      reject("alloca of more bytes than 64 bits can count: " + printed(A));
    Bytes = "(some " + bitVec(Total) + ")";
  } else {
    // Counted the same way as a constant one, so one that doesn't fit is poison, and `Mem.alloca` of poison
    // is undefined.
    if (Width > 64)
      reject("alloca with a count wider than 64 bits: " + printed(A));
    std::string C = operand(Count);
    if (Width != 64)
      C = "(Val.zext 64 " + C + ")";
    Bytes = "(Val.mul " + C + " (some " + std::to_string(Each) + "#64) (nuw := true))";
  }
  // An alloca with `lifetime.start` is dead until that runs.
  bool Dead = any_of(A.users(), [](const User *U) {
    const auto *I = dyn_cast<IntrinsicInst>(U);
    return I && I->getIntrinsicID() == Intrinsic::lifetime_start;
  });
  Out.push_back({Line::Bind, "(" + Names.at(&A) + ", m)", "Mem.alloca m " + Bytes + flag(Dead, "dead")});
}

// A pointer as an address, for comparisons and `ptrtoint`.
std::string FunctionEmitter::pointerAsInt(const Value *V) { return "(Mem.toVal m " + operand(V) + ")"; }

// A look at a pointer's address. A constant has no tags, so there's nothing to check.
void FunctionEmitter::observeAddress(const Value *V, bool NullCheck, std::vector<Line> &Out) {
  if (!isa<Constant>(V))
    Out.push_back({Line::Guard, "", "Mem.observeAddress " + operand(V) + (NullCheck ? " true" : " false")});
}

void FunctionEmitter::emitInstruction(const Instruction &I, std::vector<Line> &Out) {
  checkMetadata(I);
  auto Op = [&](unsigned N) { return operand(I.getOperand(N)); };
  bool IsVector = I.getType()->isVectorTy();
  // A binary operation, which on vectors applies to each lane.
  auto Binary = [&](const std::string &Fn, const std::string &Flags = "") {
    if (IsVector)
      addLet(I, Out, "Vec.map2 (fun a b => " + Fn + " a b" + Flags + ") " + Op(0) + " " + Op(1));
    else
      addLet(I, Out, Fn + " " + Op(0) + " " + Op(1) + Flags);
  };
  // A cast. `Fn` takes the result's lane width first, and the flags come after the operand.
  auto Cast = [&](const std::string &Fn, const std::string &Flags = "") {
    std::string Width = std::to_string(I.getType()->getScalarSizeInBits());
    if (IsVector)
      addLet(I, Out, "Vec.map (fun a => " + Fn + " " + Width + " a" + Flags + ") " + Op(0));
    else
      addLet(I, Out, Fn + " " + Width + " " + Op(0) + Flags);
  };
  // Effects on one lane of a vector don't have a meaning here yet.
  auto ScalarOnly = [&] {
    if (IsVector)
      reject("instruction " + printed(I));
  };
  auto Wrap = [&] {
    std::string Flags;
    if (I.hasNoUnsignedWrap())
      Flags += flag(true, "nuw");
    if (I.hasNoSignedWrap())
      Flags += flag(true, "nsw");
    return Flags;
  };
  switch (I.getOpcode()) {
  case Instruction::Add:
    Binary("Val.add", Wrap());
    return;
  case Instruction::Sub:
    Binary("Val.sub", Wrap());
    return;
  case Instruction::Mul:
    Binary("Val.mul", Wrap());
    return;
  case Instruction::Shl:
    Binary("Val.shl", Wrap());
    return;
  case Instruction::LShr:
    Binary("Val.lshr", flag(I.isExact(), "exact"));
    return;
  case Instruction::AShr:
    Binary("Val.ashr", flag(I.isExact(), "exact"));
    return;
  case Instruction::UDiv:
    ScalarOnly();
    addBind(I, Out, "Val.udiv " + Op(0) + " " + Op(1) + flag(I.isExact(), "exact"));
    return;
  case Instruction::SDiv:
    ScalarOnly();
    addBind(I, Out, "Val.sdiv " + Op(0) + " " + Op(1) + flag(I.isExact(), "exact"));
    return;
  case Instruction::URem:
    ScalarOnly();
    addBind(I, Out, "Val.urem " + Op(0) + " " + Op(1));
    return;
  case Instruction::SRem:
    ScalarOnly();
    addBind(I, Out, "Val.srem " + Op(0) + " " + Op(1));
    return;
  case Instruction::And:
    Binary("Val.and");
    return;
  case Instruction::Or:
    Binary("Val.or", flag(cast<PossiblyDisjointInst>(I).isDisjoint(), "disjoint"));
    return;
  case Instruction::Xor:
    Binary("Val.xor");
    return;
  case Instruction::ICmp: {
    const auto &C = cast<ICmpInst>(I);
    const char *Fn;
    switch (C.getPredicate()) {
    case CmpInst::ICMP_EQ:
      Fn = "Val.icmpEq";
      break;
    case CmpInst::ICMP_NE:
      Fn = "Val.icmpNe";
      break;
    case CmpInst::ICMP_UGT:
      Fn = "Val.icmpUgt";
      break;
    case CmpInst::ICMP_UGE:
      Fn = "Val.icmpUge";
      break;
    case CmpInst::ICMP_ULT:
      Fn = "Val.icmpUlt";
      break;
    case CmpInst::ICMP_ULE:
      Fn = "Val.icmpUle";
      break;
    case CmpInst::ICMP_SGT:
      Fn = "Val.icmpSgt";
      break;
    case CmpInst::ICMP_SGE:
      Fn = "Val.icmpSge";
      break;
    case CmpInst::ICMP_SLT:
      Fn = "Val.icmpSlt";
      break;
    case CmpInst::ICMP_SLE:
      Fn = "Val.icmpSle";
      break;
    default:
      reject("instruction " + printed(I));
    }
    bool IsPointer = C.getOperand(0)->getType()->isPointerTy();
    if (IsVector) {
      Binary(Fn, flag(C.hasSameSign(), "samesign"));
      return;
    }
    if (IsPointer) {
      observeAddress(C.getOperand(0), C.isEquality() && isa<ConstantPointerNull>(C.getOperand(1)), Out);
      observeAddress(C.getOperand(1), C.isEquality() && isa<ConstantPointerNull>(C.getOperand(0)), Out);
    }
    addLet(I, Out,
           std::string(Fn) + " " + (IsPointer ? pointerAsInt(C.getOperand(0)) : Op(0)) + " " +
               (IsPointer ? pointerAsInt(C.getOperand(1)) : Op(1)) + flag(C.hasSameSign(), "samesign"));
    return;
  }
  case Instruction::Load:
    emitLoad(cast<LoadInst>(I), Out);
    return;
  case Instruction::Store:
    emitStore(cast<StoreInst>(I), Out);
    return;
  case Instruction::GetElementPtr:
    emitGep(cast<GetElementPtrInst>(I), Out);
    return;
  case Instruction::Alloca:
    emitAlloca(cast<AllocaInst>(I), Out);
    return;
  // `ptrtoaddr` doesn't capture the pointer, which only matters to the compiler, so here it's the same.
  case Instruction::PtrToAddr:
  case Instruction::PtrToInt: {
    unsigned Width = I.getType()->getIntegerBitWidth();
    observeAddress(I.getOperand(0), false, Out);
    std::string V = pointerAsInt(I.getOperand(0));
    addLet(I, Out, Width == 64 ? V : "Val.trunc " + std::to_string(Width) + " " + V);
    return;
  }
  case Instruction::Select:
    addLet(I, Out,
           std::string(I.getOperand(0)->getType()->isVectorTy() ? "Vec.select " : "select ") + Op(0) + " " +
               Op(1) + " " + Op(2));
    return;
  case Instruction::ZExt:
    Cast("Val.zext", flag(I.hasNonNeg(), "nneg"));
    return;
  case Instruction::SExt:
    Cast("Val.sext");
    return;
  case Instruction::Trunc: {
    const auto &T = cast<TruncInst>(I);
    Cast("Val.trunc", flag(T.hasNoUnsignedWrap(), "nuw") + flag(T.hasNoSignedWrap(), "nsw"));
    return;
  }
  // Between integers and vectors of integers of the same size, where one lane width divides the other, so
  // it's a split or a join, with a scalar as a vector of one lane. LangRef reads it as a store and a load,
  // which puts lane 0 in the low bits only on a little-endian target, so a big-endian module is refused, even
  // for a function that doesn't touch memory.
  case Instruction::BitCast: {
    Type *Src = I.getOperand(0)->getType();
    Type *Dst = I.getType();
    auto IntegerShape = [](Type *T) {
      return T->isIntegerTy() || (isa<FixedVectorType>(T) && T->getScalarType()->isIntegerTy());
    };
    if (!IntegerShape(Src) || !IntegerShape(Dst))
      reject("integer bitcast shape " + printed(I));
    unsigned W = Src->getScalarSizeInBits(), V = Dst->getScalarSizeInBits();
    unsigned SrcLanes = Src->isVectorTy() ? cast<FixedVectorType>(Src)->getNumElements() : 1;
    unsigned DstLanes = IsVector ? cast<FixedVectorType>(Dst)->getNumElements() : 1;
    if (uint64_t(W) * SrcLanes != uint64_t(V) * DstLanes)
      reject("integer bitcast size " + printed(I));
    if (W % V != 0 && V % W != 0)
      reject("integer bitcast with nondividing lane widths " + printed(I));
    if (!Context.DL.isLittleEndian())
      reject("big-endian integer bitcast " + printed(I));
    if (!Src->isVectorTy() && !IsVector) {
      addLet(I, Out, Op(0));
      return;
    }
    std::string In = Src->isVectorTy() ? Op(0) : "#v[" + Op(0) + "]";
    std::string M = std::to_string(DstLanes), VS = std::to_string(V), Expr = In;
    if (W > V)
      Expr = "Vec.split " + M + " " + VS + " " + std::to_string(W / V) + " " + In;
    else if (V > W)
      Expr = "Vec.join " + M + " " + VS + " " + std::to_string(V / W) + " " + In;
    addLet(I, Out, IsVector ? Expr : "Vec.lane (" + Expr + ") 0");
    return;
  }
  case Instruction::ExtractElement:
    addLet(I, Out, "Vec.extract " + Op(0) + " " + Op(1));
    return;
  case Instruction::InsertElement:
    addLet(I, Out, "Vec.insert " + Op(0) + " " + Op(1) + " " + Op(2));
    return;
  case Instruction::ShuffleVector: {
    const auto &V = cast<ShuffleVectorInst>(I);
    auto *Result = dyn_cast<FixedVectorType>(V.getType());
    if (!Result)
      reject("instruction " + printed(I));
    std::string Mask = "#[";
    bool First = true;
    for (int M : V.getShuffleMask()) {
      Mask += std::string(First ? "" : ", ") + (M < 0 ? "none" : "some " + std::to_string(M));
      First = false;
    }
    addLet(I, Out,
           "Vec.shuffle " + std::to_string(Result->getNumElements()) + " " + Op(0) + " " + Op(1) + " " +
               Mask + "]");
    return;
  }
  case Instruction::Freeze:
    // Of a vector, LangRef freezes each lane, and of a pointer it gives one with no provenance: neither is
    // modeled.
    if (!I.getType()->isIntegerTy())
      reject("instruction " + printed(I));
    addLet(I, Out, "Val.freeze (c'.pick " + nextChooser() + ") " + Op(0));
    return;
  case Instruction::ExtractValue: {
    const auto &E = cast<ExtractValueInst>(I);
    std::string Expr = Op(0);
    Type *T = E.getAggregateOperand()->getType();
    for (unsigned Idx : E.indices()) {
      auto *S = dyn_cast<StructType>(T);
      if (!S)
        reject("instruction " + printed(I));
      // Lean tuples nest to the right, so a middle field is reached through `.2`s then `.1`.
      for (unsigned K = 0; K != Idx; ++K)
        Expr += ".2";
      if (Idx + 1 != S->getNumElements())
        Expr += ".1";
      T = S->getElementType(Idx);
    }
    addLet(I, Out, Expr);
    return;
  }
  case Instruction::InsertValue: {
    const auto &V = cast<InsertValueInst>(I);
    auto *S = dyn_cast<StructType>(V.getType());
    if (!S || V.getNumIndices() != 1)
      reject("instruction " + printed(I));
    unsigned Idx = V.getIndices()[0];
    std::string Base = Op(0), Expr = "(";
    for (unsigned K = 0, E = S->getNumElements(); K != E; ++K) {
      std::string Field = Base;
      for (unsigned J = 0; J != K; ++J)
        Field += ".2";
      if (K + 1 != E)
        Field += ".1";
      Expr += (K ? ", " : "") + (K == Idx ? Op(1) : Field);
    }
    addLet(I, Out, Expr + ")");
    return;
  }
  case Instruction::Call:
    emitCall(cast<CallBase>(I), Out);
    return;
  default:
    reject("instruction " + printed(I));
  }
}

// An argument with what its attributes imply, and the checks they require before the call. `WithDeclaration`
// adds what the callee's declaration says of the argument's value, for a callee nothing else checks it in.
// Both have to hold, so each is checked on its own: a call's `range` doesn't replace the declaration's.
std::string FunctionEmitter::callArgument(const CallBase &C, unsigned N, std::vector<Line> &Out,
                                          bool WithDeclaration) {
  std::vector<AttributeSet> Sets = {C.getAttributes().getParamAttrs(N)};
  if (const Function *Callee = C.getCalledFunction(); WithDeclaration && Callee) {
    AttributeSet Declared = Callee->getAttributes().getParamAttrs(N);
    AttrBuilder B(C.getContext());
    for (Attribute::AttrKind K : {Attribute::NoUndef, Attribute::NonNull, Attribute::Alignment,
                                  Attribute::Range, Attribute::Dereferenceable})
      if (Declared.hasAttribute(K))
        B.addAttribute(Declared.getAttribute(K));
    Sets.push_back(AttributeSet::get(C.getContext(), B));
    // A global's address is what makes these hold, and LLVM fixes what they say of one: it isn't null, and
    // it's as aligned and as large as it's declared. So they're settled here, and a function that passes only
    // constants needn't have memory to check them in. One that can't be shown to hold is refused.
    const auto *Global = dyn_cast<GlobalVariable>(C.getArgOperand(N));
    for (AttributeSet &Set : Sets) {
      AttrBuilder S(C.getContext(), Set);
      if (Global && !Global->hasExternalWeakLinkage() && Global->getValueType()->isSized()) {
        MaybeAlign Wanted = S.getAlignment();
        bool Holds = (!Wanted || Global->getPointerAlignment(Context.DL) >= *Wanted) &&
                     (!S.contains(Attribute::Dereferenceable) ||
                      Context.DL.getTypeStoreSize(Global->getValueType()).getFixedValue() >=
                          S.getDereferenceableBytes());
        if (!Holds)
          reject("call argument attributes that don't plainly hold of @" + Global->getName().str());
        S.removeAttribute(Attribute::NonNull).removeAttribute(Attribute::Alignment);
        S.removeAttribute(Attribute::Dereferenceable);
      } else if (!UsesMemory && (S.contains(Attribute::NonNull) || S.contains(Attribute::Alignment) ||
                                 S.contains(Attribute::Dereferenceable))) {
        reject("call argument attributes that don't plainly hold of " + printed(*C.getArgOperand(N)));
      }
      Set = AttributeSet::get(C.getContext(), S);
    }
  }
  std::string Arg = operand(C.getArgOperand(N));
  bool NoUndef = false;
  for (AttributeSet Set : Sets) {
    checkValueAttributes(Set, C.getArgOperand(N)->getType(), Position::CallParameter);
    Arg = withValueChecks(Set, Arg);
    NoUndef |= Set.hasAttribute(Attribute::NoUndef);
  }
  if (NoUndef)
    Out.push_back({Line::Guard, "", "noundef " + Arg});
  for (AttributeSet Set : Sets)
    if (Set.hasAttribute(Attribute::Dereferenceable))
      Out.push_back({Line::Guard, "",
                     "Mem.dereferenceable m " + Arg + " " + std::to_string(Set.getDereferenceableBytes())});
  return Arg;
}

// The call-site return attributes apply to the value the call produced.
void FunctionEmitter::checkCallResult(const CallBase &C, std::vector<Line> &Out) {
  if (C.getType()->isVoidTy())
    return;
  AttributeSet Ret = C.getAttributes().getRetAttrs();
  const std::string &Name = Names.at(&C);
  if (hasValueChecks(Ret))
    Out.push_back({Line::Let, Name, withValueChecks(Ret, Name)});
  if (Ret.hasAttribute(Attribute::NoUndef))
    Out.push_back({Line::Guard, "", "noundef " + Name});
  if (Ret.hasAttribute(Attribute::Dereferenceable))
    Out.push_back({Line::Guard, "",
                   "Mem.dereferenceable m " + Name + " " + std::to_string(Ret.getDereferenceableBytes())});
}

bool FunctionEmitter::emitIntrinsic(const IntrinsicInst &C, std::vector<Line> &Out) {
  // An argument's attributes count even if the intrinsic's meaning doesn't use the argument.
  std::vector<std::string> Args;
  for (unsigned N = 0, E = C.arg_size(); N != E; ++N)
    Args.push_back(isa<MetadataAsValue>(C.getArgOperand(N)) ? "" : callArgument(C, N, Out));
  auto Op = [&](unsigned N) { return Args[N]; };
  auto BoolArg = [&](unsigned N) -> std::string {
    auto *K = dyn_cast<ConstantInt>(C.getArgOperand(N));
    if (!K)
      reject("instruction " + printed(C));
    return K->isOne() ? "true" : "false";
  };
  auto Unary = [&](const char *Fn) {
    addLet(C, Out, std::string(Fn) + " " + Op(0));
    return true;
  };
  auto Binary = [&](const char *Fn) {
    if (C.getType()->isVectorTy())
      addLet(C, Out, "Vec.map2 (fun a b => " + std::string(Fn) + " a b) " + Op(0) + " " + Op(1));
    else
      addLet(C, Out, std::string(Fn) + " " + Op(0) + " " + Op(1));
    return true;
  };
  auto Reduce = [&](const char *Fn) {
    addLet(C, Out, "Vec.reduce (fun a b => " + std::string(Fn) + " a b) " + Op(0));
    return true;
  };
  auto Ternary = [&](const char *Fn) {
    addLet(C, Out, std::string(Fn) + " " + Op(0) + " " + Op(1) + " " + Op(2));
    return true;
  };
  auto Lanes = [&] { return std::to_string(cast<FixedVectorType>(C.getType())->getNumElements()); };
  // A length in bytes, which LangRef reads as unsigned, as the 64 bits `Mem` counts in.
  auto Length = [&](unsigned N) {
    unsigned Width = C.getArgOperand(N)->getType()->getIntegerBitWidth();
    if (Width > 64)
      reject("instruction " + printed(C));
    return Width == 64 ? Op(N) : "(Val.zext 64 " + Op(N) + ")";
  };
  // These print the scalar operation, which on vectors isn't the lane-by-lane one LangRef gives, nor even
  // Lean that elaborates. tests/ir_features.py elaborates what this prints for every intrinsic it translates.
  auto ScalarOnly = [&] {
    if (any_of(C.args(), [](const Use &U) { return U->getType()->isVectorTy(); }))
      reject("intrinsic " + C.getCalledFunction()->getName().str() + " of vectors");
  };
  switch (C.getIntrinsicID()) {
  case Intrinsic::ctpop:
  case Intrinsic::bitreverse:
  case Intrinsic::bswap:
  case Intrinsic::ctlz:
  case Intrinsic::cttz:
  case Intrinsic::abs:
  case Intrinsic::fshl:
  case Intrinsic::fshr:
  case Intrinsic::uadd_with_overflow:
  case Intrinsic::sadd_with_overflow:
  case Intrinsic::usub_with_overflow:
  case Intrinsic::ssub_with_overflow:
  case Intrinsic::umul_with_overflow:
  case Intrinsic::smul_with_overflow:
  case Intrinsic::ucmp:
  case Intrinsic::scmp:
    ScalarOnly();
    break;
  default:
    break;
  }
  switch (C.getIntrinsicID()) {
  case Intrinsic::assume:
    for (unsigned B = 0, E = C.getNumOperandBundles(); B != E; ++B) {
      OperandBundleUse Bundle = C.getOperandBundleAt(B);
      if (Bundle.getTagName() != "nonnull" || Bundle.Inputs.size() != 1)
        reject("instruction " + printed(C));
      Out.push_back({Line::Guard, "", "Mem.assumeNonnull m " + operand(Bundle.Inputs[0].get())});
    }
    Out.push_back({Line::Guard, "", "assume " + Op(0)});
    return true;
  // This says nothing about what the program computes.
  case Intrinsic::donothing:
    return true;
  // LangRef says optimizers "must assume that it has externally observable effects", so a loop calling it
  // makes progress. The model has no observable effects, and would call that loop undefined under a promise.
  case Intrinsic::sideeffect:
    reject("intrinsic llvm.sideeffect, which LangRef makes observable progress, and the model has none");
  case Intrinsic::expect:
    addLet(C, Out, Op(0));
    return true;
  case Intrinsic::lifetime_start:
    addMemoryUpdate(Out, "Mem.lifetime m " + Op(0) + " true");
    return true;
  case Intrinsic::lifetime_end:
    addMemoryUpdate(Out, "Mem.lifetime m " + Op(0) + " false");
    return true;
  case Intrinsic::memset:
    if (BoolArg(3) != "false")
      reject("instruction " + printed(C));
    addMemoryUpdate(Out, "Mem.memset m " + Op(0) + " " + Op(1) + " " + Length(2));
    return true;
  case Intrinsic::memcpy:
    if (BoolArg(3) != "false")
      reject("instruction " + printed(C));
    addMemoryUpdate(Out, "Mem.memcpy m " + Op(0) + " " + Op(1) + " " + Length(2));
    return true;
  case Intrinsic::vector_reduce_add:
    return Reduce("Val.add");
  case Intrinsic::vector_reduce_mul:
    return Reduce("Val.mul");
  case Intrinsic::vector_reduce_and:
    return Reduce("Val.and");
  case Intrinsic::vector_reduce_or:
    return Reduce("Val.or");
  case Intrinsic::vector_reduce_xor:
    return Reduce("Val.xor");
  case Intrinsic::vector_reduce_umin:
    return Reduce("Val.umin");
  case Intrinsic::vector_reduce_umax:
    return Reduce("Val.umax");
  case Intrinsic::vector_reduce_smin:
    return Reduce("Val.smin");
  case Intrinsic::vector_reduce_smax:
    return Reduce("Val.smax");
  case Intrinsic::ctpop:
    return Unary("Val.ctpop");
  case Intrinsic::bitreverse:
    return Unary("Val.bitreverse");
  case Intrinsic::bswap:
    return Unary("Val.bswap");
  case Intrinsic::ctlz:
    addLet(C, Out, "Val.ctlz " + Op(0) + " " + BoolArg(1));
    return true;
  case Intrinsic::cttz:
    addLet(C, Out, "Val.cttz " + Op(0) + " " + BoolArg(1));
    return true;
  case Intrinsic::abs:
    addLet(C, Out, "Val.abs " + Op(0) + " " + BoolArg(1));
    return true;
  case Intrinsic::umin:
    return Binary("Val.umin");
  case Intrinsic::umax:
    return Binary("Val.umax");
  case Intrinsic::smin:
    return Binary("Val.smin");
  case Intrinsic::smax:
    return Binary("Val.smax");
  case Intrinsic::fshl:
    return Ternary("Val.fshl");
  case Intrinsic::fshr:
    return Ternary("Val.fshr");
  case Intrinsic::uadd_sat:
    return Binary("Val.uaddSat");
  case Intrinsic::usub_sat:
    return Binary("Val.usubSat");
  case Intrinsic::sadd_sat:
    return Binary("Val.saddSat");
  case Intrinsic::ssub_sat:
    return Binary("Val.ssubSat");
  case Intrinsic::uadd_with_overflow:
    return Binary("Val.uaddWithOverflow");
  case Intrinsic::sadd_with_overflow:
    return Binary("Val.saddWithOverflow");
  case Intrinsic::usub_with_overflow:
    return Binary("Val.usubWithOverflow");
  case Intrinsic::ssub_with_overflow:
    return Binary("Val.ssubWithOverflow");
  case Intrinsic::umul_with_overflow:
    return Binary("Val.umulWithOverflow");
  case Intrinsic::smul_with_overflow:
    return Binary("Val.smulWithOverflow");
  // x86's integer dot products, in IRLean/X86.lean. The first two need the number of lanes they produce.
  case Intrinsic::x86_ssse3_pmadd_ub_sw_128:
  case Intrinsic::x86_avx2_pmadd_ub_sw:
  case Intrinsic::x86_avx512_pmaddubs_w_512:
    addLet(C, Out, "X86.pmaddubsw " + Lanes() + " " + Op(0) + " " + Op(1));
    return true;
  case Intrinsic::x86_sse2_pmadd_wd:
  case Intrinsic::x86_avx2_pmadd_wd:
  case Intrinsic::x86_avx512_pmaddw_d_512:
    addLet(C, Out, "X86.pmaddwd " + Lanes() + " " + Op(0) + " " + Op(1));
    return true;
  case Intrinsic::x86_avx512_vpdpbusd_128:
  case Intrinsic::x86_avx512_vpdpbusd_256:
  case Intrinsic::x86_avx512_vpdpbusd_512:
    addLet(C, Out, "X86.vpdpbusd " + Op(0) + " " + Op(1) + " " + Op(2));
    return true;
  case Intrinsic::ucmp:
  case Intrinsic::scmp:
    addLet(C, Out,
           std::string(C.getIntrinsicID() == Intrinsic::ucmp ? "Val.ucmp " : "Val.scmp ") +
               std::to_string(C.getType()->getIntegerBitWidth()) + " " + Op(0) + " " + Op(1));
    return true;
  default:
    return false;
  }
}

void FunctionEmitter::emitCall(const CallBase &C, std::vector<Line> &Out) {
  const Function *Direct = C.getCalledFunction();
  // LangRef: "The calling convention of any pair of dynamic caller/callee must match, or the behavior of the
  // program is undefined." The model would run such a call, so it's refused, as is a call through a pointer
  // that can reach a function with another.
  auto SameConvention = [&](const Function *Callee) {
    if (Callee->getCallingConv() != C.getCallingConv())
      reject("call with calling convention " + std::to_string(C.getCallingConv()) + " to @" +
             Callee->getName().str() + ", whose calling convention is " +
             std::to_string(Callee->getCallingConv()));
  };
  if (Direct)
    SameConvention(Direct);
  else
    for (const Function *Target : Context.candidates(C.getFunctionType()))
      SameConvention(Target);
  bool Library = Direct && libraryFunction(*Direct);
  // A call to something outside the module that never returns, such as an abort, stops the model. A
  // theorem saying `= Outcome.ok` shows it isn't reached, and nothing here claims what it does.
  bool GivesUp = Direct && Direct->isDeclaration() && !Direct->isIntrinsic() && !Library &&
                 C.doesNotReturn() && !C.getFunctionType()->isVarArg() && !C.hasOperandBundles() &&
                 C.getType()->isVoidTy();
  checkFunctionAttributes(C.getAttributes().getFnAttrs(), "call", Library, GivesUp);
  // A function's own promises are checked, but a narrower one at a call isn't, so it's refused. What's known
  // of the C library is the exception: `Mem.strlen` only reads through its argument, and they all return.
  AttributeSet CallAttrs = C.getAttributes().getFnAttrs();
  if (Library && CallAttrs.hasAttribute(Attribute::NoBuiltin))
    reject("call attribute nobuiltin on " + printed(C));
  if (CallAttrs.hasAttribute(Attribute::Memory) &&
      !(Library && Direct->getName() == "strlen" &&
        isRefSet(C.getMemoryEffects().getModRef(IRMemLocation::ArgMem))))
    reject("call attribute memory on " + printed(C));
  for (Attribute::AttrKind Kind : {Attribute::WillReturn, Attribute::MustProgress})
    if (CallAttrs.hasAttribute(Kind) && !Library)
      reject("call attribute " + CallAttrs.getAttribute(Kind).getAsString() + " on " + printed(C));
  for (Attribute::AttrKind Kind : {Attribute::NoFree, Attribute::NoRecurse})
    if (CallAttrs.hasAttribute(Kind) && !(Library && Direct->getName() != "free"))
      reject("call attribute " + CallAttrs.getAttribute(Kind).getAsString() + " on " + printed(C));
  // A `noalias` result is what `Mem.malloc` gives, and a function declaring it is checked at its return.
  bool NoAliasResult = Direct && ((Library && Direct->getName() == "malloc") || Direct->returnDoesNotAlias());
  checkValueAttributes(C.getAttributes().getRetAttrs(), C.getType(), Position::CallReturn, NoAliasResult);
  if (GivesUp) {
    // The arguments are passed before the callee runs, so what their attributes and the declaration say of
    // them is checked first: a poison `noundef` argument is undefined, even to a call that never returns.
    for (unsigned I = 0, E = C.arg_size(); I != E; ++I)
      callArgument(C, I, Out, /*WithDeclaration=*/true);
    Out.push_back({Line::Bind, "_", "(Outcome.stop .noReturnCall : Outcome Unit)"});
    return;
  }
  if (const auto *Intr = dyn_cast<IntrinsicInst>(&C)) {
    if (!emitIntrinsic(*Intr, Out))
      reject("intrinsic " + Intr->getCalledFunction()->getName().str());
    checkCallResult(C, Out);
    return;
  }
  if (C.getFunctionType()->isVarArg())
    reject("variadic call");
  if (C.hasOperandBundles())
    reject("instruction " + printed(C));
  const Function *Callee = C.getCalledFunction();
  // A call runs whichever copy the linker keeps, and only an exact definition is certainly this one. This
  // module's copy of an `_odr` one can't stand in for it.
  if (Callee && !Callee->isDeclaration() && !hasExactLinkage(*Callee))
    reject("call to @" + Callee->getName().str() + ", whose definition may not be the one that runs");
  if (Callee && !Callees.count(Callee))
    reject(Callee->isDeclaration() ? "call to external @" + Callee->getName().str()
                                   : "call to @" + Callee->getName().str() + ", which isn't translated");

  std::string Args;
  for (unsigned I = 0, E = C.arg_size(); I != E; ++I)
    Args += " " + callArgument(C, I, Out);
  bool Void = C.getType()->isVoidTy();
  std::string Bound = "(" + (Void ? std::string("_") : Names.at(&C)) + ", m)";
  // A call to a function that chooses gives it the choices at this chooser's place.
  std::string Choices;
  auto Chooser = [&]() -> const std::string & {
    if (Choices.empty())
      Choices = " (c'.sub " + nextChooser() + ")";
    return Choices;
  };
  if (Callee) {
    std::string Expr = Callees.lookup(Callee) + Args;
    if (ChoosingFunctions.count(Callee))
      Expr += (MemoryFunctions.count(Callee) ? " m" : "") + Chooser();
    if (ChoosingFunctions.count(Callee) && MemoryFunctions.count(Callee))
      Out.push_back({Line::Bind, Bound, promisedCall(Callee, Expr)});
    else if (MemoryFunctions.count(Callee))
      Out.push_back({Line::Bind, Bound, promisedCall(Callee, Expr + " m")});
    else
      addBind(C, Out, promisedCall(Callee, Expr));
  } else {
    // Try each function of this type whose address is taken. Anything else stops the model.
    std::string Expr = "(indirect " + operand(C.getCalledOperand()) + " fun q' =>";
    for (const Function *Target : Context.candidates(C.getFunctionType())) {
      // As for a direct call, this module's copy of an `_odr` function needn't be what the pointer holds.
      if (!hasExactLinkage(*Target))
        reject("indirect call that can reach @" + Target->getName().str() +
               ", whose definition may not be the one that runs");
      if (!Callees.count(Target))
        reject("indirect call that can reach @" + Target->getName().str() + ", which isn't translated");
      std::string Call = Callees.lookup(Target) + Args;
      if (MemoryFunctions.count(Target))
        Call += " m";
      if (ChoosingFunctions.count(Target))
        Call += Chooser();
      if (MemoryFunctions.count(Target))
        Call = promisedCall(Target, Call);
      else
        Call = "andThen (" + promisedCall(Target, Call) + ") fun r' => Outcome.ok (r', m)";
      Expr += "\n      if q'.same " + Context.functionAddress(Target) + " then " + Call + " else";
    }
    Expr += "\n      Outcome.stop .unknownCallee : Outcome (" + leanType(C.getType()) + " × Mem))";
    Out.push_back({Line::Bind, Bound, Expr});
  }
  checkCallResult(C, Out);
}

std::string FunctionEmitter::emitTerminator(const BasicBlock *BB) {
  const Instruction *T = BB->getTerminator();
  const char *Ret = Recursive ? "Outcome.ok " : "ret ";
  auto WithMemory = [&](const std::string &V) { return UsesMemory ? "(" + V + ", m)" : V; };
  if (const auto *R = dyn_cast<ReturnInst>(T)) {
    if (!R->getReturnValue())
      return std::string(Ret) + WithMemory("()");
    AttributeSet Attrs = F.getAttributes().getRetAttrs();
    std::string V = withValueChecks(Attrs, operand(R->getReturnValue()));
    std::string Checks;
    if (Attrs.hasAttribute(Attribute::NoUndef))
      Checks += "noundef " + V + " <| ";
    if (Attrs.hasAttribute(Attribute::Dereferenceable))
      Checks += "Mem.dereferenceable m " + V + " " + std::to_string(Attrs.getDereferenceableBytes()) + " <| ";
    if (Attrs.hasAttribute(Attribute::NoAlias))
      Checks += "Mem.noaliasResult m " + V + " <| ";
    for (const Argument &A : F.args())
      if (A.hasReturnedAttr())
        Checks += std::string(A.getType()->isPointerTy() ? "Mem.returnedArgument " : "Mem.returnedInt ") +
                  Names.at(&A) + " " + V + " <| ";
    return Checks + Ret + WithMemory(V);
  }
  if (const auto *B = dyn_cast<UncondBrInst>(T))
    return goTo(BB, B->getSuccessor(0));
  if (const auto *B = dyn_cast<CondBrInst>(T)) {
    if (Recursive)
      return "branch " + operand(B->getCondition()) + " " + goTo(BB, B->getSuccessor(0)) + " " +
             goTo(BB, B->getSuccessor(1));
    return "br " + operand(B->getCondition()) + " " + target(BB, B->getSuccessor(0)) + " " +
           target(BB, B->getSuccessor(1));
  }
  if (const auto *S = dyn_cast<SwitchInst>(T)) {
    // The binder is primed so no value's name can be the same: NameTable only makes letters, digits and `_`.
    std::string Out = "sw " + operand(S->getCondition()) + " fun sel' =>";
    for (const auto &Case : S->cases())
      Out += "\n      if sel' == " + bitVec(Case.getCaseValue()->getValue()) + " then " +
             goTo(BB, Case.getCaseSuccessor()) + " else";
    return Out + "\n      " + goTo(BB, S->getDefaultDest());
  }
  if (isa<UnreachableInst>(T))
    return "unreachable";
  reject("instruction " + printed(*T));
}

std::string FunctionEmitter::emitArm(const BasicBlock *BB) {
  Current = BB;
  NextChooser = 1;
  std::string Out = "  | ." + BlockNames.lookup(BB);
  if (Chooses)
    Out += " c'";
  if (UsesMemory)
    Out += " m";
  for (const Value *V : blockParams(BB))
    Out += " " + Names.at(V);
  Out += " =>\n";
  std::vector<Line> Lines;
  for (const Instruction &I : *BB) {
    if (isa<PHINode>(I) || I.isTerminator())
      continue;
    emitInstruction(I, Lines);
  }
  for (const Line &L : Lines) {
    switch (L.K) {
    case Line::Let:
      Out += "    let " + L.Name + " := " + L.Expr + "\n";
      break;
    case Line::Bind:
      Out += "    andThen (" + L.Expr + ") fun " + L.Name + " =>\n";
      break;
    case Line::Guard:
      Out += "    " + L.Expr + " <|\n";
      break;
    }
  }
  return Out + "    " + emitTerminator(BB) + "\n";
}

void FunctionEmitter::prepare() {
  if (F.isVarArg())
    reject("variadic function");
  if (F.hasPersonalityFn())
    reject("exception handling");
  if (!hasExactLinkage(F) && !hasODRLinkage(F))
    reject("linkage: this may not be the definition that runs");
  if (F.hasPrefixData() || F.hasPrologueData() || F.hasGC())
    reject("function with prefix data, prologue data or a garbage collector");
  checkFunctionAttributes(F.getAttributes().getFnAttrs(), "function");
  // Neither needs checking on each run: what's reachable shows they hold, or the function is refused.
  if (Recursive && F.hasFnAttribute(Attribute::NoRecurse))
    reject("function attribute norecurse on a function in a cycle");
  if (F.hasFnAttribute(Attribute::NoFree) && ReachesFree.count(&F))
    reject("function attribute nofree on a function that can reach free");
  collectBlocks();
  nameValues();
  computeLiveness();
  findPromises();
  if (Recursive && Blocks.size() > MaxRecursiveBlocks)
    reject("recursive function with more than " + std::to_string(MaxRecursiveBlocks) + " blocks");
  RetType = leanType(F.getReturnType());
  checkValueAttributes(F.getAttributes().getRetAttrs(), F.getReturnType(), Position::Return);
  for (const Value *V : Values)
    leanType(V->getType());
  if (UsesMemory && (Context.DL.getPointerSizeInBits() != 64 || !Context.DL.isLittleEndian()))
    reject("data layout " + F.getParent()->getDataLayoutStr());
  for (const BasicBlock *BB : Blocks)
    for (const Instruction &I : *BB)
      HasAlloca |= isa<AllocaInst>(I);
  // A call only needs a frame if its function promised something about memory.
  AttributeList Attrs = F.getAttributes();
  HasCall = UsesMemory &&
            (F.getMemoryEffects() != MemoryEffects::unknown() || Attrs.hasRetAttr(Attribute::NoAlias));
  for (const Argument &A : F.args()) {
    AttributeSet Param = Attrs.getParamAttrs(A.getArgNo());
    HasCall |=
        UsesMemory && (Param.hasAttribute(Attribute::ReadOnly) || Param.hasAttribute(Attribute::ReadNone) ||
                       Param.hasAttribute(Attribute::WriteOnly) || Param.hasAttribute(Attribute::NoFree) ||
                       Param.hasAttribute(Attribute::Captures) || Param.hasAttribute(Attribute::Initializes));
  }
  // Each would need its own record of what it wrote, and no real code has two that could overlap.
  if (count_if(F.args(), [&](const Argument &A) {
        return Attrs.getParamAttrs(A.getArgNo()).hasAttribute(Attribute::Initializes);
      }) > 1)
    reject("more than one parameter with attribute initializes");
  if (HasCall)
    for (const Argument &A : F.args())
      if (!A.getType()->isPointerTy() && mentionsPointer(A.getType()))
        reject("parameter with pointers in it, in a function that promises something about memory");
}

std::string FunctionEmitter::emitBlocks() {
  std::string NextType = "Outcome (Next Block (" + resultType() + "))";
  std::string Out = "namespace " + LeanName + "\n\n";
  if (Recursive || Blocks.size() <= MaxFlatBlocks) {
    Out += "inductive Block where\n";
    for (const BasicBlock *BB : Blocks)
      Out += emitConstructor(BB);
    if (!Recursive) {
      Out += "\n" + Context.Def + "step : Block → " + NextType + "\n";
      for (const BasicBlock *BB : Blocks)
        Out += emitArm(BB);
    }
  } else {
    unsigned Groups = (Blocks.size() + blocksPerGroup() - 1) / blocksPerGroup();
    for (unsigned G = 0; G != Groups; ++G) {
      Out += "inductive G" + std::to_string(G) + " where\n";
      for (unsigned I = G * blocksPerGroup(); I != Blocks.size() && I != (G + 1) * blocksPerGroup(); ++I)
        Out += emitConstructor(Blocks[I]);
      Out += '\n';
    }
    Out += "inductive Block where\n";
    for (unsigned G = 0; G != Groups; ++G)
      Out += "  | g" + std::to_string(G) + " (block : G" + std::to_string(G) + ")\n";
    Out += '\n';
    for (unsigned G = 0; G != Groups; ++G) {
      Out +=
          Context.Def + "G" + std::to_string(G) + ".step : G" + std::to_string(G) + " → " + NextType + "\n";
      for (unsigned I = G * blocksPerGroup(); I != Blocks.size() && I != (G + 1) * blocksPerGroup(); ++I)
        Out += emitArm(Blocks[I]);
      Out += '\n';
    }
    Out += Context.Def + "step : Block → " + NextType + "\n";
    for (unsigned G = 0; G != Groups; ++G)
      Out += "  | .g" + std::to_string(G) + " block => G" + std::to_string(G) + ".step block\n";
  }
  // The blocks under a promise, when they aren't all of them. The entry block is never in a loop.
  if (!Recursive && !F.willReturn() && !Promised.empty() && Promised.size() != Blocks.size()) {
    Out += "\n/-- The blocks of loops marked `llvm.loop.mustprogress`. -/\n" + Context.Def +
           "promise : Block → Bool\n";
    for (const BasicBlock *BB : Blocks)
      if (Promised.count(BB))
        Out += "  | " + constructorPath(BB, BlockNames.lookup(BB) + " ..") + " => true\n";
    Out += "  | _ => false\n";
  }
  return Out + "\nend " + LeanName + "\n";
}

std::string FunctionEmitter::emitLoop() {
  std::string Out =
      Context.Def + LeanName + ".loop : " + LeanName + ".Block → Outcome (" + resultType() + ")\n";
  for (const BasicBlock *BB : Blocks)
    Out += emitArm(BB);
  return Out + "partial_fixpoint\n";
}

std::string FunctionEmitter::signature(const std::string &Name) {
  std::string Out = Context.Def + Name;
  for (const Argument &A : F.args())
    Out += " (" + Names.at(&A) + " : " + leanType(A.getType()) + ")";
  if (UsesMemory)
    Out += " (m : Mem)";
  if (Chooses)
    return Out + " : Outcomes (" + resultType() + ") := fun c' =>\n";
  return Out + " : Outcome (" + resultType() + ") :=\n";
}

// A run from the entry block, judged by the function's promises.
std::string FunctionEmitter::promisedRun(const std::string &Entry) {
  std::string Run = "run " + LeanName + ".step " + Entry;
  if (F.willReturn())
    return "promised (" + Run + ") fun _ => Outcome.ub .noReturn";
  if (Promised.empty())
    return Run;
  std::string Which = Promised.size() == Blocks.size() ? "(fun _ => true)" : LeanName + ".promise";
  return "promised (" + Run + ") fun _ => runPromised " + Which + " " + LeanName + ".step " + Entry;
}

// Under a promise, a call to a function that promises to progress, and not to return, that never returns is a
// run LangRef doesn't settle, so it stops the model. A callee without the promise may run forever, which
// leaves the run waiting on it, as `runPromised` allows. A recursive function's cycle judges its runs as a
// whole.
std::string FunctionEmitter::promisedCall(const Function *Callee, const std::string &Call) {
  if (Recursive || F.willReturn() || !Promised.count(Current) || !Callee->mustProgress() ||
      Callee->willReturn())
    return Call;
  return "promised (" + Call + ") fun _ => Outcome.stop .progressUnsettled";
}

std::string FunctionEmitter::emitPromisedCycleWrapper() {
  std::string Args;
  for (const Argument &A : F.args())
    Args += " " + Names.at(&A);
  if (UsesMemory)
    Args += " m";
  if (Chooses)
    Args += " c'";
  return signature(LeanName) + "  promised (" + LeanName + ".raw" + Args + ") fun _ => " +
         (F.willReturn() ? "Outcome.ub .noReturn" : "Outcome.stop .recursionUnsettled") + "\n";
}

std::string FunctionEmitter::emitFunction() {
  std::string Out = signature(PromisedCycle ? LeanName + ".raw" : LeanName);
  AttributeList Attrs = F.getAttributes();
  for (const Argument &A : F.args()) {
    AttributeSet Param = Attrs.getParamAttrs(A.getArgNo());
    checkValueAttributes(Param, A.getType(), Position::Parameter);
    const std::string &Name = Names.at(&A);
    if (hasValueChecks(Param))
      Out += "  let " + Name + " := " + withValueChecks(Param, Name) + "\n";
    if (Param.hasAttribute(Attribute::NoUndef))
      Out += "  noundef " + Name + " <|\n";
    if (Param.hasAttribute(Attribute::Dereferenceable))
      Out +=
          "  Mem.dereferenceable m " + Name + " " + std::to_string(Param.getDereferenceableBytes()) + " <|\n";
  }
  if (HasCall) {
    MemoryEffects Effects = F.getMemoryEffects();
    bool Tracked = isModSet(Effects.getModRef(IRMemLocation::Other)) &&
                   !isRefSet(Effects.getModRef(IRMemLocation::Other));
    Tracked |= isModSet(Effects.getModRef(IRMemLocation::ArgMem)) &&
               !isRefSet(Effects.getModRef(IRMemLocation::ArgMem));
    for (const Argument &A : F.args()) {
      AttributeSet Param = Attrs.getParamAttrs(A.getArgNo());
      Tracked |= Param.hasAttribute(Attribute::WriteOnly) || Param.hasAttribute(Attribute::Initializes);
    }
    Out += std::string("  Mem.call m { other := ") + leanAccess(Effects.getModRef(IRMemLocation::Other)) +
           ", arg := " + leanAccess(Effects.getModRef(IRMemLocation::ArgMem)) +
           ", inaccessible := " + leanAccess(Effects.getModRef(IRMemLocation::InaccessibleMem)) +
           ", errno := " + leanAccess(Effects.getModRef(IRMemLocation::ErrnoMem)) + " } " +
           (Tracked ? "true" : "false") + " fun m call' =>\n";
    for (const Argument &A : F.args()) {
      if (!A.getType()->isPointerTy())
        continue;
      AttributeSet Param = Attrs.getParamAttrs(A.getArgNo());
      const std::string &Name = Names.at(&A);
      Out += "  let " + Name + " := Mem.tag " + leanTag(Param) + " " + Name + "\n";
      if (Param.hasAttribute(Attribute::Initializes))
        for (const ConstantRange &R :
             Param.getAttribute(Attribute::Initializes).getValueAsConstantRangeList())
          Out += "  let m := Mem.addInitializes m " + Name + " " + bitVec(R.getLower().sextOrTrunc(64)) +
                 " " + bitVec(R.getUpper().sextOrTrunc(64)) + "\n";
    }
  }
  if (HasAlloca)
    Out += "  Mem.withFrame m fun m =>\n";
  std::string Entry = BlockNames.lookup(Blocks.front());
  if (Chooses)
    Entry += " c'";
  if (UsesMemory)
    Entry += " m";
  for (const Value *V : blockParams(Blocks.front()))
    Entry += " " + Names.at(V);
  if (Recursive)
    return Out + "  " + LeanName + ".loop (." + Entry + ")\npartial_fixpoint\n";
  return Out + "  " + promisedRun(constructorPath(Blocks.front(), Entry)) + "\n";
}

std::string describeSignature(const Function &F) {
  std::string S = "(";
  bool First = true;
  for (const Argument &A : F.args()) {
    S += (First ? "" : ",") + printedType(A.getType());
    First = false;
  }
  return S + ")->" + printedType(F.getReturnType());
}

// Whether a function needs memory passed in, leaving aside what it calls.
bool usesMemoryDirectly(const Function &F) {
  for (const Argument &A : F.args())
    if (mentionsPointer(A.getType()))
      return true;
  if (mentionsPointer(F.getReturnType()))
    return true;
  for (const BasicBlock &BB : F)
    for (const Instruction &I : BB) {
      if (mentionsPointer(I.getType()) || I.mayReadOrWriteMemory()) {
        // Some intrinsics claim to touch memory only so they aren't moved around.
        if (const auto *C = dyn_cast<IntrinsicInst>(&I))
          switch (C->getIntrinsicID()) {
          case Intrinsic::assume:
            if (C->hasOperandBundles())
              return true;
            continue;
          case Intrinsic::donothing:
          case Intrinsic::sideeffect:
            continue;
          default:
            break;
          }
        else if (isa<CallBase>(I))
          continue;
        return true;
      }
      for (const Use &U : I.operands())
        if (U->getType()->isPointerTy() && !isa<Function>(U.get()))
          return true;
    }
  return false;
}

// Tarjan's algorithm over calls, where a call through a pointer might reach any function of its type
// whose address is taken. Callees come first in Lean, and this produces components with every callee
// before its callers. A component that can reach itself becomes a `mutual` block.
class CallGraphOrder {
public:
  std::vector<std::vector<Function *>> Components;
  std::set<const Function *> Recursive;

  explicit CallGraphOrder(Module &M) {
    for (Function &F : M)
      if (!F.isDeclaration() && F.hasAddressTaken())
        ByType[F.getFunctionType()].push_back(&F);
    for (Function &F : M)
      if (!F.isDeclaration() && !Index.count(&F))
        visit(&F);
  }

private:
  void visit(Function *F) {
    unsigned Mine = Index.size();
    Index[F] = Mine;
    LowLink[F] = Mine;
    Stack.push_back(F);
    OnStack.insert(F);
    auto Edge = [&](Function *Callee) {
      if (!Callee || Callee->isDeclaration())
        return;
      if (Callee == F)
        Recursive.insert(F);
      if (!Index.count(Callee))
        visit(Callee);
      if (OnStack.count(Callee))
        LowLink[F] = std::min(LowLink[F], LowLink[Callee]);
    };
    for (const BasicBlock &BB : *F)
      for (const Instruction &I : BB) {
        const auto *C = dyn_cast<CallBase>(&I);
        if (!C)
          continue;
        if (C->getCalledFunction()) {
          Edge(C->getCalledFunction());
          continue;
        }
        auto It = ByType.find(C->getFunctionType());
        if (It != ByType.end())
          for (Function *Target : It->second)
            Edge(Target);
      }
    if (LowLink[F] != Mine)
      return;
    std::vector<Function *> Component;
    Function *Member;
    do {
      Member = Stack.back();
      Stack.pop_back();
      OnStack.erase(Member);
      Component.push_back(Member);
    } while (Member != F);
    if (Component.size() > 1)
      Recursive.insert(Component.begin(), Component.end());
    Components.push_back(std::move(Component));
  }

  std::map<const FunctionType *, std::vector<Function *>> ByType;
  std::map<const Function *, unsigned> Index, LowLink;
  std::vector<Function *> Stack;
  std::set<const Function *> OnStack;
};

// Whether a declaration of a C library function only promises what `Mem`'s version of it does.
bool keepsItsPromises(const Function &F, bool ReadsArgument, bool WritesArgument, bool Allocates,
                      bool Frees) {
  if (!hasExactLinkage(F))
    return false;
  try {
    checkFunctionAttributes(F.getAttributes().getFnAttrs(), "function", /*Library=*/true);
  } catch (const Unsupported &) {
    return false;
  }
  MemoryEffects Effects = F.getMemoryEffects();
  if ((ReadsArgument && !isRefSet(Effects.getModRef(IRMemLocation::ArgMem))) ||
      (WritesArgument && !isModSet(Effects.getModRef(IRMemLocation::ArgMem))) ||
      (Allocates && !isModSet(Effects.getModRef(IRMemLocation::InaccessibleMem))) ||
      // `Mem.malloc` can fail, which writes `errno`.
      (F.getName() == "malloc" && !isModSet(Effects.getModRef(IRMemLocation::ErrnoMem))) ||
      (Frees && F.hasFnAttribute(Attribute::NoFree)))
    return false;
  auto Only = [](AttributeSet Attrs, std::initializer_list<Attribute::AttrKind> Allowed) {
    for (Attribute A : Attrs)
      if (A.isStringAttribute() || llvm::find(Allowed, A.getKindAsEnum()) == Allowed.end())
        return false;
    return true;
  };
  AttributeList Attrs = F.getAttributes();
  if (!Only(Attrs.getRetAttrs(), {Attribute::NoAlias, Attribute::NoUndef}))
    return false;
  AttributeSet Param = Attrs.getParamAttrs(0);
  if (F.getName() == "malloc")
    return Only(Param, {Attribute::NoUndef});
  if (F.getName() == "free")
    return Only(Param, {Attribute::NoUndef, Attribute::Captures, Attribute::AllocatedPointer});
  return Only(Param, {Attribute::NoUndef, Attribute::Captures, Attribute::ReadOnly, Attribute::NoFree});
}

// The Lean for a C library function the model knows, if `F` is one with its standard signature.
const char *libraryFunction(const Function &F) {
  LLVMContext &Context = F.getContext();
  Type *I64 = Type::getInt64Ty(Context);
  Type *Ptr = PointerType::getUnqual(Context);
  FunctionType *T = F.getFunctionType();
  if (!F.isDeclaration())
    return nullptr;
  if (F.getName() == "malloc" && T == FunctionType::get(Ptr, {I64}, false) &&
      keepsItsPromises(F, false, false, true, false))
    return "Mem.malloc";
  if (F.getName() == "free" && T == FunctionType::get(Type::getVoidTy(Context), {Ptr}, false) &&
      keepsItsPromises(F, false, true, true, true))
    return "Mem.free";
  if (F.getName() == "strlen" && T == FunctionType::get(I64, {Ptr}, false) &&
      keepsItsPromises(F, true, false, false, false))
    return "Mem.strlen";
  return nullptr;
}

} // namespace

bool isReservedName(const std::string &Name) { return reservedNames().count(Name) != 0; }

Emitted emitModule(Module &M, const std::string &Namespace, const std::string &SourceName, bool NoCode) {
  CallGraphOrder Order(M);
  ModuleContext Context(M, NoCode);
  std::set<const Function *> MemoryFunctions;
  // Functions whose run can make a choice, which take an `IRLean.Choice`: see `FunctionEmitter`.
  std::set<const Function *> ChoosingFunctions;

  NameTable FunctionNames;
  DenseMap<const Function *, std::string> LeanNames, Translated;
  std::map<const Function *, FunctionReport> Reports;
  for (Function &F : M) {
    if (!F.isDeclaration()) {
      LeanNames[&F] = FunctionNames.make(F.getName(), "f");
    } else if (const char *Library = libraryFunction(F)) {
      Translated[&F] = Library;
      MemoryFunctions.insert(&F);
    }
  }

  // Modules are files, and some filesystems ignore case.
  std::set<std::string> ModuleNames;
  auto uniqueModuleName = [&](const std::string &Name) {
    std::string Unique = Name;
    for (unsigned I = 1;; ++I) {
      if (ModuleNames.insert(StringRef(Unique).lower()).second)
        return Unique;
      Unique = Name + "_" + std::to_string(I);
    }
  };
  std::map<const Function *, std::string> ModuleOf;
  std::vector<Piece> Pieces;

  // What can call `free`, callees first. A call through a pointer can reach anything of its type in the
  // module, and stops the model otherwise.
  std::set<const Function *> ReachesFree;
  for (const std::vector<Function *> &Component : Order.Components) {
    bool Reaches = false;
    for (const Function *F : Component)
      for (const BasicBlock &BB : *F)
        for (const Instruction &I : BB) {
          const auto *C = dyn_cast<CallBase>(&I);
          if (!C)
            continue;
          if (const Function *Callee = C->getCalledFunction()) {
            Reaches |= Callee->getName() == "free" || ReachesFree.count(Callee);
            continue;
          }
          for (const Function *Target : Context.candidates(C->getFunctionType()))
            Reaches |= ReachesFree.count(Target) != 0;
        }
    if (Reaches)
      ReachesFree.insert(Component.begin(), Component.end());
  }

  std::string Body;
  for (const std::vector<Function *> &Component : Order.Components) {
    bool Recursive = Order.Recursive.count(Component.front());
    // A cycle where something promises to progress has its runs that never return judged as a whole, by a
    // function outside the `mutual` block: inside it, members call each other's raw functions.
    bool PromisedCycle =
        Recursive && any_of(Component, [](const Function *F) { return promisesProgress(*F); });
    // Members of a cycle call each other, so they must all be known before any is emitted.
    for (Function *F : Component)
      if (Recursive)
        Translated[F] = LeanNames.lookup(F) + (PromisedCycle ? ".raw" : "");

    // A function uses memory if it does so itself, or calls something that does. Members of a
    // cycle pass memory along for each other, so they share the answer.
    bool UsesMemory = false;
    for (const Function *F : Component) {
      UsesMemory |= usesMemoryDirectly(*F);
      for (const BasicBlock &BB : *F)
        for (const Instruction &I : BB)
          if (const auto *C = dyn_cast<CallBase>(&I))
            UsesMemory |= MemoryFunctions.count(C->getCalledFunction()) != 0;
    }
    if (UsesMemory)
      MemoryFunctions.insert(Component.begin(), Component.end());

    // A function chooses if it has a `freeze`, or calls something that does, through a pointer too. Members
    // of a cycle pass choices along for each other, so they share the answer.
    bool Chooses = false;
    for (const Function *F : Component)
      for (const BasicBlock &BB : *F)
        for (const Instruction &I : BB) {
          Chooses |= isa<FreezeInst>(I);
          const auto *C = dyn_cast<CallBase>(&I);
          if (!C)
            continue;
          if (const Function *Callee = C->getCalledFunction()) {
            Chooses |= ChoosingFunctions.count(Callee) != 0;
            continue;
          }
          for (const Function *Target : Context.candidates(C->getFunctionType()))
            Chooses |= ChoosingFunctions.count(Target) != 0;
        }
    if (Chooses)
      ChoosingFunctions.insert(Component.begin(), Component.end());

    std::vector<std::unique_ptr<FunctionEmitter>> Emitters;
    std::string Types, Loops, Functions, Wrappers, Failure;
    for (Function *F : Component) {
      Emitters.push_back(std::make_unique<FunctionEmitter>(*F, LeanNames.lookup(F), Recursive, PromisedCycle,
                                                           UsesMemory, Chooses, Translated, MemoryFunctions,
                                                           ChoosingFunctions, ReachesFree, Context));
      FunctionEmitter &E = *Emitters.back();
      try {
        E.prepare();
        Types += E.emitBlocks() + "\n";
        if (Recursive)
          Loops += E.emitLoop() + "\n";
        Functions += E.emitFunction() + "\n";
        if (PromisedCycle)
          Wrappers += E.emitPromisedCycleWrapper() + "\n";
      } catch (const Unsupported &U) {
        Failure = U.Why;
      }
      FunctionReport R;
      R.LLVMName = F->getName().str();
      R.LeanName = LeanNames.lookup(F);
      R.Signature = describeSignature(*F);
      R.Blocks = E.blockCount();
      R.Instructions = E.instructionCount();
      R.UsesMemory = UsesMemory;
      Reports[F] = std::move(R);
    }
    if (!Failure.empty()) {
      for (Function *F : Component) {
        Reports[F].Unsupported =
            Component.size() > 1 ? "in a cycle with a function that has " + Failure : Failure;
        Translated.erase(F);
      }
      continue;
    }
    for (Function *F : Component)
      Translated[F] = LeanNames.lookup(F);
    std::string Text =
        Types + (Recursive ? "mutual\n\n" + Loops + Functions + "end\n\n" + Wrappers : Functions);
    Body += Text;

    Piece P;
    P.Module = uniqueModuleName(LeanNames.lookup(Component.front()));
    P.Lean = std::move(Text);
    std::set<std::string> Imports;
    for (Function *F : Component) {
      ModuleOf[F] = P.Module;
      for (const BasicBlock &BB : *F)
        for (const Instruction &I : BB) {
          const auto *C = dyn_cast<CallBase>(&I);
          if (!C)
            continue;
          auto Need = [&](const Function *Callee) {
            auto It = ModuleOf.find(Callee);
            if (It != ModuleOf.end() && It->second != P.Module)
              Imports.insert(It->second);
          };
          if (const Function *Callee = C->getCalledFunction())
            Need(Callee);
          else
            for (const Function *Target : Context.candidates(C->getFunctionType()))
              Need(Target);
        }
    }
    P.Imports.assign(Imports.begin(), Imports.end());
    Pieces.push_back(std::move(P));
  }

  Emitted Out;
  for (Function &F : M)
    if (!F.isDeclaration())
      Out.Functions.push_back(Reports[&F]);

  Out.Lean = "-- Generated by ir-lean from " + SourceName + ". Do not edit.\n";
  for (const FunctionReport &R : Out.Functions)
    if (!R.Unsupported.empty()) {
      std::string Why = R.Unsupported;
      Why = Why.substr(0, Why.find('\n'));
      Out.Lean += "-- Left out @" + R.LLVMName + ": " + Why + "\n";
    }
  Out.Header = Out.Lean;
  Out.Lean +=
      "import IRLean\n\nopen IRLean\n\n"
      "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
      "set_option linter.unusedVariables false\n"
      // Proofs don't need these, and they are most of the cost of checking a large function.
      "set_option genInjectivity false\nset_option genSizeOf false\nset_option genSizeOfSpec false\n\n"
      "namespace " +
      Namespace + "\n\n" + Context.emitGlobals() + Body + "end " + Namespace + "\n";
  Out.Globals = Context.emitGlobals();
  Out.Pieces = std::move(Pieces);
  return Out;
}

} // namespace ir_lean
