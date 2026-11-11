// ir-lean: prints LLVM IR as Lean.

#include "Emitter.h"

#include "llvm/ADT/SmallString.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <cctype>
#include <memory>
#include <string>

using namespace llvm;

namespace {

enum ExitCode { ExitOk = 0, ExitError = 1, ExitUsage = 2, ExitSomeUnsupported = 3 };

void printUsage(raw_ostream &OS) {
  OS << R"(usage: ir-lean <input.ll|input.bc> [options]

Prints the functions in an LLVM module as Lean, against the semantics in the
IRLean library. Functions the semantics can't model yet are left out, and
named on stderr.

options:
  -o FILE           where to write the Lean (default: stdout)
  --namespace NAME  Lean namespace for the module (default: from the input name)
  --report          print one line per function instead of Lean
  --split DIR       write one Lean module per function under DIR/NAME, and DIR/NAME.lean
                    importing them in dependency order
  --no-code         don't have Lean generate code, so the output checks far faster but can
                    only be proved about, not run
  --executable-memory
                    the same Lean, with IRLean.ExecMem in place of IRLean.Mem, for running tests:
                    each operation on memory is proved to agree with Mem's, and runs far faster

exit codes:
  0  every function was translated
  1  error
  2  bad arguments
  3  some functions were left out
)";
}

std::string defaultNamespace(StringRef Input) {
  std::string Name;
  for (char C : sys::path::stem(Input))
    Name += std::isalnum(static_cast<unsigned char>(C)) ? C : '_';
  if (Name.empty() || std::isdigit(static_cast<unsigned char>(Name[0])) || ir_lean::isReservedName(Name))
    Name = "m" + Name;
  return Name;
}

// Whether `C` can be part of a Lean identifier, apart from the dots between its components.
bool identifierChar(char C) {
  return std::isalnum(static_cast<unsigned char>(C)) || C == '_' || C == '\'' || C == '!' || C == '?' ||
         static_cast<unsigned char>(C) >= 0x80;
}

// The same Lean with every `Mem` that names IRLean's memory, the type or its namespace, as `ExecMem`. Emitted
// names never are `Mem` or `ExecMem`, which are reserved, so a whole word `Mem` is always IRLean's.
std::string executableMemory(const std::string &Lean) {
  std::string Out;
  Out.reserve(Lean.size() + Lean.size() / 16);
  for (size_t I = 0; I < Lean.size(); ++I) {
    if (Lean.compare(I, 3, "Mem") == 0 && (I == 0 || !identifierChar(Lean[I - 1])) &&
        (I + 3 == Lean.size() || !identifierChar(Lean[I + 3]))) {
      Out += "ExecMem";
      I += 2;
    } else {
      Out += Lean[I];
    }
  }
  return Out;
}

} // namespace

int main(int Argc, char **Argv) {
  std::string Input, Output, Namespace, SplitDir;
  bool Report = false, NoCode = false, Executable = false;
  for (int I = 1; I < Argc; ++I) {
    StringRef A = Argv[I];
    auto Value = [&](const char *Flag) -> std::string {
      if (++I >= Argc) {
        errs() << "ir-lean: " << Flag << " needs a value\n";
        std::exit(ExitUsage);
      }
      return Argv[I];
    };
    if (A == "-o") {
      Output = Value("-o");
    } else if (A == "--namespace") {
      Namespace = Value("--namespace");
    } else if (A == "--report") {
      Report = true;
    } else if (A == "--split") {
      SplitDir = Value("--split");
    } else if (A == "--no-code") {
      NoCode = true;
    } else if (A == "--executable-memory") {
      Executable = true;
    } else if (A == "-h" || A == "--help") {
      printUsage(outs());
      return ExitOk;
    } else if (A.starts_with("-")) {
      errs() << "ir-lean: unknown option " << A << "\n";
      printUsage(errs());
      return ExitUsage;
    } else if (Input.empty()) {
      Input = A.str();
    } else {
      printUsage(errs());
      return ExitUsage;
    }
  }
  if (Input.empty()) {
    printUsage(errs());
    return ExitUsage;
  }
  if (Namespace.empty())
    Namespace = defaultNamespace(Input);
  // `--executable-memory` renames every whole word `Mem`, so a namespace with `Mem` or `ExecMem` in it would
  // change too, or clash with IRLean's.
  if (Executable) {
    for (StringRef Rest = Namespace; !Rest.empty();) {
      auto [Part, Tail] = Rest.split('.');
      if (Part == "Mem" || Part == "ExecMem") {
        errs() << "ir-lean: --executable-memory can't take the namespace " << Namespace << ", which names "
               << Part << "\n";
        return ExitUsage;
      }
      Rest = Tail;
    }
  }

  LLVMContext Context;
  SMDiagnostic Diagnostic;
  std::unique_ptr<Module> M = parseIRFile(Input, Diagnostic, Context);
  if (!M) {
    Diagnostic.print("ir-lean", errs());
    return ExitError;
  }
  // The parser accepts IR that LLVM's verifier rejects, such as `llvm.lifetime.start` on a global, and the
  // model gives such IR a meaning LLVM doesn't. Broken debug info is only dropped, as `opt` does, since
  // nothing here reads it.
  bool BrokenDebugInfo = false;
  if (verifyModule(*M, &errs(), &BrokenDebugInfo)) {
    errs() << "ir-lean: " << Input << " doesn't pass LLVM's verifier\n";
    return ExitError;
  }
  if (BrokenDebugInfo) {
    errs() << "ir-lean: warning: ignoring invalid debug info in " << Input << "\n";
    StripDebugInfo(*M);
  }

  ir_lean::Emitted E = ir_lean::emitModule(*M, Namespace, sys::path::filename(Input).str(), NoCode);
  if (Executable) {
    E.Lean = executableMemory(E.Lean);
    E.Globals = executableMemory(E.Globals);
    for (ir_lean::Piece &P : E.Pieces)
      P.Lean = executableMemory(P.Lean);
  }

  unsigned Translated = 0;
  for (const ir_lean::FunctionReport &F : E.Functions)
    Translated += F.Unsupported.empty();
  bool AllTranslated = Translated == E.Functions.size();

  if (Report) {
    for (const ir_lean::FunctionReport &F : E.Functions) {
      if (F.Unsupported.empty())
        outs() << "ok\t" << F.LLVMName << "\t" << F.LeanName << "\t" << F.Signature << "\t" << F.Blocks
               << "\t" << F.Instructions << "\t" << (F.UsesMemory ? "memory" : "pure") << "\n";
      else
        outs() << "unsupported\t" << F.LLVMName << "\t" << StringRef(F.Unsupported).split('\n').first << "\n";
    }
    outs() << "translated " << Translated << "/" << E.Functions.size() << "\n";
    return ExitOk;
  }

  for (const ir_lean::FunctionReport &F : E.Functions)
    if (!F.Unsupported.empty())
      errs() << "ir-lean: left out @" << F.LLVMName << ": " << StringRef(F.Unsupported).split('\n').first
             << "\n";

  if (!SplitDir.empty()) {
    SmallString<128> Dir(SplitDir);
    sys::path::append(Dir, Namespace);
    if (std::error_code EC = sys::fs::create_directories(Dir)) {
      errs() << "ir-lean: can't create " << Dir << ": " << EC.message() << "\n";
      return ExitError;
    }
    auto Write = [&](const Twine &Path, const std::string &Text) {
      std::error_code EC;
      raw_fd_ostream OS(Path.str(), EC, sys::fs::OF_Text);
      if (EC) {
        errs() << "ir-lean: can't write " << Path << ": " << EC.message() << "\n";
        std::exit(ExitError);
      }
      OS << Text;
    };
    const std::string Options = "open IRLean\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
                                "set_option linter.unusedVariables false\n"
                                "set_option genInjectivity false\nset_option genSizeOf false\nset_option "
                                "genSizeOfSpec false\n\nnamespace " +
                                Namespace + "\n\n";
    const std::string Close = "end " + Namespace + "\n";
    Write(Twine(Dir) + "/Globals.lean", E.Header + "import IRLean\n\n" + Options + E.Globals + Close);
    std::string All = E.Header + "import " + Namespace + ".Globals\n";
    for (const ir_lean::Piece &P : E.Pieces) {
      std::string Imports = "import IRLean\nimport " + Namespace + ".Globals\n";
      for (const std::string &I : P.Imports)
        Imports += "import " + Namespace + "." + I + "\n";
      Write(Twine(Dir) + "/" + P.Module + ".lean", Imports + "\n" + Options + P.Lean + Close);
      All += "import " + Namespace + "." + P.Module + "\n";
    }
    Write(Twine(SplitDir) + "/" + Namespace + ".lean", All);
  } else if (Output.empty()) {
    outs() << E.Lean;
  } else {
    std::error_code EC;
    raw_fd_ostream OS(Output, EC, sys::fs::OF_Text);
    if (EC) {
      errs() << "ir-lean: can't write " << Output << ": " << EC.message() << "\n";
      return ExitError;
    }
    OS << E.Lean;
  }
  return AllTranslated ? ExitOk : ExitSomeUnsupported;
}
