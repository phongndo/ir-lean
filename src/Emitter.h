// Prints an LLVM module as Lean, against the semantics in IRLean/.
#pragma once

#include "llvm/IR/Module.h"

#include <string>
#include <vector>

namespace ir_lean {

struct FunctionReport {
  std::string LLVMName;
  std::string LeanName;
  // For example `(i32,i32)->i32`.
  std::string Signature;
  // Why the function was left out, or empty if it was translated.
  std::string Unsupported;
  // With `Survey`, for a function left out: every reason the checks found, its own first, then, for each
  // function it calls or shares a cycle with that's left out, `call to @NAME, which isn't translated`,
  // `indirect call that can reach @NAME, which isn't translated` or `in a cycle with @NAME, which isn't
  // translated`. An instruction gives one reason at most. `SurveyComplete` is false when a refusal in a
  // step that makes several checks left the rest unmade.
  std::vector<std::string> Reasons;
  bool SurveyComplete = true;
  unsigned Blocks = 0;
  unsigned Instructions = 0;
  // Whether the Lean function takes and returns memory.
  bool UsesMemory = false;
};

// Part of the output as its own Lean module: a function, or functions that call each other.
struct Piece {
  std::string Module;
  std::string Lean;
  // Other pieces' `Module`s this one needs, besides the globals.
  std::vector<std::string> Imports;
};

struct Emitted {
  // Everything as one module.
  std::string Lean;
  // The same as separate modules, callees first, which takes far less memory to check.
  std::string Header;
  std::string Globals;
  std::vector<Piece> Pieces;
  std::vector<FunctionReport> Functions;
};

// With `NoCode`, Lean doesn't generate code for the output, which then checks far faster but can only
// be proved about, not run. `Survey` fills each left-out function's `Reasons`, and changes nothing else.
Emitted emitModule(llvm::Module &M, const std::string &Namespace, const std::string &SourceName,
                   bool NoCode = false, bool Survey = false);

// Whether Lean, or the code this emits, already uses this name.
bool isReservedName(const std::string &Name);

} // namespace ir_lean
