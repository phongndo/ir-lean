// Emit the eight vector results of each changed round as functions for the Lean slice proofs.
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <set>

using namespace llvm;

static void slices(Function &fn, unsigned region, int first, int last, StringRef side, StringRef dir) {
  ModuleSlotTracker slots(fn.getParent());
  slots.incorporateFunction(fn);
  std::map<int, Value *> values;
  std::map<Value *, int> ids;
  for (BasicBlock &bb : fn)
    for (Instruction &inst : bb) {
      int slot = slots.getLocalSlot(&inst);
      if (slot >= 0) {
        values.emplace(slot, &inst);
        ids.emplace(&inst, slot);
      }
    }
  if (!values.count(first) || !values.count(last))
    report_fatal_error("missing Argon2 region");
  auto *begin = cast<Instruction>(values.at(first));
  auto *end = cast<Instruction>(values.at(last));
  if (begin->getParent() != end->getParent() || !begin->comesBefore(end))
    report_fatal_error("region crosses a block boundary");

  std::vector<Instruction *> body;
  std::set<Instruction *> members;
  for (auto it = begin->getIterator();; ++it) {
    Instruction &inst = *it;
    if (!isa<StoreInst>(inst)) {
      const auto *call = dyn_cast<IntrinsicInst>(&inst);
      if (!(isa<BinaryOperator>(inst) || isa<ShuffleVectorInst>(inst) ||
            (call && call->getIntrinsicID() == Intrinsic::fshl)))
        report_fatal_error("unexpected operation in Argon2 round");
      body.push_back(&inst);
      members.insert(&inst);
    }
    if (&inst == end)
      break;
  }
  std::set<int> inputs;
  std::vector<Instruction *> outputs;
  for (auto *inst : body) {
    for (Value *v : inst->operand_values())
      if (!isa<Constant>(v) && !members.count(dyn_cast<Instruction>(v)))
        inputs.insert(ids.at(v));
    if (llvm::any_of(inst->users(), [&](User *u) { return !members.count(dyn_cast<Instruction>(u)); }))
      outputs.push_back(inst);
  }
  if (inputs.size() != 8 || outputs.size() != 8)
    report_fatal_error("expected eight input and eight output vectors");
  for (auto &[id, v] : values)
    v->setName("v" + std::to_string(id));

  std::error_code ec;
  std::string prefix = "r" + std::to_string(region);
  raw_fd_ostream os((dir + "/" + prefix + "." + side + ".ll").str(), ec);
  if (ec)
    report_fatal_error(StringRef(ec.message()));
  for (unsigned i = 0; i < outputs.size(); ++i) {
    os << "define <8 x i64> @" << prefix << "_o" << i << "_" << side << "(";
    interleaveComma(inputs, os, [&](int id) { values.at(id)->printAsOperand(os, true); });
    os << ") {\n";
    for (auto *inst : body)
      os << *inst << "\n";
    os << "  ret ";
    outputs[i]->printAsOperand(os, true);
    os << "\n}\n";
  }
  for (auto &[id, v] : values)
    v->setName("");
}

int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  LLVMContext context;
  SMDiagnostic error;
  auto module = parseIRFile(argv[1], error, context);
  if (!module) {
    error.print(argv[0], errs());
    return 1;
  }
  auto *segment = module->getFunction("argon2_fill_segment_avx512f");
  auto *block = module->getFunction("fill_block_with_xor");
  if (!segment || !block)
    return 1;
  slices(*segment, 0, 354, 431, argv[2], argv[3]);
  slices(*segment, 1, 522, 599, argv[2], argv[3]);
  slices(*block, 2, 204, 281, argv[2], argv[3]);
  slices(*block, 3, 373, 450, argv[2], argv[3]);
}
