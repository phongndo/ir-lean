#!/usr/bin/env python3
"""Tests of tests/llvm_rewrites.py, the inventory of chunk 1's rewrites, and of the rule it applies.

- The rule, on small C++ files: a forward isn't a site and makes its callee a fold; a name bound by a
matcher is a site; returning what a builder builds is the caller's site; a changed flag set to `true` is a
site and one or-ed with a fold's result is a forward; `Changed ? &I : nullptr` isn't one; a lambda a fold
forwards to is a fold; a function that declines and neither builds IR nor is forwarded to is a helper; a
driver that installs a fold's result isn't a site; and `if (fold(I)) return &I;` is a forward.
- The check, on a copy of the pinned source, if LLVM_PROJECT_SRC is set: removing a rewrite, adding one
and changing one are each reported, by ID, and the copy unchanged gives the recorded inventory exactly.

usage: tests/llvm_rewrites_test.py
"""

from __future__ import annotations

import os
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import llvm_rewrites as lr

TOY = """
namespace llvm {
static Constant *getFalse(Type *Ty) { return ConstantInt::getFalse(Ty); }

static Value *foldInner(Value *Op0, Value *Op1) {
  // X & 0 -> 0
  if (match(Op1, m_Zero()))
    return Op1;
  return nullptr;
}

static Value *findThing(Value *V) {
  if (auto *I = dyn_cast<Instruction>(V))
    return I->getOperand(0);
  return nullptr;
}

static bool changeInPlace(Instruction &I) {
  if (I.getNumOperands() == 2) {
    I.setOperand(0, I.getOperand(1));
    return true;
  }
  return false;
}

Value *visitToy(Instruction &I) {
  Value *Op0 = I.getOperand(0), *Op1 = I.getOperand(1);
  bool Changed = false;
  if (Value *V = foldInner(Op0, Op1))
    return V;
  // Y - X + X -> Y
  Value *Y = nullptr;
  if (match(Op0, m_Sub(m_Value(Y), m_Specific(Op1))))
    return Y;
  // X < X -> false
  if (Op0 == Op1)
    return getFalse(I.getType());
  auto Simplify = [&](Value *X) -> Value * {
    if (match(X, m_AllOnes()))
      return X;
    return nullptr;
  };
  if (Value *R = Simplify(Op1))
    return R;
  if (changeInPlace(I))
    return &I;
  if (Value *T = findThing(Op0))
    return Builder.CreateNot(T);
  if (I.hasNoSignedWrap()) {
    I.setHasNoSignedWrap(false);
    Changed = true;
  }
  Changed |= changeInPlace(I);
  return Changed ? &I : nullptr;
}

Value *visitShadow(Instruction &I) {
  if (Value *X = foldInner(I.getOperand(0), I.getOperand(1)))
    return X;
  Value *X = nullptr;
  if (match(I.getOperand(0), m_Not(m_Value(X))))
    return X;
  auto Hint = [&](Use &U) {
    if (U.get() != X)
      replaceUse(U, X);
  };
  Hint(I.getOperandUse(0));
  return nullptr;
}

Value *visitGeneric(Instruction &I) {
  if (isa<FPMathOperator>(I) && !I.hasNoNaNs())
    return nullptr;
  if (I.getOperand(0) == I.getOperand(1))
    return I.getOperand(0);
  const APInt *C;
  if (match(I.getOperand(1), m_APInt(C)))
    return I.getOperand(1);
  return nullptr;
}

static Instruction *lookupJ(Value *V) {
  if (auto *J = dyn_cast<Instruction>(V))
    return J;
  return nullptr;
}

Value *visitNegate(Instruction &I) {
  if (Instruction *J = lookupJ(I.getOperand(0))) {
    J->setOperand(0, I.getOperand(1));
    return J;
  }
  return nullptr;
}

static bool foldTop(Instruction &I) {
  if (!match(I.getOperand(0), m_Zero()))
    return false;
  I.setOperand(0, I.getOperand(1));
  return true;
}

static bool setFlags(Instruction &I) {
  bool Changed = I.getOperand(0) == I.getOperand(1);
  I.setIsExact(Changed);
  return Changed;
}

static Instruction *foldPtr(Instruction &I) {
  auto *P = dyn_cast<IntToPtrInst>(I.getOperand(0));
  if (!P)
    return nullptr;
  I.setOperand(0, P->getOperand(0));
  return &I;
}

bool runToy(Function &F) {
  bool Changed = false;
  for (Instruction &I : F) {
    if (Value *V = visitToy(I)) {
      I.replaceAllUsesWith(V);
      Changed = true;
    }
    if (isDead(&I)) {
      I.eraseFromParent();
      Changed = true;
    }
  }
  return Changed;
}
}
"""

TOY_PASSES = {
    "toy": {
        "prefix": "T",
        "files": ["lib/Toy.cpp"],
        "entries": ["runToy", "visitToy", "visitShadow", "visitGeneric", "visitNegate"],
    }
}


def toy_inventory(tmp: Path, source: str) -> dict:
    (tmp / "lib").mkdir(parents=True, exist_ok=True)
    (tmp / "lib" / "Toy.cpp").write_text(source)
    return lr.inventory(tmp, TOY_PASSES)["toy"]


def line_of(source: str, needle: str, nth: int = 1) -> int:
    seen = 0
    for n, ln in enumerate(source.splitlines(), 1):
        if needle in ln:
            seen += 1
            if seen == nth:
                return n
    raise AssertionError(f"no {needle!r}")


def test_rule(failures: list[str]) -> None:
    with tempfile.TemporaryDirectory() as d:
        inv = toy_inventory(Path(d), TOY)
    sites = {(r["function"], r["line"]) for r in inv["rewrites"]}
    want = {
        ("foldInner", line_of(TOY, "return Op1;")),  # reached by a forward
        ("visitToy", line_of(TOY, "return Y;")),  # bound by a matcher
        ("visitToy", line_of(TOY, "return getFalse(")),  # returns what a builder builds
        ("visitToy::Simplify", line_of(TOY, "return X;")),  # a lambda forwarded to
        ("visitToy", line_of(TOY, "return Builder.CreateNot(T);")),  # a helper's result, used to build
        ("visitToy", line_of(TOY, "Changed = true;")),  # a flag
        ("changeInPlace", line_of(TOY, "return true;")),  # a bool fold that changes IR
        ("runToy", line_of(TOY, "Changed = true;", 3)),  # the driver's dead-code erase
        # A name an `if` binds to a fold's result is that `if`'s alone: the matcher's `X` after it is a site.
        ("visitShadow", line_of(TOY, "return X;", 3)),
        # A change committed with no return or flag after it.
        ("visitShadow::Hint", line_of(TOY, "replaceUse(U, X);")),
        ("visitGeneric", line_of(TOY, "return I.getOperand(0);")),
        ("visitGeneric", line_of(TOY, "return I.getOperand(1);")),
        # A change to what a lookup found, before `return` forwards it: the change is the site.
        ("visitNegate", line_of(TOY, "J->setOperand(0, I.getOperand(1));")),
        ("lookupJ", line_of(TOY, "return J;")),
        # A change at the top of a function, committed by the `return true` after it: one site.
        ("foldTop", line_of(TOY, "return true;", 2)),
        # A returned flag isn't a site, so it doesn't commit the change before it.
        ("setFlags", line_of(TOY, "I.setIsExact(Changed);")),
        # The change and the return after it are one site, which needs what the statements before them read.
        ("foldPtr", line_of(TOY, "return &I;", 2)),
    }
    for w in sorted(want - sites):
        failures.append(f"rule: expected a site at {w}")
    for s in sorted(sites - want):
        failures.append(f"rule: unexpected site at {s}")
    folds = {f["function"]: f["why"] for f in inv["folds"]}
    for name, why in (
        ("foldInner", "forwarded"),
        ("visitToy::Simplify", "forwarded"),
        ("changeInPlace", "builds"),
    ):
        if folds.get(name) != why:
            failures.append(f"rule: {name} should be a fold, {why}, not {folds.get(name)}")
    if "findThing" not in inv["helpers"]:
        failures.append(f"rule: findThing should be a helper, not a fold: {inv['helpers']}")
    if "getFalse" not in inv["builders"]:
        failures.append(f"rule: getFalse should be a builder: {inv['builders']}")
    needs = {r["line"]: r["needs"] for r in inv["rewrites"]}
    # A function that handles floating point rewrites it too, unless the path says integer.
    if needs.get(line_of(TOY, "return I.getOperand(0);")) != ["fp"]:
        failures.append(
            f"rule: a generic site should need fp: {needs.get(line_of(TOY, 'return I.getOperand(0);'))}"
        )
    if needs.get(line_of(TOY, "return I.getOperand(1);")) != ["int"]:
        failures.append("rule: a site behind m_APInt is integers only")
    if needs.get(line_of(TOY, "return &I;", 2)) != ["memory"]:
        failures.append(
            f"rule: a site after an inttoptr should need memory: {needs.get(line_of(TOY, 'return &I;', 2))}"
        )
    kinds = {r["line"]: r["kind"] for r in inv["rewrites"]}
    if kinds.get(line_of(TOY, "replaceUse(U, X);")) != "change":
        failures.append("rule: a lone replaceUse should be a change site")
    ids = [r["id"] for r in inv["rewrites"]]
    if len(set(ids)) != len(ids):
        failures.append(f"rule: IDs aren't unique: {ids}")


REASSOCIATE = """
namespace llvm {
void ReassociatePass::canonicalizeOperands(Instruction *I) {
  Value *LHS = I->getOperand(0);
  Value *RHS = I->getOperand(1);
  if (LHS == RHS || isa<Constant>(RHS))
    return;
  if (isa<Constant>(LHS) || getRank(RHS) < getRank(LHS)) {
    cast<BinaryOperator>(I)->swapOperands();
    MadeChange = true;
  }
}

PreservedAnalyses ReassociatePass::run(Function &F) {
  for (Instruction &I : F)
    if (I.isCommutative())
      canonicalizeOperands(&I);
  return PreservedAnalyses::none();
}
}
"""


def test_generic_pass(failures: list[str]) -> None:
    """Reassociate serves floating point as well as integers throughout, so a site in it with no integer guard
    needs floating point, though its own function never mentions it."""
    rel = "lib/Transforms/Scalar/Reassociate.cpp"
    passes = {"ra": {"prefix": "RA", "files": [rel], "entries": ["ReassociatePass::run"]}}
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / rel).parent.mkdir(parents=True)
        (Path(d) / rel).write_text(REASSOCIATE)
        rows = lr.inventory(Path(d), passes)["ra"]["rewrites"]
    got = [(r["function"], r["needs"]) for r in rows]
    if got != [("ReassociatePass::canonicalizeOperands", ["fp"])]:
        failures.append(f"generic pass: canonicalizeOperands should need fp, got {got}")


INTRINSICS = """
namespace llvm {
static Value *simplifyToyIntrinsic(Intrinsic::ID IID, Value *Op0, Value *Op1, FastMathFlags FMF) {
  switch (IID) {
  case Intrinsic::umax:
    // umax(X, X) -> X
    if (Op0 == Op1)
      return Op0;
    break;
  case Intrinsic::minnum:
    // minnum(X, X) -> X
    if (Op0 == Op1)
      return Op1;
    break;
  case Intrinsic::fabs:
    if (FMF.noNaNs())
      return Op0;
    [[fallthrough]];
  case Intrinsic::ctpop:
    // ctpop(0) -> 0, and fabs(0) -> 0 with it
    if (match(Op0, m_Zero()))
      return Op0;
    break;
  default:
    break;
  }
  return nullptr;
}

static Value *foldToyShared(Intrinsic::ID IID, Value *Op0, Value *Op1) {
  if (IID != Intrinsic::not_intrinsic && Op0 == Op1)
    return Op1;
  return nullptr;
}

Instruction *visitToyCall(CallInst &CI) {
  Value *Op0 = CI.getArgOperand(0);
  switch (CI.getIntrinsicID()) {
  case Intrinsic::smin:
    // smin(X, X) -> X
    if (Op0 == CI.getArgOperand(1))
      return replaceInstUsesWith(CI, Op0);
    break;
  case Intrinsic::copysign:
    if (isa<ConstantFP>(Op0))
      return replaceInstUsesWith(CI, Op0);
    break;
  default:
    break;
  }
  return nullptr;
}

static Value *simplifyToyDefault(Intrinsic::ID IID, Value *Op0, FastMathFlags FMF) {
  switch (IID) {
  default:
  case Intrinsic::ctpop:
    if (match(Op0, m_Zero()))
      return ToyDefaultFirst;
    break;
  }
  switch (IID) {
  default:
    if (FMF.noNaNs())
      break;
    [[fallthrough]];
  case Intrinsic::ctlz:
    if (match(Op0, m_Zero()))
      return ToyDefaultSecond;
    break;
  }
  return nullptr;
}

Instruction *visitToyAssume(IntrinsicInst *II) {
  switch (II->getIntrinsicID()) {
  case Intrinsic::assume: {
    for (auto [Idx, OBU] : llvm::enumerate(II->operand_bundles())) {
      switch (getBundleAttrFromOBU(OBU)) {
      case BundleAttr::Align: {
        auto [Ptr, _, OffsetPtr, Alignment, Offset] = getAssumeAlignInfo(OBU);
        if (*Alignment == 1)
          return ToyRemoveAlign;
        break;
      }
      case BundleAttr::NoUndef:
        return ToyRemoveNoUndef;
      }
    }
    if (II->hasOperandBundles())
      break;
    if (isa<ConstantInt>(II->getArgOperand(0)))
      return ToyEraseAssume;
    break;
  }
  default:
    break;
  }
  return nullptr;
}
}
"""


def test_intrinsic_cases(failures: list[str]) -> None:
    """A case label naming an integer intrinsic says the site's values are integers, in a function that takes
    floating point for its other intrinsics, through a `FastMathFlags` parameter or by naming it; a
    floating-point intrinsic's case, or one falling through into an integer one, stays floating point; and
    `Intrinsic::ID` and `Intrinsic::not_intrinsic` aren't intrinsics, so they don't make a site a call. A
    `default` label reaching a case says nothing of the intrinsic, and operand bundles make a site a call."""
    passes = {
        "toy": {
            "prefix": "T",
            "files": ["lib/Toy.cpp"],
            "entries": [
                "simplifyToyIntrinsic",
                "foldToyShared",
                "visitToyCall",
                "simplifyToyDefault",
                "visitToyAssume",
            ],
        }
    }
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "lib").mkdir()
        (Path(d) / "lib" / "Toy.cpp").write_text(INTRINSICS)
        rows = lr.inventory(Path(d), passes)["toy"]["rewrites"]
    got = {r["line"]: (r["needs"], r["intrinsics"]) for r in rows}
    want = {
        # Under `case Intrinsic::umax:`, in a function that also takes `minnum` and its `FastMathFlags`.
        line_of(INTRINSICS, "return Op0;"): (["int"], ["umax"]),
        line_of(INTRINSICS, "return Op1;"): (["fp"], ["minnum"]),
        line_of(INTRINSICS, "return Op0;", 2): (["fp"], ["fabs"]),
        # `fabs` falls through into `ctpop`, so the site sees floating point too.
        line_of(INTRINSICS, "return Op0;", 3): (["fp"], ["ctpop"]),
        # Only `Intrinsic::ID` and `Intrinsic::not_intrinsic` on its path: no intrinsic, and no call.
        line_of(INTRINSICS, "return Op1;", 2): (["int"], []),
        # A visit method that names floating point, under `case Intrinsic::smin:`.
        line_of(INTRINSICS, "return replaceInstUsesWith(CI, Op0);"): (["int"], ["smin"]),
        # Its path names `CallInst` and an intrinsic that isn't an integer one, so it's a call too.
        line_of(INTRINSICS, "return replaceInstUsesWith(CI, Op0);", 2): (["fp", "calls"], ["copysign"]),
        # A `default` label reaches each of these, with any intrinsic, so `FastMathFlags` counts.
        line_of(INTRINSICS, "return ToyDefaultFirst;"): (["fp"], ["ctpop"]),
        line_of(INTRINSICS, "return ToyDefaultSecond;"): (["fp"], ["ctlz"]),
        # `llvm.assume`'s operand bundles aren't in the model, and "align" carries a pointer.
        line_of(INTRINSICS, "return ToyRemoveAlign;"): (["memory", "calls"], ["assume"]),
        line_of(INTRINSICS, "return ToyRemoveNoUndef;"): (["calls"], ["assume"]),
        # Past `if (II->hasOperandBundles()) break;`, an assume of an `i1` constant.
        line_of(INTRINSICS, "return ToyEraseAssume;"): (["int"], ["assume"]),
    }
    for line, w in sorted(want.items()):
        if got.get(line) != w:
            failures.append(
                f"intrinsic cases: line {line} should need {w[0]} with {w[1]}, got {got.get(line)}"
            )
    for line in sorted(set(got) - set(want)):
        failures.append(f"intrinsic cases: unexpected site at line {line}: {got[line]}")


def mutate(src: Path, tmp: Path, rel: str, old: str, new: str) -> Path:
    """A copy of the passes' files under `tmp`, with `old` replaced by `new` once in `rel`, line for line."""
    root = tmp / "llvm"
    for spec in lr.PASSES.values():
        files = spec["files"]
        rels = (
            [str(x.relative_to(src)) for x in (src / files.rsplit("/", 1)[0]).glob(files.rsplit("/", 1)[1])]
            if isinstance(files, str)
            else files
        )
        for r in rels:
            (root / r).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src / r, root / r)
    if old:
        text = (root / rel).read_text()
        assert text.count(old) >= 1, old
        (root / rel).write_text(text.replace(old, new, 1))
    return root


def test_check(failures: list[str]) -> bool:
    """The mutation check against the pinned source. Returns whether it ran, so a skip isn't reported as a
    pass. Needs the dev shell for LLVM_PROJECT_SRC; ctest always has it."""
    env = os.environ.get("LLVM_PROJECT_SRC")
    if not env:
        print(
            "skipped the check against the pinned source: LLVM_PROJECT_SRC isn't set, so not in the dev shell"
        )
        return False
    src = lr.source()
    recorded = {p: lr.load(lr.HERE / f"{p}.json") for p in lr.PASSES}
    simplify = "lib/Analysis/InstructionSimplify.cpp"
    cases = [
        ("unchanged", simplify, "", "", []),
        # X + 0 -> X, at InstructionSimplify.cpp:609, no longer folds.
        (
            "removed",
            simplify,
            "  if (match(Op1, m_Zero()))\n    return Op0;\n\n  // If two operands are negative",
            "  if (match(Op1, m_Zero()))\n    return nullptr;\n\n  // If two operands are negative",
            ["instsimplify: rewrite IS.simplifyAddInst.L609 is gone"],
        ),
        # X & -1 -> X returns Op1 instead: the same site, changed.
        (
            "changed",
            simplify,
            "  if (match(Op1, m_AllOnes()))\n    return Op0;",
            "  if (match(Op1, m_AllOnes()))\n    return Op1;",
            ["instsimplify: rewrite IS.simplifyAndInst.L2094 changed: code, hash"],
        ),
        # A new rewrite where InstCombine's checkForNegativeOperand gave up, at InstCombineAddSub.cpp:759.
        (
            "added",
            "lib/Transforms/InstCombine/InstCombineAddSub.cpp",
            "  if (!LHS->hasOneUse() && !RHS->hasOneUse())\n    return nullptr;\n\n  Value *X = nullptr",
            "  if (!LHS->hasOneUse() && !RHS->hasOneUse())\n    return LHS;\n\n  Value *X = nullptr",
            ["instcombine: new rewrite IC.AddSub.checkForNegativeOperand.L759"],
        ),
    ]
    for name, rel, old, new, expect in cases:
        with tempfile.TemporaryDirectory() as d:
            root = mutate(src, Path(d), rel, old, new)
            derived = lr.inventory(root)
        got = [
            g
            for g in lr.differences(recorded, derived)
            # The mutated file's hash changes, which the file list records: that's expected of every mutation.
            if not g.endswith(": files differs from what the source gives")
        ]
        got_short = [g.split(" at ")[0].split(" from ")[0] for g in got]
        if got_short != expect:
            failures.append(f"check, {name}: expected {expect}, got {got}")
    return True


def main() -> int:
    failures: list[str] = []
    test_rule(failures)
    test_generic_pass(failures)
    test_intrinsic_cases(failures)
    ran_check = test_check(failures)
    for f in failures:
        print(f"FAIL {f}")
    if failures:
        print(f"{len(failures)} failures")
        return 1
    print("ok" if ran_check else "ok, but the check against the pinned source was skipped")
    return 0


if __name__ == "__main__":
    sys.exit(main())
