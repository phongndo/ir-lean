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

TOY_PASSES = {"toy": {"prefix": "T", "files": ["lib/Toy.cpp"], "entries": ["runToy", "visitToy"]}}


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
    ids = [r["id"] for r in inv["rewrites"]]
    if len(set(ids)) != len(ids):
        failures.append(f"rule: IDs aren't unique: {ids}")


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


def test_check(failures: list[str]) -> None:
    env = os.environ.get("LLVM_PROJECT_SRC")
    if not env:
        print(
            "skipped the check against the pinned source: LLVM_PROJECT_SRC isn't set, so not in the dev shell"
        )
        return
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


def main() -> int:
    failures: list[str] = []
    test_rule(failures)
    test_check(failures)
    for f in failures:
        print(f"FAIL {f}")
    print("ok" if not failures else f"{len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
