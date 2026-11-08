# Connecting a proof to LLVM's C++

One foothold between a theorem here and the C++ of an LLVM pass: `simplifyAddInst`, the function InstSimplify calls
on every integer `add`, at the pinned llvm-project. It's restated as a Lean function, that function is proved right at
every width, and the restatement is checked against the pinned source and the pinned `opt`. The restatement itself is
manual, so this is a translation someone can audit line by line, not a proof about the C++. For what any theorem here
means, see [trust](trust.md). For binding a single run of a pass, see [binding](llvm-proof-binding.md).

Facts here were checked on top of commit `4cd91e5` on 2026-11-08, on x86-64 Linux in the dev shell, with LLVM 23.1.3
and Lean 4.35.0.

## What's established

| Layer | Says | Kind of evidence | Where |
| --- | --- | --- | --- |
| The model is right | Every value the model returns refines the `add` it replaces, at every width, with any flags | A Lean theorem, on the standard axioms only, replayed by `leanchecker` | `simplifyAddInst_sound` in [`SimplifyAddSound.lean`](../tests/cpp_correspondence/SimplifyAddSound.lean) |
| The model is the source | Each step of [`SimplifyAddModel.lean`](../tests/cpp_correspondence/SimplifyAddModel.lean) is the C++ it quotes | A manual translation. The quotes are checked: each is at its line of a file with the pinned SHA-256, and every code line of the three functions modelled is quoted | [`anchors.json`](../tests/cpp_correspondence/anchors.json) |
| The model is the binary | The model's answer is what `opt -passes=instsimplify` does, on 3938 generated `add`s | Finitely many cases, so evidence, not proof | [`tests/cpp_correspondence.py`](../tests/cpp_correspondence.py) |

The pin is `tests/llvm/targets.toml`'s: `llvmorg-23.1.3`, commit `0d261d1ca552c95a8f007e061c787ac7132fbcbc`, with the NAR
hash `LLVM_PROJECT_SRC` has in the dev shell. `anchors.json` names it, and has to match it. `instsimplify` is
`pass:instsimplify` in the [inventory](llvm-verification-tasks.md), whose hash for `InstSimplifyPass.cpp` has to be the
one recorded here.

## The theorem

```lean
theorem simplifyAddInst_sound (ρ : Nat → Val w) (op0 op1 r : Operand w) (isNSW isNUW : Bool)
    (maxRecurse : Nat) (v0 v1 : Val w) (c0 : op0.Consistent ρ) (c1 : op1.Consistent ρ)
    (h0 : op0.denote ρ = some v0) (h1 : op1.denote ρ = some v1)
    (h : simplifyAddInst op0 op1 isNSW isNUW maxRecurse = .value r) :
    ∃ vr, r.denote ρ = some vr ∧
      (Val.add v0 v1 isNUW isNSW = none ∨ vr = Val.add v0 v1 isNUW isNSW)
```

An `Operand` is what the matchers can see of a `Value *`: a `ConstantInt`, poison, `undef`, a `sub`, `xor` or `add`
instruction with its operands and flags, or anything else. Each instruction carries an identity, standing for its
address. `ρ` gives each instruction and argument its value, and `Consistent ρ` says each instruction's value is what
its operation gives on its operands', so one address has one value. `denote` is `none` where an operand reaches
`undef`, and the hypotheses rule that out.

So: if the model returns a value, then whatever the operands' values, poison included, either the `add` is poison or
the value is the `add`'s. That's refinement for values, as `IRLean.Val.add` defines `add`'s flags. `Val.add` takes
`nuw` first, and `simplifyAddInst` takes `IsNSW` first, as the C++ does.

## The C++ it models

`simplifyAddInst` is at `llvm/lib/Analysis/InstructionSimplify.cpp:594`. The model takes the same steps, in the same
order, and returns at the first that applies. The case named is one of the comparison's, and each step has one.

| Step | C++ | Returns | Why it's right | Case |
| --- | --- | --- | --- | --- |
| `fold.both`, `fold.swap`, `add.fold` | Two constants fold. A lone constant on the left swaps to the right | Constant folding isn't modelled | `add` commutes | `fold.both`, `fold.swap` |
| `add.poison` | `X + poison` | poison | The `add` is poison | `add.poison` |
| `add.undef` | `X + undef` | `undef` | Not claimed: `undef` has no value in IRLean | `add.undef` |
| `add.zero` | `X + 0` | `X` | `x + 0 = x` | `add.zero` |
| `add.negation` | `isKnownNegation(X, Y)`: `X = 0 - Y`, `Y = 0 - X`, or `X = A - B` and `Y = B - A`, with any flags | 0 | The sum is 0 where nothing is poison | `negation.of_op1`, `negation.of_op0`, `negation.swapped` |
| `add.subCancel` | `X + (Y - X)`, `(Y - X) + X` | `Y` | `(y - x) + x = y` | `subCancel.op1`, `subCancel.op0` |
| `add.not` | `X + ~X`, `~X + X`, with `~X` as `xor X, -1` or `xor -1, X` | -1 | `x + ~x` is all ones | `not.op0`, `not.op1` |
| `add.signMask` | `add nsw` or `add nuw` of `xor Y, signmask` and `signmask` | `Y` | Adding the sign mask only flips the sign bit, so this is `y` whatever the flags | `signMask.nsw`, `signMask.nuw` |
| `add.nuwAllOnes` | `add nuw X, -1` | -1 | It doesn't wrap only when `x` is 0 | `nuwAllOnes` |
| `add.i1` | Any `i1` add, while recursion is left | `simplifyXorInst` isn't modelled | | `i1` |
| `add.assoc` | `simplifyAssociativeBinOp`, which needs an operand that's an `add` | `nullptr`, or isn't modelled when there's an `add` operand | | `assoc` |
| `add.null` | Nothing applies | `nullptr` | | `null` |

The matchers are modelled from `llvm/include/llvm/IR/PatternMatch.h` as the pinned source has them, and two of their
details change what's matched:

- `m_Specific` compares addresses. Two `sub` instructions with the same operands are different values to it, so the
  model compares identities, not trees. `subCancel.other_pointer` is `X + (a1 - X')`, where `X'` is a copy of `X`,
  and neither `opt` nor the model rewrites it.
- `m_Sub` and `m_Xor` match their operands in one order, and `m_Not` in both. `signMask.commuted_xor`, with the sign
  mask on the left of the `xor`, isn't rewritten.

`isKnownNegation` is at `llvm/lib/Analysis/ValueTracking.cpp:8820`, called with its defaults, `NeedNSW` false and
`AllowPoison` true. InstSimplify reaches `simplifyAddInst` through `simplifyInstruction`, with the instruction's own
flags and a recursion budget of 3. Its query has `CanUseUndef` true, so `m_Undef` applies.

InstCombine's `visitAdd` calls `simplifyAddInst` before anything else [cpp:instcombine.visitAdd], with its own query,
so the `add.zero` step is likely where [binding](llvm-proof-binding.md)'s bound `instcombine` run on `add i8 %x, 0`
comes from. Nothing here checks that.

## How it's checked

```console
nix develop -c tests/cpp_correspondence.py
```

`ctest` runs it as `cpp_correspondence`. One process at a time, each with a time limit (300 s by default), Lean's
`-M` memory limit (2000 MB by default), and, where `systemd-run --user --scope` works, a cgroup capped at 512 MB more
with no swap. A limit prints `UNKNOWN` and fails the run, so it's never a pass. Without waiting for other jobs, it takes
about 12 s.

| Check | What it shows | Fails when |
| --- | --- | --- |
| `pin` | llvm-project has the pinned NAR hash, `opt` is its version, and the inventory's hash for `InstSimplifyPass.cpp` is this one | Any of them moves |
| `anchors` | Each of the 42 quotes is at its lines, of 7 files with their SHA-256. Every line of `simplifyAddInst`, `foldOrCommuteConstant` and `isKnownNegation` that isn't blank or a comment is quoted. Every `[cpp:<id>]` tag in the Lean and this page has a quote, and every quote is cited | A file or a quoted line changes, a line goes unquoted, or a tag and a quote don't pair up |
| `anchors` negatives | A copy of the source with `IsNUW &&` deleted from the `add nuw x, -1` step is refused at that quote, and the quotes without `add.signMask` are refused for its unquoted lines | Either is accepted |
| `lean` | The model and the theorem compile with warnings as errors, `tests/check_axioms.lean` finds only the standard axioms, and `leanchecker` replays them | Any doesn't |
| `differential` | 5433 generated `add`s, at widths 1, 8 and 32, with every pair of operands from a set of arguments, constants, poison, `undef`, `sub`s, `xor`s and `add`s, plus operands built to match each step against each other, with each of the four flag sets. The model's answer for each is what `opt` returns. 1111 delegate and aren't compared. 384 are left out because InstSimplify changes one of their operands first, so `simplifyAddInst` would see another operand. Each named case in the table has to be compared, or delegate as expected | Any answer differs, or a named case is left out or answered otherwise |
| Mutants | Dropping `isNUW &&` from the `add nuw x, -1` step stops the theorem with an error of its own, and 133 cases differ from `opt`. Dropping the flag guard of `add.signMask` leaves the theorem proved, since the rewrite is right without flags, and only the comparison finds it, on 5 cases | Either goes unnoticed |

Each `add` is in a function of its own, with a call that keeps both operands alive, so every line but the `add` and
the `ret` has to come out of `opt` unchanged. `opt -passes=verify` writes the same IR, for comparing the text.

## What it rests on

| Assumption | Why it's reasonable | What would break it |
| --- | --- | --- |
| The model is the C++: each step, matcher and order | Every code line is quoted, and the comparison agrees on 3938 cases, including one for each step | A mistake the cases miss, such as one about vectors or constant expressions, which aren't generated |
| A `ConstantInt`, poison or `undef` of a type has one address | `LLVMContext` keeps one of each per value and type | Nothing at the pin |
| `opt` is built from the pinned source, by a compiler that does what the source says | The same `llvmPackages` gives both, as in [binding](llvm-proof-binding.md) | A Nix or binary-cache compromise, or a miscompiled `opt` |
| IRLean's `add`, `sub` and `xor` are LLVM's | [Trust](trust.md), and `tests/opcheck.py` against Alive2 | A wrong operation those checks miss |
| Lean's kernel | [Trust](trust.md) | A Lean bug |

The theorem doesn't trust the translation: it's about the model, whatever the C++ does.

## What isn't established

Each of these counts as unfinished. No claim about `instsimplify` goes into
[`coverage.json`](../tests/llvm_scope/coverage.json): this is progress toward the `code-binding` dimension, not a
claim of it.

- **The rest of the C++.** Constant folding, `simplifyXorInst`, and `simplifyAssociativeBinOp` when an operand is an
  `add`, are delegated, and the model claims nothing there. Vectors, constant expressions and other constants aren't
  representable. Every other opcode `simplifyInstruction` handles is untouched.
- **The pass around it.** InstSimplify's loop replaces uses, deletes dead instructions, revisits users, skips
  unreachable blocks, and turns an instruction that simplifies to itself into poison. None of that is modelled, and
  neither is dominance: each value the model returns is a constant, an operand or an operand's operand, which
  dominate the `add`, but nothing here proves a replacement is in scope.
- **A mechanical translation.** The model was written by hand. Tying it to the C++ without a person in between needs
  the C++ compiled at the pin and translated, with LLVM's `Value`, use lists and uniqued constants in the model
  (BIND-04 and BIND-05 in the [tasks](llvm-verification-tasks.md)), or a checked extraction.
- **`undef`.** The `X + undef` step returns `undef`, which IRLean has no value for, and arguments that may be `undef`
  are outside the theorem. That waits on `undef` semantics.
- **The shared refinement relation.** The theorem states refinement as `Val.add v0 v1 nuw nsw = none ∨ vr = ...`.
  Once `IRLean.Refines` is on the main branch, it can be restated with it.
- **The compiler and the binary.** Every route here trusts the compiler that built `opt`.

## When the pin moves

`pin` and `anchors` fail. Then: diff each quoted range between the two sources, read the model against the new text,
change it where the C++ changed, and record the new quotes, line numbers and file hashes in `anchors.json`. The
differential comparison then runs against the new `opt`.
