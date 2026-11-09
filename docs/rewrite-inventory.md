# Rewrite inventory: chunk 1

Every rewrite in chunk 1's four peephole passes, InstSimplify, InstCombine, AggressiveInstCombine and Reassociate, at
LLVM `llvmorg-23.1.3`, each with a stable ID and a source location. This is
[INV-04](llvm-verification-tasks.md#inv-04-rewrite-level-inventory) for chunk 1, and the denominator of chunk 1's G2:
every rewrite proved for every input. It's derived from the pinned source by
[`tests/llvm_rewrites.py`](../tests/llvm_rewrites.py) into [`tests/llvm_scope/rewrites/`](../tests/llvm_scope/rewrites),
one file per pass, and CI derives it again and compares.

C++ doesn't say where one rewrite ends and the next begins, so the rule below says it. The rule is the trust gap INV-04
names, and it's here to be reviewed. Generated on 2026-11-09 from the dev shell's `LLVM_PROJECT_SRC`. It reads only
source files, so it gives the same bytes on any host.

## Totals

| Pass | Rewrites | Integers only | Need floating point | Need memory | Need calls | Folds | Files |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InstSimplify | 540 | 305 | 189 | 32 | 109 | 150 | 2 |
| InstCombine | 2,392 | 1,600 | 428 | 178 | 381 | 520 | 15 |
| AggressiveInstCombine | 25 | 13 | 3 | 7 | 5 | 33 | 2 |
| Reassociate | 43 | 29 | 13 | 0 | 1 | 23 | 1 |
| All | 3,000 | 1,947 | 633 | 217 | 496 | 726 | 20 |

A rewrite can need more than one of floating point, memory and calls, so those columns overlap. "Integers only" is
the rest, which needs none of them. `tests/llvm_rewrites.py summary` prints these from the files.

What the blocked ones wait for:

| Needs | Waits for |
| --- | --- |
| Floating point | SEM-05, the floating-point semantics |
| Memory | F4, `Refines` for functions with memory, SEM-06 |
| Calls | The external-calls lane: calls to functions and intrinsics the model doesn't have |

## The rule

### A rewrite is a site

A **rewrite** is a *site*: a statement in the pinned C++ where a fold function commits a change. There are two kinds.

- **A return** of something other than `nullptr`, `false`, `{}` or `std::nullopt`, from a fold whose result is an IR
  value, such as `Value *` or `Instruction *`, or `std::optional` of one, or a `bool` that says it changed something.
  This includes `return &I;` after changing `I` in place, and `return Op0;`, which replaces an instruction with one of
  its operands.
- **A flag**: `Changed = true;`, or the same for `MadeChange`, `MadeIRChange` and `Modified`. This is how flag
  inference and in-place canonicalization commit, as in `visitAdd`'s `nsw` inference and Reassociate's
  `OptimizeInst`.

A site's obligation for G2 is that whatever reaches it is right for every input. That's the path from the function's
entry to the site, with every condition on it, and the value built there.

### Folds, helpers and builders

A function in the pass's files is a **fold** when it can **decline**, by returning a null value, `false`, or a flag
that may be false, and one of these holds:

- it's an entry point: InstSimplify's `simplifyInstruction`, every other `simplify*` function `InstructionSimplify.cpp`
  exports, since InstCombine and other passes call them, and the pass driver's `runImpl`. InstCombine's `visit*`
  methods, which the `InstVisitor` dispatches to, `InstCombinerImpl::run`, `prepareWorklist`, `InstCombinePass::run`
  and `combineInstructionsOverFunction`. AggressiveInstCombine's `runImpl`, its pass's `run` and
  `TruncInstCombine::run`. Reassociate's `ReassociatePass::run`. `PASSES` in the script lists them;
- a fold forwards to it;
- it builds IR or changes it in place: it calls `Create*`, `new`, `replaceOperand`, `setOperand`, `swapOperands`, a
  flag setter such as `setHasNoSignedWrap`, `replaceAllUsesWith`, or an eraser. The full list is `CHANGES` in the script.

A lambda is a function of its own here, named after the variable it's stored in.

A function that returns an IR value and isn't a fold is listed for review, and has no sites:

- A **helper** declines, but builds nothing and nothing forwards to it. It finds a value a fold then uses, as
  `findInitTrampoline` does. Each pass's file lists them under `helpers`.
- A **builder** never declines, as `getFalse(Ty)` doesn't. When a fold returns what a builder builds, the site is the
  fold's return, since that's where the decision to rewrite is made. Listed under `builders`.

### Forwards aren't sites

A **forward** passes on another fold's result. It isn't a site, and it makes its callee a fold:

- `return g(...)`, `return replaceInstUsesWith(I, g(...))`, or `return C ? g(...) : h(...)`, where `g` and `h` are
  folds;
- `if (Value *V = g(...)) return V;`, or `return replaceInstUsesWith(I, V);`, where every value assigned to `V` is a
  fold's result. A name bound by a matcher, such as `m_Value(Y)`, holds the site's own value, so `return Y;` is a site;
- `if (g(I)) return &I;`, and `Changed |= g(I);`, where `g` is a fold that returns `bool`;
- `return foldA(...) || foldB(...);` in a fold that returns `bool`;
- a driver's `if (Value *V = g(I)) { I.replaceAllUsesWith(V); Changed = true; }`, where the block changes nothing but
  installing `V`;
- `return Changed ? &I : nullptr;`, whose sites are where `Changed` is set.

So InstCombine's `visitAdd` calling `simplifyAddInst` isn't a site of InstCombine's: the eight sites in
`simplifyAddInst` are InstSimplify's, counted once. A pass's rewrites are the sites in its own files. InstCombine's G2
leans on InstSimplify's, but they're counted under InstSimplify.

### One site, one pattern?

Not always, and the proof obligation is per site:

- One site can cover several patterns: `if (match(A, P) || match(B, Q)) return Y;` is one site with two. #47's model
  of `simplifyAddInst` has two cases for its line 621, `X + (Y - X)` and `(Y - X) + X`, both one `return Y;`.
- One pattern can be written as two sites, such as a fold and its commuted twin.
- One site can return different things on different paths: `return IsExact ? Op0 : Zero;` is one site.

### IDs

`<pass>.<file>.<function>.L<line>`, such as `IS.simplifyAddInst.L609` or `IC.AddSub.visitAdd.L1647`:

- `IS`, `IC`, `AIC` and `RA` are the passes. InstSimplify has no file part, since its rewrites are all in
  `InstructionSimplify.cpp`, apart from its driver's.
- The file part drops `InstCombine` from InstCombine's file names, so `InstCombineAddSub.cpp` is `AddSub`.
- The function part drops `llvm`, `InstCombinerImpl`, `InstCombiner` and `ReassociatePass`, and keeps other classes,
  such as `Negator`. A lambda adds its name.
- The line is the line of the statement's first token. Two sites on one line get `.2`, `.3` and so on, in order.

An ID is stable at the pin: deriving it again gives the same IDs. A new pin moves lines, so each rewrite also records
a hash of its function's name and its statement's text, to match old IDs to new sites by function and hash.

## What each rewrite needs

Each rewrite has:

- `needs`: `int`, or any of `fp`, `memory` and `calls`, from the identifiers on its path. The path is the function's
  name and parameters, the conditions of the statements around the site, the plain statements before it in each
  enclosing block, the case labels it's under, and the site itself;
- `also`: `vector` for shuffles, extracts, inserts and vector types, `cfg` for phis, branches and blocks, and `undef`
  for folds that test for `undef`. These don't block G2: the model has fixed-width vectors and control flow, and it has
  no `undef`, so a proof covers poison and says nothing about `undef`, as #47's does. Scalable vectors aren't in the
  model at all, and no rewrite's proof covers them;
- `analyses`: the analyses on its path, such as `computeKnownBits` or `isKnownToBeAPowerOfTwo`. A proof takes each
  analysis's answer as a hypothesis that it's sound, which is [PASS-01](llvm-verification-tasks.md#pass-01-analyses-are-sound)'s
  to prove. 321 of InstCombine's rewrites and 85 of InstSimplify's read one;
- `intrinsics`: those named on its path. The integer intrinsics `src/Emitter.cpp` translates, such as `umax`, `ctpop`
  and `fshl`, count as integers only. An intrinsic the model doesn't have counts as a call.

The tags are triage, read from names. A proof can find a rewrite needs more than its tags say. When it does, the
proof's record says so. The tags don't decide what's proved.

## What the rule doesn't see

For the reviewer, the places the rule can be wrong:

- **It reads tokens, not a C++ AST.** It finds functions, statements, lambdas and calls by their brackets and names.
  It doesn't expand macros, instantiate templates or resolve overloads. A call resolves to every function in the four
  passes with its name and a compatible qualifier, so overloads merge.
- **Calls through the `InstVisitor`** aren't followed. Every `visit*` method is an entry instead.
- **Rewrites made outside these files** are sites only where these files return or install their result. A
  `return ConstantFoldBinaryOpOperands(...)` is one site, and the constant folder's own cases aren't inventoried.
  Neither are `Local.cpp`'s dead-code removal or `ValueTracking`'s analyses.
- **Helpers and builders aren't counted.** What a builder builds is part of the site that returns it, and what a helper
  finds is part of the site that uses it. A helper that's really a fold, because its caller installs its result in a
  way the forward rules don't name, would be missed. The `helpers` lists are short for that reason: 2 in InstSimplify,
  36 in InstCombine, 1 in each of the others.
- **Changes with no site.** A function that changes IR and returns neither a value nor a flag, or changes IR before
  declining, has a change no site names. A test of every such call would need data flow the scanner doesn't have.
- **Other counts measure other things.** InstCombine's `.cpp` files have 2,308 calls to `match(`: patterns tried, of
  which several can guard one site and one can guard several. The 520 folds include lambdas and helpers that build,
  so they're more than the functions named `fold*` or `visit*`.
- **Preprocessor conditionals are read as code.** At the pin no site is inside `#ifndef NDEBUG` or
  `#if LLVM_ENABLE_STATS`, which the release `opt` leaves out. A site there would be counted.

[`tests/llvm_rewrites_test.py`](../tests/llvm_rewrites_test.py) checks the rule on small C++ files, a positive case
for each kind of site and forward, a helper and a builder. On a copy of the pinned source, it checks that a rewrite
removed, added or changed is each reported by its ID.

## Reproducing

In `nix develop`:

```console
tests/llvm_rewrites.py check      # derive the inventory again, and fail on any difference
tests/llvm_rewrites.py generate   # write it, after a change to the rule or the pin
tests/llvm_rewrites.py summary    # the totals, from the files in the repo
tests/llvm_rewrites_test.py
```

`check` takes about a second. It fails if a rewrite appears or disappears, or a recorded one changes, without the files
changing, and names each by ID.
