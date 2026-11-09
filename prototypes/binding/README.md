# Binding prototype

**Prototype, for research only.** Nothing here is part of the `IRLean` library, the build or CI, and nothing here is
a claim in [status](../../docs/status.md) or the [task list](../../docs/llvm-verification-tasks.md)'s coverage.
[Binding a proof to LLVM's C++](../../docs/binding-approach.md) says what it's for, what it found, and where it stops.

It proves that `llvm::isKnownNegation`, compiled by the pinned clang from the pinned `ValueTracking.cpp` and translated
by `ir-lean`, computes what [#47's model](../../docs/llvm-cpp-correspondence.md) of it computes, on every heap that
holds its operands as `HeapView.lean` describes, with three of its callees cut.

| File | What it is |
| --- | --- |
| `census.sh` | Compiles InstCombine's 15 files and the 3 InstSimplify leans on most, and counts what `ir-lean` translates and why it refuses the rest |
| `check.sh` | The prototype end to end: compile, extract, cut, translate, check the layout, check the proof, and two must-break mutants of the C++ |
| `cut.py` | Replaces each call to the functions it's given with a call that stops the model. This is the step the prototype trusts |
| `layout_probe.cpp` | Builds objects with the pinned `libLLVM` and checks the offsets and IDs `HeapView.lean` takes as its definition |
| `HeapView.lean` | What bytes in IRLean's memory mean as the `Value *`s the model calls `Operand`s, for the reads this function makes, with lemmas for reading them and for the function's stack slots |
| `KnownNegationProof.lean` | The theorem, `isKnownNegation_compiled`, and `Example.view`, a heap built byte by byte that meets its hypotheses |

```console
nix develop
cmake -S . -B build -G Ninja && ninja -C build ir-lean
lake build IRLean
prototypes/binding/check.sh build/ir-lean build/binding-proto
tools/measure.py run --label census --heavy --max-tree-rss-mb 12000 -- \
  prototypes/binding/census.sh build/ir-lean build/binding-proto
```

Everything they generate goes under the work directory, `build/binding-proto` above. `check.sh` takes about 30 s and
1.6 GiB. `census.sh` runs 4 clang processes at once, so it's a heavy run.

## What `cut.py` trusts

`ir-lean` refuses a call to a function outside the module. The compiled `isKnownNegation` has 6 calls to 3 such
functions, on paths for widths over 64, for vectors, and for `NeedNSW`. `cut.py` replaces each with a call to a
declared `noreturn` function, which `ir-lean` translates as `Outcome.stop .noReturnCall`, followed by a placeholder for
the result that never runs. Nothing else in the function changes.

The theorem says the cut function returns `Outcome.ok`, so no run it covers reaches a cut. On a run that reaches no
cut, the cut and uncut functions run the same instructions in the same order and return the same value. So the theorem
holds of the uncut function too, by that argument, which is on paper and not in Lean. Making `ir-lean` translate such
calls as stops itself, or linking their definitions in, removes it.
