# Lemma-reuse experiment

The production lemma store now checks admission. Its retirement audit refused all 13 generated population-count
lemmas and all 27 generated q4_K lemmas. The [per-lemma record](against-store.json) lists each outcome and reason
for those lemmas, the five handwritten seeds in [Count.lean](Count.lean), and the 21 theorems from
[Bits.lean](../../tests/llvm/Bits.lean).

The store checks axioms for the whole module. In `Bits.lean`, `fold16`, `fold8`, `fold4` and `fold4Small`
call `bv_decide`. The other 17 theorems inherited the module's `nonstandard_axiom` refusal. Across all four
groups, the 19 entries marked `hypotheses_unsatisfiable` were missing the required `.sat` witness.

From a checkout with the archived commit in its Git history, run:

```sh
nix develop -c prototypes/lemma-reuse/compare.sh
```

The script builds the original store in a temporary directory, compiles its inputs from the archive, and
compares the dry-run decisions with the record. The original scripts and generated proofs can be read together
in the [archived experiment](https://github.com/phongndo/ir-lean/tree/b0b8b1d4158dec7afd4e578d35da97d915edc245/prototypes/lemma-reuse).
The [research report](../../docs/lemma-reuse.md) describes the original timing runs.
