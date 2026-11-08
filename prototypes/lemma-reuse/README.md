# Lemma reuse prototype

**Prototype, for research only.** Nothing here is part of the `IRLean` library, the build or CI, and nothing here
is a claim in [status](../../docs/status.md). [Lemma reuse](../../docs/lemma-reuse.md) says what it's for, what it
found, what it rests on and what it can't do yet.

It takes a theorem that a rewrite returns what clang's code returns, which one `bv_decide` call can't finish, cuts
clang's code where simulation says a value is understood, checks a lemma for each step in a module of its own, keeps
the lemmas that check, and continues the original proof with them. The next goal looks in the store first.

| File | What it is |
| --- | --- |
| `lemmas.py` | The tool. `prove` runs the goals, `rewrite` reruns the search that found each rewrite |
| `goals.toml` | The three goals, in the order they fill and use the store |
| `Count.lean` | Seed lemmas, proved once by induction for every width: a population count is the sum of its fields' |
| `rewrites/` | What `tests/superopt.py`'s search finds for `__popcountdi2` and `__popcountti2`, with a truncation |
| `store/` | The lemmas the goals saved, one module each, and `index.json`: what each says, how general it is, who used it |
| `proofs/` | Each goal's finished proof, as the original proof continued with lemmas from the store |
| `report.json` | What `check.sh` measured from an empty store: times, sources of lemmas, axioms and gaps |
| `check.sh` | Proves every goal from an empty store, then again from what that saved, and compares with the above |

To run it, in `nix develop`, after `lake build` and building `build/ir-lean`:

```console
prototypes/lemma-reuse/check.sh build/ir-lean
prototypes/lemma-reuse/lemmas.py prove popcountti2_same --store prototypes/lemma-reuse/store --fresh
```

The second line proves one goal from the saved lemmas alone, checking each of them again. `--baseline` first tries
the goal as one `bv_decide` call, `--alive MS` asks Alive2 too, and `--goals FILE` takes goals from a file like
`goals.toml`.
