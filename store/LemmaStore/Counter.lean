import LemmaStore.Counter.Contract
import LemmaStore.Counter.Generic
import LemmaStore.Counter.Refine

/-! # Counterexamples for the lemma store

For each hypothesis of a stored lemma, a theorem that the lemma without it is false, and for each lemma with
hypotheses, a witness that they can all hold. `tools/store/store.py check` finds them by name, under this namespace:
`LemmaStore.Counter.<lemma>.drop_<hypothesis>` and `LemmaStore.Counter.<lemma>.sat`, and checks each states exactly
what it has to. `docs/lemma-store.md` says why. -/
