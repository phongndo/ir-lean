import Rules.Mono
import Rules.Statements
import Rules.Imported

/-! # Rules: rewrites proved for every input

Each rule is a pattern, a replacement and side conditions in `rules/src/*.json`. `Rules.Statements` has the statement
generated from each, `Rules.Stmt.<name>`, and `Rules.<name>` proves it, on the standard three axioms.
`Rules.Mono` has the congruence lemmas a certificate carries a rule through. `docs/rules.md`. -/
