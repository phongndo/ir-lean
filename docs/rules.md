# Rules

A rule is a rewrite of LLVM IR that's proved for every input: a pattern, a replacement and side conditions, in one
declarative source. From that one source come the rule's Lean statement and the matcher that applies it to real IR. This
page is the format, what the statement claims, how the two are tied, what's trusted, and which of chunk 1's proved
rewrites are rules now. [Rule search](rule-search.md) is the search that uses them. For what any theorem here means,
read [trust](trust.md) first.

It's [decision 10 after #103](roadmap.md)'s rule format and certify mode, and decision 4's rules. The plugin that will
generate its C++ matcher from the same source isn't built: [below](#the-plugin) says how the format allows it.

Facts here were checked on 2026-11-10 on top of `df3e997`, on z, x86-64 Linux, in the dev shell, with Lean 4.35.0 and
LLVM 23.1.3.

## What's there

- **182 rules, each proved for every input,** at every width where it has a width variable, on the standard three
  axioms, with nothing from `bv_decide`. `lake build` checks them, in 0.9 s on top of the rest.
- **All 182 were imported, none written by hand:** of the 243 lemmas about instructions in the `Peephole` library and
  `IRLean.Generic`, 182 are rules the format can say, and each one's proof is its lemma, in one line. The other 61
  can't be said, each for a reason [below](#what-was-imported).
- **100 of chunk 1's 247 proved rewrites have a proof that uses a lemma that's now a rule.** None of InstSimplify's
  95 `icmp` rewrites does.
- **Certify mode takes IR and the names of rules, and nothing a matcher says.** A wrong statement generator, a
  wrong matcher and a false rule are each refused, for their own reason: [below](#what-fails).

## The format

A rule file is JSON, schema `ir-lean.rules/1`, in [`rules/src`](../rules/src). Each rule:

| Field | Meaning |
| --- | --- |
| `name` | A Lean identifier. The statement is `Rules.Stmt.<name>` and the theorem `Rules.<name>` |
| `match` | The pattern, an S-expression over the instructions below |
| `replace` | The replacement, over the pattern's variables. A new instruction, a constant, or something the pattern bound |
| `where` | Side conditions on the pattern's constants and widths. Optional |
| `doc` | One line, for a reader. Optional |
| `from` | The theorem the rule was cut from, if any. Provenance only: nothing reads it as evidence |
| `sites` | The [inventory](rewrite-inventory.md)'s IDs of the rewrites whose proofs use that theorem. Provenance only |

```json
{"name": "add_sub_cancel", "match": "(add (sub B A) A)", "replace": "B",
 "from": "Peephole.Lemmas.add_sub_cancel_refines",
 "sites": ["IS.simplifyAddInst.L613", "IS.simplifyAddInst.L621"]}
```

### Terms

| Term | Matches | In the Lean statement |
| --- | --- | --- |
| `X`, `Y`, any name starting with a capital, but `C` and a digit | Any value. A second occurrence has to be the same value, as `m_Specific` | `x : Val w` |
| `C`, `C0`, `C1` | A `ConstantInt`, as `m_APInt` | `c : BitVec w`, used as `some c` |
| `0`, `1`, `-1`, `intmin`, `intmax`, any integer | That constant, at the operand's width | `0#w`, `1#w`, `BitVec.allOnes w`, `BitVec.intMin w`, `BitVec.intMax w`, `n#w` |
| `(add A B)`, and `sub`, `mul`, `shl`, `lshr`, `ashr`, `and`, `or`, `xor`, `udiv`, `sdiv`, `urem`, `srem` | That instruction, operand 0 then operand 1. Not commutative: a commuted form is another rule | `Val.add a b nuw nsw`, and the like |
| `(icmp.ult A B)`, and the other nine predicates | An `icmp` with that predicate | `Val.icmpUlt a b samesign` |
| `(select P A B)` | A `select` on an `i1` | `select p a b` |
| `(zext A)`, `(sext A)`, `(trunc A)` | The cast. Its operand has a width of its own | `Val.zext w a nneg`, with `w1 < w` as a hypothesis, which LLVM's verifier guarantees |
| `(umin A B)`, and `umax`, `smin`, `smax`, `uadd_sat`, `usub_sat`, `sadd_sat`, `ssub_sat`, `ctpop`, `bitreverse`, `bswap`, `ctlz`, `cttz`, `abs`, `fshl`, `fshr` | A call to that intrinsic | `Val.umin a b`, and the like |
| `(bind T (or A B))` | What `(or A B)` matches, and names it `T`, for the replacement or for a second occurrence | The same expression, wherever `T` is used |
| `(c.not C)`, and `c.neg`, `c.add`, `c.sub`, `c.and`, `c.or`, `c.xor`, `c.urem`, `c.srem` | In a pattern, the constant with that value. In a replacement, a new constant | `~~~c`, `c1 + c2`, and the like |
| `X:1` | A value of exactly that width | `x : Val 1` |

**Flags.** A flag named in the pattern is required: `(add.nuw X -1)` matches only an `add nuw`. A flag the pattern
doesn't name may be set or not, and the statement quantifies over it as a `Bool`. A flag named in the replacement is
set on the new instruction, and one not named isn't. The `i1` operand of `ctlz`, `cttz` and `abs` is a flag: `zp` and
`imp`.

**Side conditions** are `(eq E1 E2)`, `(ne E1 E2)`, `(ult E1 E2)`, `(ule E1 E2)`, `(bule E1 E2)`, `(bsle E1 E2)`,
`(pow2 E)`, `(msb E)`, `(lsb E)`, `(not P)` and `(wgt N)`, the width is above `N`, over constant expressions. Each has a
Lean form and a Python form, and the matcher runs the Python one on the constants it bound. `bule` and `bsle` are
`BitVec.ule` and `BitVec.sle`, the forms the min and max lemmas use.

**A division in a pattern** can be undefined, so it isn't a value. One at the pattern's root is the statement's left
side itself. One below the root becomes a variable `q` with the hypothesis that the division returned it,
`Val.udiv a b exact = Outcome.ok q`.

### What the format can't say

- **Analyses.** A rewrite that asks known bits, a range or dominance has no pattern for the answer.
- **Vectors, floating point, memory, calls, `freeze` and `phi`.** Scalar integers only.
- **A flag on the replacement that depends on the matched flags,** such as keeping `nuw` when the pattern had it. So
  `add`'s, `mul`'s and `or`'s commutativity aren't rules.
- **A flag that has to be unset.**
- **Poison or `undef` as an operand.**
- **A division in the replacement.**
- **A commutative matcher.** `m_c_Add` is two rules here.

## What a statement claims

[`tools/rules/rules.py gen`](../tools/rules/rules.py) writes
[`rules/Rules/Statements.lean`](../rules/Rules/Statements.lean), one definition a rule:

```lean
/-- `add_sub_cancel`: `(add (sub B A) A)` to `B`. -/
@[reducible] def add_sub_cancel : Prop :=
  ∀ {w : Nat} (b a : Val w) (f0 f1 f2 f3 : Bool),
    Refines (Outcome.ok (Val.add (Val.sub b a f2 f3) a f0 f1)) (Outcome.ok b)
```

It says the replacement [refines](refinement.md) the pattern: for every width, every operand, poison included, every
flag the pattern leaves open and every constant meeting the side conditions, the replacement only does what the pattern
allows. It's a statement about values in IRLean's model, at every width where the rule has a width variable. It isn't
about LLVM's C++, and it isn't an equality: `(b - a) + a` with `a` poison is poison, and `b` needn't be.

The file is checked in, and `rules.py gen --check` fails if it isn't what the source generates.

A rule is **proved** when `Rules.<name>` is a theorem whose type is the constant `Rules.Stmt.<name>` itself, on the
standard three axioms, with nothing from `bv_decide`, as [the bar for a stored lemma](lemma-store.md) asks, in a
library `lake` has nothing left to build for and `leanchecker` replays. The proofs are ordinary Lean, in
[`rules/Rules`](../rules/Rules), which `lake build` checks. `tools/rules/rules.py check` reads each theorem's type and
axioms from the compiled library, with [`tools/rules/rules_check.lean`](../tools/rules/rules_check.lean), and only a
rule that passes is given to the matcher. It took 5.3 s and 2.4 GB for the 182.

## How the matcher and the statement are tied

Both come from the same parsed rule, in [`tools/rules/lang.py`](../tools/rules/lang.py): `Rule.statement` prints the
proposition, and `Rule.match` and `Rule.build` are the matcher. Nothing trusts that. Every application is proved
again, in **certify mode**, which is given IR and the names of rules, and nothing the matcher says:

```console
tools/rules/rules.py certify tests/rules/chain.ll --rule or_zero --rule and_allOnes --rule add_sub_cancel
```

1. **The states.** A module whose functions `@s0` to `@sk` are the states of a chain, each one block of integer
   instructions, and the rule applied at each step. `opt -passes=verify` has to accept it.
2. **The translation.** `build/ir-lean`, the emitter every certificate in the repo rests on, translates the module, and
   each state has to come out as one block without memory.
3. **The certificate.** For each step, `Cert.step_i : IRLean.Refines Chain.s_i Chain.s_{i+1}`. Its proof is one term,
   written from where the two states differ, as the IR has them: one congruence lemma an instruction, `Rules.Mono.*`
   in [`rules/Rules/Mono.lean`](../rules/Rules/Mono.lean), from the function's result down to the instruction that
   changed, `Refine.refl_val _` for each operand that's the same, and the rule's theorem at the instruction that
   changed, with every operand, flag and constant left for Lean to read off the two functions, and each side
   condition left to `decide`. Then `Cert.cert : IRLean.Refines Chain.s0 Chain.sk`, by `IRLean.Refines.trans`.
4. **The gate.** Lean elaborates the certificate. `rules_check.lean` builds `IRLean.Refines Chain.s0 Chain.sk` from
   the two names, where only Lean, `IRLean` and the generated module give it meaning, and requires the theorem's type
   to be that expression, as [`tools/binding_check.lean`](llvm-proof-binding.md) does, and reads the axioms the
   theorem rests on and the rules its proof uses, which have to be the rules named.
   [`tests/check_axioms.lean`](../tests/check_axioms.lean) audits the certificate's module and everything it imports,
   `leanchecker` replays the modules, and [`irlean.verdict`](trust.md#where-python-decides-a-verdict) decides.

The answer is JSON, schema `ir-lean.rules.certificate/1`, and the exit code is 0 only for `certified`:

| Status | Means |
| --- | --- |
| `certified` | Every check above passed |
| `refused` | The certificate doesn't prove the claim: its proof doesn't elaborate, it states another claim, it rests on an axiom that isn't allowed, or it uses other rules than the ones named |
| `unsupported` | A state isn't one block of integer instructions without memory, or its proof would be too long to write |
| `unknown` | A limit stopped Lean. More time or memory might decide it |
| `error` | The states aren't valid IR, or a tool failed |

The certificate's proof has no search in it and no `bv_decide`. It took 3.0 s for the chain above.

### What fails

[`tests/rules_test.py`](../tests/rules_test.py) `--tier live` checks each of these is refused, and for this reason:

| What's wrong | What refuses it |
| --- | --- |
| A statement generator that prints `sub`'s operands the wrong way round | `add_sub_cancel`'s proof stops checking: Lean can't unify the lemma with the statement |
| A statement that isn't the pattern's and is still true, `xor_zero` with its operands swapped, with a proof of its own | The library's statements aren't what the source generates, so `check` proves no rule. And an application of the rule as the pattern has it is `refused`: `proof_failed` |
| A rule whose statement is false, `(add X 1)` to `X` | Its proof from a lemma fails. With no theorem: `not_proved`. Proved by `sorry`: `disallowed_axiom`. With a theorem of another statement: `statement_mismatch` |
| A true rule at one width, proved by `bv_decide` | `disallowed_axiom` |
| A matcher that takes a second occurrence of a variable for any value | `refused`: `proof_failed`, a type mismatch at the rule's theorem |
| A matcher that skips a side condition | `refused`: `proof_failed`, `decide` finds the condition false |
| A matcher that doesn't check a flag, builds another replacement, or names another rule | `refused`: `proof_failed`, a type mismatch |
| A certificate whose theorem states something else | `refused`: `claim_type_mismatch` |
| A certificate by `sorry` | `refused`: its axioms aren't allowed |

The matchers are wrong in two ways there: as states a wrong matcher would give, handed to certify mode, and as
matchers generated from a wrong pattern, run by the search's own core.

## What was imported

[`tools/rules/import_peephole.py`](../tools/rules/import_peephole.py) reads every theorem of
`tests/passes-proofs/peephole/Peephole/Lemmas/*.lean`, `IRLean/Generic/Arith.lean` and `IRLean/Generic/Bitwise.lean`
whose conclusion is `Refines l r` or `l = r` with `l` an instruction: the lemmas [chunk 1's rewrites](rewrite-proofs.md)
are proved from. It writes each one the format can say to [`rules/src/peephole.json`](../rules/src/peephole.json), with
a one-line proof from the lemma in [`rules/Rules/Imported.lean`](../rules/Rules/Imported.lean), and why each other
can't be said to [`rules/import/peephole.json`](../rules/import/peephole.json). Lean checks each proof before a rule is
kept, so the importer's reading of a lemma is trusted for nothing. `--check` fails if the three files aren't what it
writes. It took 1.0 s.

| | Lemmas |
| --- | ---: |
| Considered | 243 |
| Imported as rules: 152 from the `Peephole` library, 30 from `IRLean.Generic` | 182 |
| Refused | 61 |

| Why a lemma isn't a rule | Lemmas | Such as |
| --- | ---: | --- |
| A hypothesis the format has no side condition for | 23 | `c.toNat ≤ w`, `s.toNat % w = 0`, `c = BitVec.twoPow w k` |
| A hypothesis about a value, which takes an analysis | 15 | `∀ x, a = some x → x.toNat.isPowerOfTwo ∨ x = 0#w` |
| Its right side isn't a value | 7 | `add_cases`, which says an `add` is poison or the sum |
| Poison as an operand | 7 | `add_none_right` |
| A flag on the replacement that depends on a matched flag | 4 | `add_comm`, `mul_comm`, `or_comm`, `add_self` |
| A flag that has to be unset | 4 | `or_self`, an equation only without `disjoint`. Its refinement, `or_self_disjoint_refines`, is a rule |
| A hypothesis about a flag | 1 | `mul_one`. Its refinement, `mul_one_refines`, is a rule |

Of the 182, 38 have a division in their pattern, and the search doesn't apply those yet
([rule search](rule-search.md#what-it-cant-do)).

**Against chunk 1's proved rewrites.** [The lemma store](lemma-store.md) records, for each lemma, the rewrites whose
theorems use it. By that record, of the 247 rewrites the seven InstSimplify families list with a proof, 100 have a
proof that uses at least one lemma that's now a rule:

| Family | Rewrites listed | With a lemma that's a rule |
| --- | ---: | ---: |
| `is-add` | 7 | 6 |
| `is-arith` | 37 | 24 |
| `is-logic` | 60 | 37 |
| `is-shift` | 22 | 11 |
| `is-intrinsic` | 26 | 22 |
| `is-icmp` | 38 | 0 |
| `is-icmp-b` | 57 | 0 |

That counts lemmas, not rewrites: a rewrite's theorem is about a model of LLVM's C++, with its matchers and the
order it tries them in, and a rule is one pattern. It doesn't say the rule matches everything the rewrite does. The
`icmp` families have none because their lemmas are about bit vectors and predicates, such as when `x.ult y` holds,
and not about instructions, so no lemma there has a pattern on its left. The format has `icmp`: a rule for one of
those rewrites needs a proof written from those facts, which isn't done. The other 52, in the five other families,
use only lemmas that were refused or that aren't about one instruction. This page doesn't break them down.

## What's trusted

- **The emitter and the model,** as for every theorem here ([trust](trust.md)).
- **Cutting a slice out and putting its result back.** For a function with more than one block, memory or a call, the
  certificate is about the slice: the instructions the rewrite reads, as a function of what they read. That the slice
  is what the function computes there, and that replacing it keeps the function's meaning, isn't proved, as for
  [llama.cpp's](llama.md#what-it-assumes). The lemma that would prove it is F4's.
- **`opt`,** for checking that each state is valid IR.
- **Python, for which theorem and which files a verdict is about.** `irlean.verdict` grants it.

Not trusted: the rule source, both generators, the matcher, the search, the importer and the certificate's proof.

## The plugin

Not built. The format is what `PatternMatch.h` can say: each term above is one combinator. `(add A B)` is
`m_Add(A, B)`, a variable is `m_Value(X)` and its second occurrence `m_Specific(X)`, a constant variable
`m_APInt(C)`, `0` is `m_Zero()`, `-1` `m_AllOnes()`, `intmin` `m_SignMask()`, a flag `m_NUWAdd` or a check on the
matched instruction, a cast `m_ZExt`, an intrinsic `m_Intrinsic`, and a side condition a predicate on `APInt`s. A
replacement is `IRBuilder` calls. So a C++ matcher can be printed from the same parsed rule the Lean statement is
printed from.

Certify mode is ready for it, since it takes only IR and the names of rules: a plugin that writes the function before
and after each rule it applied gets each application proved again. What a plugin would add is cutting each rewrite's
slice out of the functions it ran on, which the search does for its own rewrites.

## Gaps

- **No rule is written for a rewrite LLVM doesn't make.** Every rule is one of InstSimplify's.
- **Divisions aren't applied,** and vectors, floating point and memory aren't in the format.
- **A rule's proof is its lemma.** A rule the Peephole library has no lemma for has to be proved by hand, or by an
  agent, and stored.
- **Certify mode needs every state.** Given only the function before and after a chain, it doesn't find the states
  between.
- **The second agent's review of each statement,** [decision 11](roadmap.md), hasn't happened for these 182.
- **`rules.py check` reads the library `lake` built.** It checks `lake` has nothing left to build, and doesn't build.

## Reproducing

In `nix develop`, after `lake build` and building `build/ir-lean`. On a shared machine, run each under
`tools/measure.py run --heavy`:

```console
tools/rules/import_peephole.py --check  # the imported rules are what the importer writes
tools/rules/rules.py gen --check        # the statements are what the source generates
tools/rules/rules.py check              # every rule's theorem, its type and its axioms
tools/rules/rules.py certify tests/rules/chain.ll --rule or_zero --rule and_allOnes --rule add_sub_cancel
tests/rules_test.py --tier static
tests/rules_test.py --tier live
```
