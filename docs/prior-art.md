# Prior art

What others have built toward `ir-lean`'s goals, and what to borrow, contribute to, or build here. This is a research
note. It changes nothing `ir-lean` claims: [status](status.md) and [trust](trust.md) still say what's true, and the
[roadmap](roadmap.md) still says what's planned.

The goals it reads against are the ones set on 2026-11-08:

- **Proved superoptimization:** find code faster than the compiler's, and prove in Lean that it refines the original.
  LLVM IR first, MLIR later by lowering, GIMPLE much later.
- **A lemma store:** each proof leaves checked lemmas that make the next search and proof cheaper.
- **Proof tests:** random and edge-case inputs, then a bounded proof, then a full proof from stored lemmas, never
  reporting unknown as a pass.
- **Guarantees** carried across optimization by `Safe src → Refines src tgt → Safe tgt`.
- **Speed** of the tool and the dev cycle.

It also answers the gate in [Phase 4](roadmap.md#phase-4-certified-translation-validation-and-superoptimization):
whether Trivet or Lean-MLIR already cover integer stage 1.

Researched on 2026-11-08, on top of commit `0330cd7`. LLVM is cited at `llvmorg-23.1.3`, the dev shell's
`LLVM_PROJECT_SRC`, and Lean at `v4.35.0`. Repositories were read at the commits below. Counts of LLVM issues are from
GitHub's search API on that date. Papers are cited by section or table, and the few read only as an abstract say so.
Claims marked *inferred* are this note's reading, not a source's statement.

| Repository | Commit read | Date |
| --- | --- | --- |
| [opencompl/lean-mlir](https://github.com/opencompl/lean-mlir) | `b8c4a771319a` | 2026-07-28 |
| [opencompl/veir](https://github.com/opencompl/veir) | `cb58df7bbf1a` | 2026-11-08 |
| [AliveToolkit/alive2](https://github.com/AliveToolkit/alive2) | `adacbd5180cc` | 2026-10-25 |
| [vellvm/vellvm](https://github.com/vellvm/vellvm) | `1d651e7a391c` | 2026-11-05 |
| [leanprover-community/plausible](https://github.com/leanprover-community/plausible) | `129d1ba9a16b` | 2026-10-27 |
| [leanprover/lean4](https://github.com/leanprover/lean4/tree/v4.35.0) | `v4.35.0` | 2026-10-12 |

## Findings

- **The gate: neither Trivet nor Lean-MLIR covers integer stage 1.** Between them they cover its core: Lean proofs that
  a small integer rewrite refines another, at fixed and symbolic widths, and checked refutations. Neither has a released
  semantics faithful to LangRef, InstCombine's tests proved in the kernel, a comparison with Alive2, known
  miscompilations, a search, or real compiled functions. [Below](#the-gate).
- **Everyone else accepts a rewrite when Alive2 or Z3 says so.** Souper, Minotaur, Hydra, LPO, LPG, PeepholeBench and
  IntOpt produce no proof object, and none proves a rewrite for every width. LLMs find more rewrites than synthesis:
  LPO recovered 22 of 25 known InstCombine misses where Souper found 15 and Minotaur 3. But unchecked LLM output is
  often wrong. Search over real compiled code with Lean certificates is unoccupied.
- **VeIR is the likeliest partner for a shared semantics.** It's the Lean-MLIR group's successor, pinned to the same
  Lean 4.35 and LLVM 23.1.3. It already makes division UB as `IRLean/Int.lean` does, and John Regehr is one of its main
  contributors. It differs on two points that matter for certificates: `freeze` of poison is always 0, and a source its
  interpreter can't run refines anything.
- **Lemma libraries get reused when they're small, curated and matched by structure.** An audit of LEGO-Prover's logs
  found one lemma reused once. DreamProver keeps fewer than 100 lemmas and reports 58% reused. For machine-made lemmas,
  exact and discrimination-tree matching, through Lean core's premise-selection hook, fit better than embeddings.
  Checking small widths is proved to suffice only for narrow fragments, such as linear mixed boolean-arithmetic at
  width 1.
- **Proofs beat tests on the code they cover, and the bugs move to the edges.** CompCert's verified middle end survived
  six CPU-years of Csmith. Alive2 found 121 refinement violations in LLVM unit tests that passed. What's left is in
  specs, glue code and verifiers. A bounded proof needs a check that the bound was enough, as CBMC's and Kani's
  unwinding assertions are. Lean's Plausible can't be tier 1 as it stands: it admits the goal when it finds nothing.

## The gate

> Before stage 1, read Trivet and Lean-MLIR closely. If they cover it, contribute to them or share a semantics, and put
> our effort where memory and whole real functions differ.

Stage 1 is "Pure, loop-free integer code. Using shallow generated functions and `bv_decide` where widths are fixed.
Benchmark against Alive2 on LLVM's InstCombine tests and a set of known miscompilations." It exits when "no known
miscompilation gets a certificate, and each disagreement with Alive2 over at least 500 transformations is explained".

**The answer is no.** So stage 1 goes ahead, but narrowed to what nobody has shipped, and `ir-lean` shouldn't build a
second LLM proof pipeline or width-generic decision procedure for peepholes.

### Trivet

Liao, Xu, Zhou, Zhang and Sun, at Waterloo, "LLVM Translation Validation Automated with Large Language Models and
Lean", [arXiv 2609.19583](https://arxiv.org/abs/2609.19583), v1 of 17 September 2026, a preprint. No code or data was
found: not in the paper, on its arXiv page, on the [author's page](https://cs.uwaterloo.ca/~cnsun/public/preprint/trivet/),
or in the group's GitHub organization.

- **Semantics.** "We build Trivet on top of the LLVM dialect in Lean-MLIR", extended with "immediate UB and
  transformation preconditions", `ctpop`, `cttz` and `ctlz`, and "multiple symbolic-bitwidth parameters and
  multi-block transformations" (§3.4). None of those extensions is on Lean-MLIR's `main`, so this fork's semantics
  can't be checked beyond what the paper says.
- **Input.** LLVM IR goes through MLIR's import, which the paper says works "without loss of semantic information"
  (§3.4). `ir-lean` measured otherwise at 23.1.3: `icmp samesign` drops from 70 uses to 0
  ([multi-IR](multi-ir.md#mlir-loses-facts-on-the-way-in)).
- **Scope.** "Our formalization currently targets integer instructions" (§3.4). No memory, and no `undef`: "our work does
  not support it" (§2.1). Loops are one shape: a three-block canonical loop rewritten to one loop-free block (§3.3).
  `freeze`, `samesign`, `disjoint` and `exact` don't appear in the paper's text.
- **Proofs.** A deterministic scaffold splits on the source's and target's UB conditions and on `select`s, discharges
  the UB branches, and leaves typed holes. An LLM, "the Codex CLI with the gpt-5.5 model", fills them (§3.1, §3.4). A
  proof counts only if the kernel checks it, the statement is unchanged, and it "relies exclusively on standard axioms"
  (§3.1). *Inferred:* that excludes `bv_decide`, whose proofs add an axiom per call.
- **Refutations.** The LLM proposes concrete widths and inputs, and the scaffold proves non-refinement there with
  `decide` (§3.2).
- **Benchmark.** 148 transformations "from the LLVM GitHub repository": 60 valid and 60 invalid loop-free, 14 and 14
  with loops, half at symbolic widths (§4.1, Table 2). The symbolic valid ones are Hydra's or LPG's generalizations, and
  the symbolic invalid ones were made by hand. None is from InstCombine's tests, and none is a known miscompilation.
- **Results.** 147 of 148 (abstract). The valid loop-free cases all prove, at a mean of 684 s. Alive2 proves 20 of the
  30 fixed-width ones and times out at 2 h on the other 10 (Table 3). The invalid loop-free cases are all refuted, at a
  mean of 61 s, where Alive2 refutes 29 of 30 at a median of 0.1 s (Table 4). The one miss is a loop whose
  counterexample needs a poison input (§4.4). A valid proof costs $1.47 on average, and $13.23 without the scaffold
  (Table 6).
- **No search.** It checks pairs it's given (§5). The same group's [LPO](#superoptimizers-and-proposers) searches, and
  checks with Alive2.

### Lean-MLIR

Bhat, Keizer, Hughes, Goens and Grosser, "Verifying Peephole Rewriting In SSA Compiler IRs", ITP 2024,
[arXiv 2407.03685](https://arxiv.org/abs/2407.03685). The repository is Apache-2.0.

- **UB is poison.** In `LeanMLIR/LeanMLIR/Dialects/LLVM/Semantics.lean`, `udiv?`'s docstring says "Division by zero is
  undefined behavior", and its code is `if y = 0 then .poison` (lines 203–213). `sdiv`, `urem` and `srem` do the same
  for a zero divisor and for `INT_MIN / -1`, and a poison divisor gives poison. LangRef 23.1.3 makes all of these
  immediate UB. The paper calls it a deliberate approximation, "safe as long as the right hand side is allowed to
  produce ub only when the left hand side produces ub", which "we manually verify" (§6.1.1).
- **Other gaps against LangRef.** `sdiv i1 -1, -1` is a value (line 238: "at width 1, -1 / -1 is considered -1").
  `freeze` of poison is 0 (lines 636–639). There's no `samesign`, no intrinsics (`Basic.lean`, lines 43–115), no memory
  in the LLVM dialect, and one block per function.
- **InstCombine's tests aren't proved.** `SSA/Projects/InstCombine/scripts/test-gen.py` runs each InstCombine test
  through `opt -passes=instcombine` and `mlir-translate -import-llvm`. `Tests/LLVM` has 4,556 theorems of the form
  `before ⊑ after`, in 367 files. Every one ends `all_goals (try extract_goal ; sorry)` under
  `set_option debug.skipKernelTC true`, counted at `b8c4a771`. The published numbers come from a benchmark harness:
  "over 7000 SMT statements extracted from LLVM" in the [`bv_decide` paper](https://doi.org/10.1145/3763167) (abstract),
  and 4,552 of 4,572 InstCombine goals solved by `bv_decide`, at a geometric mean of 359 ms, in the repository's
  `bv-evaluation/automata-automata-circuit-cactus-plot-data.tex`.
- **Alive's suite:** 93 of its 435 tests translated, 54 proved automatically and 6 by hand (ITP 2024, §6.1.2).
- **Width-generic procedures.** `bv_automata` decides a fragment for every width, and solves "up to 27%" of LLVM's
  peephole tests ([OOPSLA 2025](https://doi.org/10.1145/3763148), abstract only). Blase is "sound and complete for
  parametric bitvector expressions with linear arithmetic, bitwise operations, zeroExtend, signExtend, and bitwidth
  constraints" (`Blase/README.md`). `Blase/Blase/Fast/MBA.lean`, line 627, proves that a linear mixed
  boolean-arithmetic equation that holds at width 1 holds at every width. Medusa, a Hydra-style generalizer in the same
  repository, has no paper this study found.
- **No comparison with Alive2.** The evaluation scripts compare `bv_decide` with Bitwuzla.
- **Activity.** `main` was last committed on 2026-07-28, mostly Blase since January. *Inferred:* the group's energy is
  in VeIR.

### VeIR

[opencompl/veir](https://github.com/opencompl/veir), Apache-2.0 with LLVM exceptions: "a compiler infrastructure written
in Lean that offers both an MLIR-style imperative design and (optional) ITP-level verification" (README). It pins Lean
`v4.35.0-rc4`, and its tests "assume LLVM/MLIR 23.1.3" (README, line 119). By GitHub's contributor counts on
2026-11-08, John Regehr has the second most commits.

- **Division agrees with `ir-lean`.** A zero or poison divisor is UB, and so is `-1` with an `INT_MIN` or poison
  dividend (`Veir/Data/LLVM/Int/Basic.lean`, lines 357 and 368). That's `IRLean/Int.lean`'s `divOverflows`.
- **`freeze`:** "We currently always pick zero" (same file, lines 866–870). LangRef says "an arbitrary, but fixed,
  value". `ir-lean` stopped the model when this was written. Since F3, on 2026-11-09, it chooses a value for each run
  ([refinement](refinement.md#runs-that-make-choices)).
- **Refinement:** `.ub _, _ => True` and `.fail _, _ => True`, where `.fail` is the interpreter giving up
  (`Veir/Interpreter/Refinement/Basic.lean`, lines 100–107). So a source it can't run refines anything. In
  `ir-lean` a model stop refines nothing ([refinement](refinement.md#the-relation)).
- **Scope.** Memory as bytes with poison, branches, many intrinsics, no `samesign`. Its InstCombine is "a (very)
  partial implementation" (`Veir/Passes/InstCombine.lean`). It has tools to check its interpreter against Alive2 and
  `llubi`.

### Stage 1, item by item

| Stage 1 needs | Trivet | Lean-MLIR `main` | Covered? |
| --- | --- | --- | --- |
| A semantics faithful to LangRef | A fork, unreleased. Division by zero is UB. Poison divisors, `sdiv` overflow, `freeze` and `samesign` unstated | UB is poison, `sdiv i1` overflow is a value, `freeze` is 0, no `samesign` or intrinsics | No |
| Refinement certificates in Lean | Yes, for its 148 pairs, standard axioms only | Stated for 4,556 pairs, all `sorry`, kernel check skipped | Trivet, for its pairs |
| InstCombine's tests | No | A pipeline, through the lossy MLIR import. Solved in a harness, not kept as proofs | Partly |
| At least 500 transformations against Alive2, disagreements explained | 30 fixed-width cases, timeouts only | None | No |
| Known miscompilations | None | None | No |
| Candidate search | No | No | No |
| Real compiled functions | No | No | No |

### Semantics side by side

| Case | LangRef 23.1.3 | `ir-lean` | Lean-MLIR `main` | VeIR | Trivet |
| --- | --- | --- | --- | --- | --- |
| `udiv` or `urem` by 0 | UB | UB | Poison | UB | UB |
| Poison divisor | UB | UB | Poison | UB | Not stated |
| `sdiv INT_MIN, -1` | UB | UB | Poison | UB | Not stated |
| `sdiv i1 -1, -1` | UB | UB | `-1` | UB | Not stated |
| `freeze poison` | Arbitrary, fixed | Model stop. Since F3, on 2026-11-09, arbitrary and fixed, chosen each run | 0 | 0 | Not stated |
| `icmp samesign` | Poison if signs differ | Yes | Absent | Absent | Lost on import |
| `ctpop`, `ctlz`, `cttz` | | Yes | Absent | Yes | Added in the fork |
| A source the model can't run | | Refines nothing | | Refines anything | |

*Inferred*, read off the code and not run: each of these is wrong in LLVM, and Alive2 rejects it, but `src ⊑ tgt` holds
under Lean-MLIR's `main`. Any certificate built on it would fail stage 1's exit criterion.

1. **Speculated division.** `%a = shl i8 %x, 8` returned, which is always poison, to `udiv i8 %x, %y` returned. The
   target is UB at `y = 0`, where the source isn't.
2. **`freeze` in the target.** `ret i8 0` to `freeze (shl i8 %x, 8)` returned. The target may return anything.
3. **Width 1.** `ret i1 %x` to `sdiv i1 %x, true` returned. The target is UB at `x = true`.
4. **A lost flag.** If InstCombine adds `samesign` to the target, the import drops it, and the certificate is about a
   more defined target than LLVM produced.

### What to build, contribute and leave

- **Build stage 1, narrowed.**
  - Read InstCombine's and InstSimplify's `.ll` tests through `ir-lean`'s emitter, so `samesign`, `range`, `noundef` and
    intrinsics survive. Pair each with `opt -passes=instcombine`'s output, as `test-gen.py` does. At `llvmorg-23.1.3`
    there are 1,845 InstCombine test files with 38,708 `define`s, and 289 InstSimplify files.
  - Prove at fixed widths with `bv_decide`. Lean-MLIR's harness puts it at a 359 ms geometric mean per goal, in
    Alive2's range. Trivet's LLM proofs take minutes each.
  - Then do what no one has: compare with Alive2 over at least 500 pairs and explain every disagreement, and run the
    [known-miscompilation corpus](#benchmarks).
- **Contribute.**
  - To Lean-MLIR: the four counterexamples and `sdiv i1` as issues, and an Alive2 oracle like `tests/opcheck.py`.
    *Inferred:* its exhaustive check against `opt`'s constant folder (`SSA/Projects/InstCombine/LLVM/Enumerator.lean`)
    can't see UB, since the folder folds division by zero to poison.
  - To VeIR: `freeze`, `.fail` in refinement, and `samesign`. Compare its memory with `ir-lean`'s promises checked on
    each access.
  - To Trivet: ask for the 148 pairs and run them through `ir-lean`'s emitter and `Refines`, as an independent check of
    their fork's semantics.
  - To Lean-MLIR and VeIR: the flag-complete rewrites in `IRLean/Generic` as test cases for `bv_automata` and Blase.
- **Don't build:** an LLM proof-completion pipeline for peepholes (Trivet's), width-generic decision procedures
  (Lean-MLIR's, which are worth trying on `IRLean/Generic/BitVec.lean`), or a Hydra-style generalizer (Medusa, LPG).
- **Put the effort where the gate says:** memory, whole real functions, `Safe src → Refines src tgt → Safe tgt`, and
  search with Lean certificates.

Sharing a semantics needs UB kept apart from poison at the operation, which VeIR has and Lean-MLIR's `main` doesn't; a
`freeze` that's nondeterministic or refused; a source the model can't run that refines nothing; `samesign`; and
agreement on which axioms a certificate may use. The value types `Option (BitVec w)`, `PoisonOr (BitVec w)` and VeIR's
`Int w` are isomorphic. *Inferred:* a bridge is a lemma per operation, a few hundred lines.

## Recommendations

### Superoptimizer v2

**Candidate sources, all untrusted:**

1. **LLVM's issue tracker.** 672 issues labeled `missed-optimization` and `llvm:instcombine`, and 705 labeled
   `missed-optimization` that link an Alive2 page, already hold source and target pairs. Hydra, LPO, LPG,
   PeepholeBench and Trivet all draw on them.
2. **An LPO-style LLM proposer over real IR.** Extract dependent instruction sequences from functions `ir-lean`
   translates and from [llvm-opt-benchmark](https://github.com/dtcxzyw/llvm-opt-benchmark). Drop any that `opt` still
   optimizes on its own (LPO §3.2, Souper §3.1). Feed counterexamples back to the model (LPO Algorithm 1). LPO costs
   about $5 per 5,000 sequences with a cheap model (Table 4).
3. **`superopt.py`'s enumerator, widened.** More arguments, `select`, `icmp`, min and max and funnel shifts. Constants
   left symbolic and solved by the checker instead of enumerated (Minotaur §4.1). Dataflow pruning, which removed 65%
   of Souper's solver calls ([OOPSLA 2020](https://www-old.cs.utah.edu/~regehr/dataflow-pruning.pdf)). Every
   counterexample added to the inputs (Optgen §3.3, STOKE §5.2).
4. **Minotaur, run offline,** especially on vector code, where integer vector rewrites gave 75.6% of its speedup
   (Table 2). Souper is archived and builds against LLVM 18, so it isn't worth porting (*inferred*).

**Search.** Cut around each instruction with a depth bound, as Minotaur does (§2.4), so the search stays small while the
certificate is about the whole function. That needs a lemma that refinement of the cut gives refinement of the
function. `Refine.andThen_mono` and `val_map₂_mono` are the start of it. Rank candidates by where code runs (Souper §3).
Accept on `llvm-mca` uOps per target, which Minotaur found "a better performance predictor than cycles" (§4.3), and keep
`superopt.py --bench`'s timings for claims.

**Verification, cheapest first, with Lean the only acceptance:**

1. Drop a cut `opt -O3` already improves.
2. Run both sides on edge-case inputs, poison and UB-triggering ones included, natively and in the Lean model.
3. Filter on profitability before any solver call (LPO §3.3).
4. Alive2 with a short timeout, as a filter. "Incorrect" sends a counterexample back to the proposer and becomes a
   [checked refutation](#proof-tests). "Correct" or a timeout goes on to Lean. Pass `--fail-if-src-is-ub` (see
   [trust and tooling](#trust-and-tooling)).
5. Lean: the [store](#the-lemma-store) and cutting at shared values, then `bv_decide` at the fixed width, then
   width-generic procedures, then an LLM on a deterministic scaffold. Trivet's scaffold cut cost by 88% (Table 6).
6. The acceptance audit `tests/check_axioms.lean` does today, plus Aqueduct's rules: the source's declarations
   byte-identical, no `sorry`, `implemented_by` or `extern` (Appendix A).

**Generalizing a found rewrite.** Run Hydra's steps (Table 1, §3–6), but finish with a proof for every width instead
of checking each width up to 64, which is where Hydra and LPG stop:

- **Lift constants** into variables. Group instances by a shape hash that ignores constants, as Optgen does (§3.2),
  and anti-unify them, as babble does. The masks 127, 255 and 63 in the
  [popcount lemmas](lemma-reuse.md#gaps) become one `x &&& m`.
- **Find the conditions** with `bv_decide` over a ladder of widths: 1 to 8, then 16, 32 and 64. Flags are finite: an
  `add` and its rewrite carry at most 4 between them, so their condition is an exact table of 16 rows. Keep the weakest
  precondition, as Alive-Infer does.
- **Prove for every width** by the cheapest sound route: the width-1 theorem for linear mixed boolean-arithmetic,
  `bv_automata` where its fragment applies and its axioms are acceptable, or templates on lemmas like those in
  `IRLean/Generic/BitVec.lean`. Otherwise store a family proved for the widths listed, and say so.
- **Split poison off first** (*inferred*). Many refinements, such as `sub x, x` to `0`, are equalities once neither side
  is poison. Only the `BitVec` part needs width-generic machinery.

#### Benchmarks

| Track | Set | Measure | Compare with |
| --- | --- | --- | --- |
| Soundness | Alive2's last unit-test run, 137 failing tests on 2026-01-29, 45 of them InstCombine or InstSimplify ([dashboard](https://web.ist.utl.pt/nuno.lopes/alive2/)). Alive2's 358 tests that expect an error, 65 of them in `tests/alive-tv/bugs`, and `BugList.md`'s 101 LLVM bugs. [llvm-apr-benchmark](https://github.com/dtcxzyw/llvm-apr-benchmark)'s 106 miscompilations with reproducers, as of May 2025. 246 issues labeled `miscompilation` and `llvm:instcombine` | No certificate for a known-bad rewrite, and a checked refutation for each in scope | Alive2, and Trivet's 73 of 74 refuted |
| Coverage | InstCombine and InstSimplify tests at `llvmorg-23.1.3`, read through the emitter | Proved, refuted, unsupported or timed out, time per proof, lemmas reused | Alive2 over LLVM 11's tests: 2.5 h on 8 cores (§8.2) |
| Discovery | LPO's 25 issues filed after August 2024, then issues filed after a model's cutoff | How many found, confirmed and fixed | LPO 22, Souper 15, Minotaur 3 (Table 2) |
| Generalization | Hydra's 40 issues and LPG's 102 instances | Share generalized, and share proved for every width | Hydra 30 of 40, LPG 74 of 81 integer |
| Speed | Functions `ir-lean` translates, and llvm-opt-benchmark | `llvm-mca` uOps on two x86-64 CPUs and one AArch64, code size, then wall time | Minotaur 1.2–7.3% (§5.4). LPO's fixes within 2% on SPEC CPU 2017 (Fig. 5) |
| Cost | All of the above | Seconds and dollars per candidate, per proof, per accepted rewrite | LPO 6.7 s a case, Trivet $1.47 a proof |

Report against `clang -O3` at the same tag, never against unoptimized IR. IntOpt's 2.66× speedup is over unoptimized IR.
Against `-O3` it was better on 37 of 200 functions and wrong on 19 ([arXiv 2602.18511](https://arxiv.org/abs/2602.18511),
Fig. 4).

### The lemma store

These take up the gaps [lemma reuse](lemma-reuse.md#gaps) lists, among others.

**Normalize, so one meaning has one key.**

- **Hash the elaborated statement, not its text.** Today the key is a SHA-256 of the statement's text with whitespace
  collapsed (`prototypes/lemma-reuse/lemmas.py`, line 435). Lean's `Expr` equality is up to alpha-equivalence, and its
  hash ignores binder names (`src/Lean/Expr.lean`, lines 488–497 and 804). For a stable name, hash a fully explicit
  printing, as LeanHammer serializes premises with no notation and full names (§3.2.1).
- **Fix operand order** with core's `ac_nf`, on the stored statement and on the goal. That's "the same step, written
  differently".
- **Check idempotence,** as Mathlib's `simpNF` linter does (`Batteries/Tactic/Lint/Simp.lean`): admit a lemma only if
  the normalizer the use site runs leaves it unchanged. Otherwise it can never match.
- **Drop hypotheses that hold of everything,** such as `x ≤ 255#8` on 8 bits, and **require a witness** for the rest,
  so an inconsistent lemma can't get in.

**Generalize.** Constants become variables with side conditions, closed by `decide` at use, as Lemmanaid's templates
have holes (Table 1) and LPG turns a mask of 127 into any `V` with `0 ≤u V ≤u 127` (Table 3). Key a lemma by its shape
with the width abstracted, keep the widths proved under that key, prove a new width with `bv_decide` on a miss, and
promote the family to a theorem for every width when a proof exists. Keep the largest bound that holds, which is what
let 3 of the 128-bit proof's 7 lemmas carry over ([lemma reuse](lemma-reuse.md#whats-saved-and-when-its-reused-1)).
A lemma subsumes another with the same shape and a weaker precondition. Chompy decides that with an implication graph
between conditions ([FMCAD 2026](https://github.com/ninehusky/chompy)).

**Retrieve, exact first and learned last.**

1. The normalized hash.
2. A `DiscrTree` over conclusions, with frontier values and lifted constants as wildcards, as `simp`, `exact?` and
   `rw?` index lemmas (`src/Lean/Meta/DiscrTree/Main.lean`).
3. A `Selector` registered through core's premise-selection API (`src/Lean/LibrarySuggestions/Basic.lean`), so
   `grind +suggestions`, `simp? +suggestions` and `try?` see the store with no new tactic. Put it first: core's default
   selector, given `x ^^^ x = 0#w`, tied 81 `BitVec` lemmas and ranked `xor_self` 68th of 100, in a run during this
   study.
4. A model of which lemmas each goal used, as Isabelle's MaSh learns from proofs. `index.json`'s `used_by` is already
   that data.
5. Embeddings, only if the store outgrows one family. Learned retrievers find about a third of the right premises in
   their top 10 (LeanDojo, Table 1).

In any e-graph used for retrieval, a `Refines` lemma is a directed edge, never a merge (see
[rule inference](#rule-inference-e-graphs-and-generalization)).

**Version.** Keep a lemma's identity apart from its proof's validity. Identity is a hash of the normalized statement
and the normalizer's version. Validity also hashes the toolchain, the sources of everything it imports and the tactic
settings, which is Mathlib's cache scheme (`Cache/Hashing.lean`). The durable artifacts are the `.lean` source and, for
`bv_decide`, the LRAT proof that `bv_decide?` writes and `bv_check` replays without a SAT solver. In a run during this
study, `bv_check` took 1.74 s where `bv_decide` took 3.8 to 3.9 s. `.olean` files are bound to one Lean build
(`src/library/module.cpp`, lines 490–495), so they're only a cache. Lemma files as `module`s keep a re-proof from
rebuilding their users (the reference manual's "Modules and Visibility").

**Admit a lemma only if it's:**

1. checked, with its axioms audited;
2. canonical under the normalizer, with no vacuous or unwitnessed hypotheses;
3. not derivable from, or subsumed by, the store within a budget, which is Ruler's and Enumo's `minimize`;
4. not closed by `simp`, `bv_normalize`, `grind` or `decide` alone, which is Hipster's rule;
5. cheap to use, say under 1 s to check or replay, or split further;
6. as general as tests and Lean allow;
7. recorded with its provenance;
8. provisional until goals from two different families use it, and evicted after it goes unused. That's DreamProver's
   forgetting, not LEGO-Prover's accumulation.

**Measure reuse honestly:** on families that saved none of the lemmas, as LeanDojo's `novel_premises` split does; by
how much of an outside rule set the store derives, such as Alive's 433 InstCombine rewrites, cvc5's 115 RARE bitvector
rules and Cranelift's mid-end rules; and by compression, the size of the proofs plus the store (Stitch, babble).

### Proof tests

**One statement through every tier,** stopping at the first decisive answer, as one Kani harness runs as a fuzz test
and a proof, and Hypothesis backends share a property. The answer says which tier decided, and what the lower ones saw.

| Tier | Can decide | Answer | Never |
| --- | --- | --- | --- |
| 1: generated inputs, evaluated | A refutation | `counterexample`. Evidence `compiled_evaluation`, or `kernel_decide` where `decide +kernel` checks the ground instance cheaply | A pass. Without a counterexample, its record of inputs tried goes with whatever tier 2 or 3 answers, and alone it's `error/not_proved`, as today |
| 2: `bv_decide` at the real width, every input at small widths, a fuel or input-length bound | A refutation, or a proof within a bound | A new `bounded` status, with the bound named, such as `bound.width` or `bound.fuel`. `proved`, with reason `bounded_complete`, if every input in scope finishes within the bound | `proved` without that check. Hitting the bound is `bound_insufficient` |
| 3: a full proof from stored lemmas | A proof | `proved/kernel_checked` | |

- **A bounded result says what bounded it.** CBMC is run "with the –unwinding-assertion flag which ensures that we have
  fully unwound loops" ([SPE 2021](https://doi.org/10.1002/spe.2949), §3.1), and Kani reports an insufficient bound as
  "inconclusive beyond the given depth" ([arXiv 2607.01504](https://arxiv.org/abs/2607.01504), §2). ESBMC's "forward
  condition" checks the loops were fully unrolled, which makes a bounded result complete
  ([arXiv 1502.02327](https://arxiv.org/abs/1502.02327)). AWS-LC names each bound as a caveat, such as `InputLength`
  ([aws-lc-verification](https://github.com/awslabs/aws-lc-verification)). *Inferred:* fixed-width functions whose loops
  the width bounds, such as `popcount` and `crc32` a byte at a time, fit `bounded_complete`. A new status needs
  `ir-lean.verify/2`, since [verify](verify.md#the-contract)'s statuses are stable.
- **Guard against vacuous proofs.** A hypothesis of `False` "still comes back `proved`" ([verify](verify.md)). The
  precedents all flag it: QuickCheck's "Arguments exhausted", Hypothesis's `Unsatisfiable`, Kani's warning that
  `assume(false)` "makes the proof vacuously true", CBMC Viewer's unreachable code. Require tier 1 to find an input that
  meets every hypothesis, or attach an assumption saying none was found.
- **Generate bit patterns.** Use `superopt.py`'s `inputs()`: edges, single bits, runs and seeded random values. Add every
  input at small widths for width-generic claims, and `bv_decide`'s `solverMode := .counterexample` for rare failures.
  A few hundred inputs is enough before escalating: in mutation runs on 40 Python projects, 76% of the mutants
  property-based tests killed died within 20 inputs ([OOPSLA 2025](https://doi.org/10.1145/3764068), abstract and
  artifact only).
- **Shrink, store and replay.** Shrink deterministically with a recorded seed. Keep failing inputs keyed by the pinned
  statement and the generated module's hash, and replay them first, as Hypothesis's database does: "a cache that you
  never need to invalidate". Export each as a `--witness`, as a Lean lemma `¬ stmt` proved by `decide +kernel` where it
  reduces, and as a native test where no poison or UB is involved, as Kani's concrete playback does.
- **Say why a proof failed, as far as the evidence goes.** If tier 1 or 2 refutes, the claim is false. If tier 2 holds
  and tier 3 fails, the answer stays `bounded`, with the possible causes listed: a lemma or invariant too weak, a failure
  beyond the bound, or proof search that ran out. Why3 likewise splits a failed proof into "non-conformity",
  "subcontract weakness" and inconclusive ([arXiv 2108.02967](https://arxiv.org/abs/2108.02967)).
- **Don't use Plausible as tier 1 as it is.** "If no counter-examples are found, `plausible` behaves like `admit`"
  (`Plausible/Tactic.lean`, line 84), which leaves `sorryAx`. Its `BitVec` generator draws a number up to the current
  size, which never exceeds `maxSize`, 100 by default (`Plausible/Arbitrary.lean`, lines 89–92, and `Testable.lean`,
  lines 116 and 541). *Inferred* from the code: a default run never tries `0xFFFFFFFF` or `INT_MIN`. Its three-way
  result, success, gave up or failure, and its shrink count are worth borrowing.
- **Time to an error, not just to a proof.** Verus's authors broke proofs on purpose to measure it, since "developers
  most often wait on tools for failure feedback" ([SOSP 2024](https://www.andrew.cmu.edu/user/bparno/papers/verus-sys.pdf)).
  Track heartbeats, `simp` steps and `bv_decide` time per proof in CI, as AuthV2 brought its brittle verification
  conditions from 41 to 4 ([ICSE 2025](https://cdn.amazon.science/bb/40/22ac44f84f6d8eb625ac9666a00f/formally-verified-cloud-scale-authorization.pdf)).

**A first credible demonstration: compiler-rt's integer builtins against their own unit tests.** `ir-lean` already
proves 46 compiler-rt functions ([LLVM's own code](llvm.md#whats-proved)), and upstream tests them in
`compiler-rt/test/builtins/Unit` with hand-picked vectors, tables and `rand()` loops. At llvm-project's `main` on
2026-11-08, `popcountsi2_test.c` tries 6 edge values and 10,000 `rand()` values. *Inferred:* glibc's `RAND_MAX` is
2^31 − 1, so the random part never sets bit 31.

1. Make mutants of each builtin at the C and IR levels, compiled with the proofs' flags, with Mull or by extending
   `tests/llvm.py`'s injected bugs.
2. Run four arms: the upstream test, natively; tier 1; tier 2; and tier 3, the existing theorem against the mutant.
3. Report each arm's mutation score, time to kill and CI time, lines of spec against lines of test, and **how many
   mutants the upstream tests miss that tier 3 proves equivalent**. Mutation testing alone can't tell an equivalent
   mutant from a missed one: the small-scope study judged them "by manual inspection"
   ([Andoni et al.](http://users.csc.calpoly.edu/~gfisher/work/specl/documentation/related-work/testing/evaluating_small_scope_hypoth.pdf)).
4. Replay fixed bugs from `compiler-rt/lib/builtins`' history, expecting few: mature code may yield none.
5. Claim only the semantic content of the unit tests. Keep native smoke tests for the backend and ABI, which no
   theorem here covers.

zlib's `adler32` and `crc32`, already proved against their RFCs, are the second candidate, against zlib's end-to-end
tests.

**Limits the evidence predicts.** Expect specs to hold many of the bugs that remain: all 7 mismatches AuthV2's shadow
testing found were in its spec, and "no issues were found with tools or proofs". So test specs too, against
known-answer vectors as Aeneas does with KATs, and by mutation. IronSpec strengthens a spec and flags a mutant the
unchanged proof still passes, since it shows behavior the spec leaves open ([OSDI 2024](https://www.usenix.org/conference/osdi24/presentation/goldweber),
§4.3). mCoq mutates the code and flags a mutant every proof still accepts
([ASE 2019](https://doi.org/10.1109/ASE.2019.00057)), as `tests/llvm.py` already requires each injected bug to stop its
proof. Keep testing the boundary: the emitter, the C library model and the backend, as [trust](trust.md) lists them.
And keep testing the verifier: IronFleet's build reported success after a prover crash, and Dafny after Ctrl-C
(Fonseca et al., below).

### Trust and tooling

Things this study turned up that matter outside the gate:

- **`bv_decide`'s axioms changed shape.** Since Lean 4.29 each call adds its own axiom, named `…._native.bv_decide.ax_N`
  ([lean4#12217](https://github.com/leanprover/lean4/pull/12217)), and 4.35 removed `Lean.ofReduceBool` and
  `Lean.trustCompiler` (#14953). *Inferred* from the code: `leanchecker`'s replay doesn't rerun the LRAT check.
  `tests/check_axioms.lean` does, which is what makes the lemma store's "checked again where it's used" true.
  [Trust](trust.md) could say so.
- **Peers allow only the standard axioms.** Trivet (§3.1) and Aqueduct (Appendix A) refuse `bv_decide`'s. Decide whether
  a published certificate may rest on them, or must be re-proved without them.
- **`lake check` won't take these proofs.** Lean 4.35's `lake check` "fails if anything uses an axiom other than the
  standard ones" (release notes), so `ir-lean` still needs its own checker.
- **Alive2 counts an always-UB source as correct.** It prints "Source function is always UB" as a warning and counts
  the pair correct unless given `--fail-if-src-is-ub` (`tools/transform.cpp`, lines 557–566). `tests/alive.py` reads
  the counts and doesn't pass the flag.
- **Alive2 has open soundness reports exactly where `ir-lean` checks promises:** `memory(argmem: ...)`
  ([#1213](https://github.com/AliveToolkit/alive2/issues/1213)), `initializes` with `memory(...)`
  ([#1183](https://github.com/AliveToolkit/alive2/issues/1183)), and reads from dead allocas
  ([#1242](https://github.com/AliveToolkit/alive2/issues/1242)). Where the two disagree there, settle it from LangRef.
- **Two new oracles.** `llubi`, LLVM's UB-aware interpreter, ships in the dev shell's LLVM 23.1.3
  ([docs](https://llvm.org/docs/CommandGuide/llubi.html)). Vellvm's `tests/ub` has 363 UB assertions, each quoting
  LangRef 23.1, and compares Vellvm, `llubi` and sanitized clang (`tests/ub/README.md`). Adding `ir-lean` as a column
  there is a natural collaboration.
- **Choose an oracle by the direction of the error it catches** (*inferred* from each tool's stated design). Vellvm
  reports UB only where LLVM has it ("we won't rule a behavior as UB unless it actually is", its FAQ), so its UB
  verdicts catch a model with too little UB. crucible-llvm asserts on poison it produces, so its "defined" verdicts
  catch a model with too much. Alive2's "incorrect" is strong evidence, and its "correct" is bounded.

## The works

Each row says what the work does, where it overlaps with `ir-lean`'s plans, what to borrow or where to collaborate, and
where `ir-lean` is different.

### Superoptimizers and proposers

| Work | What it does | Overlap | Borrow or collaborate | Where `ir-lean` differs |
| --- | --- | --- | --- | --- |
| [Souper](https://arxiv.org/abs/1711.04422) ([code](https://github.com/google/souper)) | Synthesizes a cheaper right-hand side for integer DAGs cut from LLVM IR, with path conditions, checked by Z3. No `undef`, memory, FP or vectors (§2.1, §2.7). Made a Clang binary 4.4% smaller and 2% slower (§4). Archived, last pushed 2024-08-28, on LLVM 18 | The same problem as `superopt.py` | Path conditions, dropping what LLVM already does (§3.1), dataflow pruning, ranking by profile counts | A Z3 verdict, where `ir-lean` has a proof. No memory |
| [Minotaur](https://arxiv.org/abs/2306.00229) ([code](https://github.com/minotaur-toolkit/minotaur)) | Cuts around each instruction, enumerates candidates with symbolic constants solved by Alive2, ranks by `llvm-mca` uOps. Integer, FP and 165 x86 SIMD intrinsics. GMP 7.3% faster, libYUV 2.2–2.9%, SPEC CPU 2017 1.2–1.5% (§5.4). OOPSLA 2024, active, tracks LLVM `main` | The closest system to v2's shape | Cuts, symbolic constants, uOps, a cache keyed by cut. Run it offline as a candidate source | Trusts Alive2, Z3 and its own intrinsic semantics (§5.1) |
| [Hydra](https://users.cs.utah.edu/~regehr/generalization-oopsla24.pdf) | Generalizes a concrete optimization: drops what's unneeded, narrows to 4 bits, makes constants symbolic, finds preconditions including known bits. Checks widths "up to … 64 bits" one by one (§6.2). Fully generalized 30 of 40 InstCombine issues (§8.6). OOPSLA 2024 | AUTO-03, rewrites at every width | Its steps, and known bits as preconditions | Proves every width |
| [LPG](https://arxiv.org/abs/2603.18477) | An LLM proposes the generalization, Alive2 and `llvm-mca` check it. 74 of 81 integer cases against Hydra's 35 (Table 6). "we cannot directly verify a generalized optimization over arbitrary bitwidths" (§3.6) | The same | The LLM-proposes, checker-decides loop | Proves every width |
| [STOKE](https://arxiv.org/abs/1211.0557) | MCMC over x86-64. The cost counts wrong bits on tests plus latency. Its validator treats 64-bit multiply and divide as uninterpreted (§5.2). Montgomery multiplication 1.6× faster than `gcc -O3` (Fig. 1). Dormant since 2020 | Search past what enumeration reaches | A graded cost, and each counterexample as a new test | Assembly, and a validator sound only under its assumptions |
| [Optgen](https://i44vm2.informatik.kit.edu/uploads/publikationen/buchwald15cc.pdf), [LENS](https://thakur.cs.ucdavis.edu/assets/pubs/mangpo_thakur_ASPLOS16.pdf) | Optgen generates every local rule up to a cost, at 8 bits, and checks it at 32. It found 63 missing from GCC, LLVM or ICC (§5.2). LENS refines its test-input abstraction only where promising (ASPLOS 2016) | `superopt.py`'s pruning by behavior | Constant-blind shape hashing, and per-bucket inputs | Fixed widths |
| [LPO](https://arxiv.org/abs/2508.16125) | An LLM proposes a better version of an IR sequence, filtered by `llvm-mca` and checked by Alive2, with counterexamples fed back. 62 new missed optimizations, 28 confirmed, 13 fixed. Their fixes moved SPEC CPU 2017 by under 2% (Fig. 5). ASPLOS 2026 | Stage 3's search | The whole loop: extraction, dropping what `opt` already does, deduplication, feedback | Alive2 only |
| [Aqueduct](https://arxiv.org/abs/2610.30188) | Agents write faster Lean code and prove it equal, with the standard axioms only and no `native_decide` (Appendix A). 156 of 189 Verina functions. October 2026 | Proved optimization by LLMs | Its acceptance rules | Lean ports of programs, not compiled code |
| LLM work checked by tests or SMT | [PeepholeBench](https://arxiv.org/abs/2607.02684): agents' InstCombine patches were unsound in 0, 1, 5 and 7 of 19 cases, by model (Table VIII). [IntOpt](https://arxiv.org/abs/2602.18511): 19 of 200 wrong. [T-LLM](https://arxiv.org/abs/2608.14953): its CBMC check accepted 33.8% of wrong optimizations (§4.4). [SuperCoder](https://arxiv.org/abs/2505.11480): checked by tests only. [AlphaDev](https://www.nature.com/articles/s41586-023-06004-9): sorting routines reverse-engineered by hand into libc++ ([D118029](https://reviews.llvm.org/D118029)) | LLMs as proposers | Nothing to adopt but the warning | A proof is the only acceptance |

### Semantics and translation validation

| Work | What it does | Overlap | Borrow or collaborate | Where `ir-lean` differs |
| --- | --- | --- | --- | --- |
| [Alive2](https://www-old.cs.utah.edu/~regehr/alive2-pldi21.pdf) ([memory](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-mem-cav21.pdf), [code](https://github.com/AliveToolkit/alive2)) | Bounded refinement checking of LLVM IR pairs with SMT. Loops unrolled to a bound, and paths past it dropped (§7). Found 121 violations in LLVM's unit tests, and 47 bugs (§8.2). On SQLite3, 2,314 pairs proved and 2,102 timed out (Fig. 7), and 1 to 5 minute timeouts added under 5% (§8.4). MIT, tracks LLVM `main`. `ir-lean` pins `a68009c9e815`, 33 commits behind | `ir-lean`'s oracle today | Its memory refinement (CAV 2021, Figs. 3–5) as the draft for `Refine Mem`. Its tests as a corpus. Its timeouts as the list of where Lean adds most | A proof object. Unbounded loops. Every width. Properties beyond refinement |
| [Alive](https://users.cs.utah.edu/~regehr/papers/pldi15.pdf), [Alive-Infer](https://people.cs.rutgers.edu/~sn349/papers/pldi2017-alive-infer.pdf) | A DSL of checked peepholes. 8 of 334 InstCombine transformations were wrong. Checks every width up to 64 (§3.1.3). Alive-Infer finds the weakest precondition for 133 of 174 (PLDI 2017) | The InstCombine corpus, 433 rewrites | The corpus, and precondition inference | Every width, proved |
| [AliveInLean](https://web.ist.utl.pt/nuno.lopes/pubs/aliveinlean-cav19.pdf) | A Lean 3 checker proved to agree with its SMT encoding, still trusting Z3 (CAV 2019). Poison but no `undef`, no memory (§6.3). Archived, never ported to Lean 4 | Same prover family | The pattern of an executable semantics proved equal to an encoding | A theorem per instance, checked by the kernel |
| [Crellvm](https://sf.snu.ac.kr/publications/crellvm.pdf) | Passes emit relational proofs, checked by a Coq-verified checker (PLDI 2018). `mem2reg` and GVN in full. 4 new bugs (§7). *Inferred* from Fig. 6: checking cost 570 to 2,500 times the pass. Dormant since 2018 | Per-run certificates, as `tools/binding.py` binds | Hints checked by a checker proved once. Search outside the trusted base | Kernel-checked terms, not an extracted checker. Its InstCombine needed 1.9 lines of proof code per line of compiler (§6) |
| [Vellvm](https://www.cis.upenn.edu/~stevez/papers/ZB+21.pdf) | Rocq semantics on interaction trees, with an extracted interpreter (ICFP 2021). Two-phase memory where running out "refines anything" ([ICFP 2024](https://arxiv.org/abs/2404.16143), §3.3). 3.0 removed `undef`. Agrees with 328 of its 363 UB assertions. Doesn't yet check `memory(...)`, `captures` or `initializes`, or `inbounds` against object bounds (`docs/content/news/ub-2026-10-29.md`) | A faithful, provable LLVM semantics | Its UB suite, its interpreter as an oracle, its memory design | Checks the promises it doesn't. Proves theorems about specific compiled code. Opposite UB polarity |
| [crucible-llvm](https://github.com/GaloisInc/crucible/tree/master/crucible-llvm) | The semantics behind SAW. `freeze` "*always* returns the argument unchanged", and poison gives failing assertions (`doc/limitations.md`). Supports LLVM 23 in its next release | Whole-function safety on clang's output | An oracle with the opposite polarity | Kernel-checked proofs |
| [Towards removing `undef`](https://web.ist.utl.pt/nuno.lopes/pubs/byte-type-pldi26.pdf) | A byte type and a freezing load, so uninitialized memory can be poison and `undef` can go. Poison per bit. PLDI 2026 | `ir-lean` already refuses `undef` and reads uninitialized memory as poison | Track it | `Byte` tracks poison per byte, so *inferred:* the byte type would need a per-bit mask |
| [First-class verification dialects](https://www2.cs.utah.edu/~regehr/papers/pldi25.pdf), [mlir-tv](https://easychair.org/publications/preprint/LjP7) | SMT semantics for MLIR dialects: 5 upstream miscompilations found (PLDI 2025). Translation validation for MLIR, 433 of 2,467 unit-test pairs validated (CAV 2022, §7) | MLIR, later | Oracles for MLIR-to-MLIR steps, which a proof about lowered LLVM IR never sees | SMT, not Lean |
| [Crocus](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf), [Arrival](https://doi.org/10.1145/3764383), [arm-tv](https://www2.cs.utah.edu/~regehr/papers/arm-tv.pdf) | Cranelift's lowering and mid-end rules checked by SMT, per type from `i8` to `i64`, on every commit (`cranelift/isle/veri/README.md`). arm-tv lifts AArch64 to Alive2, 45 new bugs (OOPSLA 2025) | Every rewrite checked | Specs on rules | Every width, poison, Lean |

### Rule inference, e-graphs and generalization

| Work | What it does | Overlap | Borrow or collaborate | Where `ir-lean` differs |
| --- | --- | --- | --- | --- |
| [egg](https://arxiv.org/abs/2004.03082), [egglog](https://arxiv.org/abs/2304.04332), [small proofs](https://arxiv.org/abs/2209.03398) | E-graphs and equality saturation. egg's explanations make it "the first certifying equality saturation engine" (FMCAD 2022). egglog's proofs are new: "Proof preparation" in 2.0.0, February 2026 (`CHANGELOG.md`) | An untrusted proof finder | Explanations replayed as Lean `rw` chains | A union is two-way, and `Refines` isn't (below) |
| [Ruler](https://arxiv.org/abs/2108.10436), [Enumo](https://ajpal.github.io/assets/files/enumo-paper.pdf), [Chompy](https://github.com/ninehusky/chompy) | Infer rewrite rules by enumerating terms, matching their values on samples, checking, and dropping what's derivable. Ruler checks bv4 exhaustively and bv32 with Z3 (§6.2). Enumo's `minimize` keeps a rule only if the rest can't derive it (§4.3). Chompy adds conditional rules through implication between conditions (FMCAD 2026) | `superopt.py` does Ruler's core already | Derivability as the store's quality bar. Chompy's implication graph for subsumption | Fixed widths, no poison |
| [Isaria](https://sgt-pl.com/papers/compgen.pdf) | Synthesizes rules on one vector lane, generalizes them to the real width, and checks them again there (ASPLOS 2024) | Generalizing widths | Synthesize small, generalize, check again | Checks again for every width |
| [lean-egg](https://github.com/marcusrossel/lean-egg) | An egg tactic replaying explanations as Lean proofs ([POPL 2026](https://doi.org/10.1145/3776667)). "only handles on the order of < 100 theorems" (§7). Its README: "no longer being developed … use Lean's `grind` tactic instead" | A Lean proof finder | Use `grind`. `grind?` records which lemmas a proof used | |
| [babble](https://arxiv.org/abs/2212.04596), [Stitch](https://arxiv.org/abs/2211.16605) | Learn a library of abstractions from a corpus, by anti-unifying e-classes (POPL 2023) or by compression (POPL 2023) | The store as compression of proofs | Anti-unification for the constants gap. Compression as a measure | |
| [Library Learning Doesn't](https://arxiv.org/abs/2410.20274) | Audits LEGO-Prover's logs: across four runs, lemmas were reused verbatim 0, 0, 0 and 1 times (Table 1) | A warning for any store | Count reuse across distinct goals | |
| [CADE 2019](https://arxiv.org/abs/1905.10434), [IsaRare](https://m-fleury.github.io/ox-hugo/LachnittFleuryAnivaReynoldsBarbosaNoetzliBarrettTinelli-TACAS24.pdf) | 113 of Alive's 433 InstCombine rewrites depend on the width, and 88 were proved for every width by SMT (§4.2). IsaRare proves 84 of cvc5's 115 bitvector rules for every width in Isabelle (TACAS 2024, Table 1) | Every-width rewrites | IsaRare's rules as a seed corpus | Poison and flags |
| [Cranelift's aegraphs](https://www.cfallin.org/blog/2026/04/09/aegraph) | An acyclic e-graph rewritten eagerly in one pass. About 2% better code, at 7–8% more compile time. Keeping several forms bought about 0.1% | E-graphs in a production compiler | Eager rewriting with a good rule set got most of the value | |
| [Rewrite system showdown](https://arxiv.org/abs/2605.19005) | Equality saturation against stochastic search: "neither technique comes out to be Pareto optimal". A directed rule is an equivalence in an e-graph and a refinement in stochastic search | v2's search | Keep refinement rules out of e-graph unions | |

What the evidence says about checking small widths:

| Kind of rewrite | Do small widths suffice? | Evidence |
| --- | --- | --- |
| Linear sums of bitwise expressions | Yes, width 1, proved in Lean | `Blase/Blase/Fast/MBA.lean`, line 627, in Lean-MLIR |
| Bitwise ops, `+`, `-`, multiplication and shifts by constants, comparisons | Decidable for every width | `bv_automata` ([slides](https://www.llvm.org/devmtg/2025-04/slides/technical_talk/bhat_peephole.pdf)) |
| Width-dependent constants, `lshr`, `ashr`, division, overflow flags, shifts compared with `w` | No finite check is known to suffice | 4-bit and 32-bit grammars give different equivalences ([SAT 2019](https://theory.stanford.edu/~barrett/pubs/NRB+19.pdf), Table 1). Shifts: 0 of 9 proved for every width (CADE 2019, §4.2). `ir-lean`'s own `i1` and `w = 0` counterexamples (`tests/generic_rewrites/RewriteCounter.lean`) |

### Lemma libraries and Lean's tooling

| Work | What it does | Overlap | Borrow or collaborate | Where `ir-lean` differs |
| --- | --- | --- | --- | --- |
| [LeanDojo](https://arxiv.org/abs/2306.15626) | Traces Lean projects, and retrieves premises with a trained model. Recall at 10: 38.4% (Table 1). Retrieval adds 3 to 4 points of proofs (Table 2). Superseded by [LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Store lookup | The `novel_premises` split, as a test of reuse | Machine-made lemmas, where exact keys work |
| [Lean Copilot](https://arxiv.org/abs/2404.12534) | LLM tactic suggestions and premise selection in Lean. Retrieves "from a fixed snapshot" of Mathlib (README) | | The pattern, now in core's API | Can't see a project's own lemmas |
| [LEGO-Prover](https://arxiv.org/abs/2310.00656), [DreamProver](https://arxiv.org/abs/2604.26311), [Seed-Prover](https://arxiv.org/abs/2507.23726) | Growing lemma libraries. LEGO-Prover reached 22,532 skills (§4.3.1), with almost no reuse when audited. DreamProver keeps fewer than 100 by forgetting the least used, and 58% get reused (§3.2, §4.3). Seed-Prover conjectures thousands of lemmas per problem and ranks them (§2.3) | The store and a discovery engine | Keep it small, forget, rank. Record requests that failed, for later | Lemmas about generated code, rechecked where used |
| [LeanHammer](https://arxiv.org/abs/2506.07477) | Premise selection plus Zipperposition, rebuilt by Duper. Recall at 32: 72.7% (Table 2). ICLR 2026 | Retrieval | Its normalized premise printing (§3.2.1) | |
| Lean core's premise selection | `src/Lean/LibrarySuggestions/Basic.lean`: an API for selectors, used by `grind +suggestions`, `simp? +suggestions` and `try?`. The default engine is Sine Qua Non, and MePo is built in too | Store lookup | Register the store as a selector | |
| `DiscrTree`, `simpNF` | `simp`'s index, keyed by structure (`src/Lean/Meta/DiscrTree/Main.lean`). Mathlib's linter that a simp lemma's left side is in normal form | Normalization and retrieval | Both, directly | |
| [`bv_decide`](https://doi.org/10.1145/3763167) | Verified bitblasting to SAT, with LRAT certificates checked in Lean (OOPSLA 2025, abstract only). `bv_check` replays a stored certificate (`src/Init/Tactics.lean`, line 1925). Fixed widths only: at a symbolic width it reports "a potentially spurious counterexample", in a run during this study | Tier 2, and lemma checks | Store each lemma's LRAT | |
| Mathlib's [cache](https://github.com/leanprover-community/mathlib4/blob/master/Cache/Hashing.lean) | Hashes each file with its imports, the toolchain and the manifest | Versioning | The scheme | |

### Testing and verification tools

| Work | What it does | Overlap | Borrow or collaborate | Where `ir-lean` differs |
| --- | --- | --- | --- | --- |
| [QuickCheck](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf), [Hypothesis](https://doi.org/10.21105/joss.01891) | Random testing of properties. QuickCheck's errors split "roughly evenly between errors in test data generators, errors in the specification, and errors in the program" (§6.6). Hypothesis shrinks the choices that made an input, keeps a database of failures, and lets a solver backend answer "verified", which a later failure reports as unsound ([internals](https://hypothesis.readthedocs.io/en/latest/reference/internals.html)) | Tier 1 | Shrinking, the database, replay first, flagging too many discards | A pass is never a proof here |
| [Plausible](https://github.com/leanprover-community/plausible) | Lean 4's property testing. Success, gave up or failure, with shrinking | Tier 1 in Lean | Its result type and shrink count | It admits on success, and samples small `BitVec`s ([above](#proof-tests)) |
| [SmallCheck, LeanCheck](https://lemonidas.github.io/pdf/ETNA.pdf), [Korat](http://users.csc.calpoly.edu/~gfisher/work/specl/documentation/related-work/testing/evaluating_small_scope_hypoth.pdf) | Every input up to a size. LeanCheck solved 82% of Etna's tasks, SmallCheck 35% (ICFP 2023). Korat killed 89–99% of mutants at scopes 3 to 7, with kill rates rising "even after achieving complete coverage" | Small widths | Exhaustive small widths before `bv_decide` | |
| [CBMC at AWS](https://doi.org/10.1002/spe.2949), [Kani](https://arxiv.org/abs/2607.01504), [ESBMC](https://github.com/esbmc/esbmc) | Bounded model checking with unwinding assertions. CBMC: 171 entry points, 83 issues fixed, a median harness of 88 s. Kani found 11 bugs tests and fuzzing missed, one where 16,777,216 fuzz runs found nothing and Kani took 20 s (Table 2). Concrete playback turns a counterexample into a unit test | Tier 2 | Unwinding assertions, playback, one harness for fuzzing and proof | Kernel-checked proofs about optimized IR |
| [Rust std verification](https://arxiv.org/abs/2606.17374) | 16,748 generated harnesses, 11,970 verified. It "has not uncovered any previously unknown memory safety vulnerabilities" (§4.4) | Proof tests at scale | Report each kind of result apart | |
| Dafny, [Verus](https://www.andrew.cmu.edu/user/bparno/papers/verus-sys.pdf), F\* | SMT-based verifiers. Dafny's counterexamples are only potential, and it measures brittleness ([reference manual](https://dafny.org/latest/DafnyRef/DafnyRef), §13.7). Verus measures time to an error (SOSP 2024). HACL\*'s F\* code is in Python 3.12's `hashlib` ([what's new](https://docs.python.org/3/whatsnew/3.12.html)) | Tier 3 | Brittleness in CI, time to an error | Proves what clang emitted |
| [Liquid Haskell with G2](https://billhallahan.github.io/files/lazy-cf-symex.pdf), [Why3](https://arxiv.org/abs/2108.02967), [Creusot](https://github.com/creusot-rs/creusot) | G2 finds counterexamples for 97.7% of 7,550 failed refinement-type checks (PLDI 2019, abstract). Why3 tells a code bug from a weak contract | Failed tier 3 | Classify the failure | |
| [Aeneas and SymCrypt](https://arxiv.org/abs/2609.15648) | Rust translated to Lean: 237 KLOC of Lean prove 16.7 KLOC of Rust. Trusts "the compiled native_decide and bv_decide tactics". Tests run in both Rust and Lean, and KATs test the specs | Very close: real code in Lean, `bv_decide`, agents | Shared `BitVec` libraries. KATs on specs | Unoptimized MIR, no memory model. `ir-lean` works after LLVM's optimizer |
| [SAW on AWS-LC](https://github.com/awslabs/aws-lc-verification), [s2n-bignum](https://github.com/awslabs/s2n-bignum) | Proofs about clang's output against Cryptol specs, with named bounds such as `InputLength`. HOL Light proofs about machine code, with a table of risks and co-simulation of the ISA model in CI (`SOUNDNESS.md`) | Proofs about compiled code | Named bounds, the risk table | |
| [Cedar](https://arxiv.org/abs/2407.01688), [AuthV2](https://cdn.amazon.science/bb/40/22ac44f84f6d8eb625ac9666a00f/formally-verified-cloud-scale-authorization.pdf), [AWS practice](https://doi.org/10.1145/3729175) | Cedar: Lean models proved, the Rust tested against them. "We also did not port our unit tests to Lean because we can instead prove properties of interest" (§3). Proofs found 4 bugs, differential and property-based testing 21. AuthV2: 7 mismatches in 10^15 shadow tests, all in the spec. AWS in 2025 puts proofs "alongside" unit and integration tests | Proofs alongside tests | Differential testing against the model. Shadow testing | Proves the compiled code, not a model of it |
| [seL4](https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf), [CompCert](https://users.cs.utah.edu/~regehr/papers/pldi11-preprint.pdf), [Airbus](https://www.di.ens.fr/~delmas/papers/fm09.pdf) | seL4: use found 16 defects, the C proof another 144 (§5.2). CompCert: no wrong-code bug in the verified middle end after "about six CPU-years" of Csmith (§3.1). Airbus has replaced unit tests with "Unit Proof" since 2002 under DO-178B, and still tests on hardware (§4.1, §5.3) | Evidence | | |
| [Fonseca et al.](https://doi.org/10.1145/3064176.3064183) | 16 bugs in three verified distributed systems, none in verified protocol code. Two were the toolchain reporting success after a prover crash and after `SIGINT` (EuroSys 2017) | Where bugs go | Fail closed, as `tools/verify.py` does | |
| [Property-based testing in practice](https://conf.researchr.org/details/icse-2024/icse-2024-research-track/90/Property-Based-Testing-in-Practice), [mutation study](https://doi.org/10.1145/3764068) | 30 interviews at Jane Street (ICSE 2024). Each property-based test found about 50 times as many mutants as the average unit test, in mutation runs on 40 Python projects (OOPSLA 2025, abstract and artifact only) | Evidence | A small tier-1 budget | |

## Limits

- **Some papers were read only as an abstract or metadata:** both OOPSLA 2025 bitvector papers, the OOPSLA 2025 mutation
  study, the CAV 2018 s2n paper, HACL\*'s CCS 2017 paper, and G2. Their numbers above come from abstracts or
  artifacts, and say so.
- **Trivet's semantics can't be checked.** Its fork isn't released, so its treatment of poison divisors, `sdiv`
  overflow, `freeze` and `samesign` is unknown.
- **The four Lean-MLIR counterexamples weren't run.** They're read off `Semantics.lean`.
- **Alive2's dashboard shows no run after 2026-01-29,** though its README says it runs daily. Whether it continues
  elsewhere is unknown.
- **Counts are point-in-time.** GitHub label counts include issues migrated from Bugzilla, and InstCombine's `define`
  count includes helper functions.
- **Timings from Lean runs during this study,** of `bv_check` and the default premise selector, are one run each on one
  machine.
- **Upstream counts for Souper, Minotaur and Hydra** are as their papers report them. Later LLVM commits weren't traced.
- **No search for Rocq or Isabelle work on LLVM peepholes in 2025–2026 turned anything up.** That's not proof there is
  none.
