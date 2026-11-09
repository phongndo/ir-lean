# Binding a proof to LLVM's C++

How a proof about an LLVM pass would be tied to the C++ that implements it: the options, the evidence for each, and one
choice. This is [BIND-01](llvm-verification-tasks.md#bind-01-what-binding-to-the-implementation-means). It changes
nothing `ir-lean` claims. It says what a `code-binding` claim's evidence is, and whether "every pass, done" is reachable
on that evidence. When it was written, proving every optimization in LLVM was
[parked](roadmap.md#whats-parked-and-what-stays) as an end goal. Since 2026-11-09 it's the main program, in
[chunks](chunks.md), and this note's gates are its binding track: a chunk's G3 is binding by the rule below. For
binding a certificate to one run of a pass, which is a different thing, see [binding](llvm-proof-binding.md). For what
any theorem means, see [trust](trust.md).

The share of InstCombine's own test transformations `ir-lean` can certify, which S1 measures, was the parked goal's
progress metric, and is chunk 1's G1 since [2026-11-09](roadmap.md#six-decisions-of-2026-11-09-after-69). That's
translation validation, the kind of evidence [candidate 2](#2-certifying-passes) gives: it measures progress, and under
the rule below it never makes a pass done. This note is about what would.

Facts here were checked on top of commit `3d7bffb` on 2026-11-09, on x86-64 Linux in the dev shell, with LLVM 23.1.3 at
`llvmorg-23.1.3`, its clang, and Lean 4.35.0. Claims marked *inferred* are this note's reading, not a measurement or a
source's statement. The [prototype](#the-prototype) is in [`prototypes/binding`](../prototypes/binding), outside the
library, the build and CI.

## The decision

**Recommendation: compile the pass and prove its compiled code, with a hand-written Lean model in the middle.** For
each unit of the pass's C++, a Lean model like [#47's](llvm-cpp-correspondence.md) is proved right for every input,
and the unit's IR, compiled by the pinned clang from the pinned source and translated by `ir-lean`, is proved to compute
what the model computes on every heap that holds well-formed IR. The second proof replaces #47's trusted translation, so
the pair meets the task list's rule as written. The one other route that could, a C++ semantics written here, needs the
same proofs and trusts more.

**The fallback, if that stops at a gate below:** keep the models and their all-input proofs, and tie them to the C++
the way #47 does, with every line quoted at a pinned hash and the model compared with the pinned `opt`. That evidence
is finite, so under the current rules `code-binding` can then never be complete, and no pass is ever done. Counting
anything would need the end condition rewritten, as [below](#the-fallback-and-what-it-does-to-done).

**Whether "100%" is reachable.** Under the rule, only a route that proves the C++ itself can reach it, and nothing
measured here says the recommended one does at the pinned scale. The [prototype](#the-prototype) passes the first gate
on one 30-line function, with three of its callees cut. InstCombine's 15 files, with InstSimplify and the two analysis
files they lean on most, are 404,004 IR instructions, of which the emitter translates 3.1% of functions today, and the
inventory's 913 anchor files are 851,964 lines before their callees. At the proof costs this repo has measured,
InstCombine alone would be several times the size of seL4's functional-correctness proof (*inferred*,
[below](#what-it-would-cost)). *Inferred:* small passes, and the libraries every pass shares, are within the route's
reach. Whether InstCombine is, the gates measure, and the [stop rules](#when-to-stop) say when to stop trying.

## What the rule asks

The task list's [definition](llvm-verification-tasks.md#translation-validation-isnt-proof-for-all-inputs):

> `code-binding`: The pass's C++, at the hashes the inventory pins, is proved to make only those rewrites. Counts toward
> done: Yes. A binding with other hashes is stale and refused.

And its end condition: proofs "tied to its actual implementation", where "timeouts, unsupported cases, admitted proofs
and proof-to-code gaps count as unfinished". BIND-01's own trust gap: "Every route trusts the C++ compiler that built
the pass, unless it reasons about the binary."

So a candidate meets the rule only if its evidence is a proof, about the code at the pinned hashes, that it makes no
rewrite outside the proved set. Three parts of the rule do the work:

- **Proved.** Finite evidence, however much, isn't proof. A comparison with `opt` on generated inputs, or a certificate
  for each run, is evidence.
- **The pass's C++.** A proof about a different program, such as a model someone wrote or a pass generated from Lean,
  is about that program.
- **At the hashes the inventory pins.** A pin move makes the claim stale until it's checked again.

## The scale, measured

[`prototypes/binding/census.sh`](../prototypes/binding/census.sh) compiles 18 of the pinned source files with
[`targets.toml`](../tests/llvm/targets.toml)'s flags for LLVM, which are upstream's Release flags as far as they change
the IR, plus `-fno-strict-aliasing`. They're InstCombine's 15 `.cpp` files, InstSimplify's pass, and the two analyses
both lean on most, `InstructionSimplify.cpp` and `ValueTracking.cpp`. It runs `build/ir-lean --report` on each, and on
the 18 linked into one module.

| | |
| --- | --- |
| Inventory | 913 anchor files, 851,964 lines. Anchors are entry files only: `instcombine`'s is `InstructionCombining.cpp`, one of 15 |
| InstCombine | 55,303 lines in its 15 `.cpp` files, and 56,244 with `InstCombineInternal.h`. The directory has 17 files with `CMakeLists.txt` |
| The 18 files, compiled and linked | 2,540 functions, 1,479 of them `linkonce_odr` copies of inline functions and templates, and 404,004 IR instructions. The median function has 68 instructions. 62 have more than 1,000, and the largest, `InstCombinerImpl::visitCallInst`, has 8,666 |
| Translated today | 146 of 3,703 function definitions file by file, or 3.9%, and 78 of 2,540 linked, or 3.1%. Linking removes duplicate copies, and puts more functions in a call cycle with one that's refused |
| Calls leaving the 18 files | 172 distinct functions, such as `Constant::getSplatValue`, `SmallVectorBase::grow_pod`, `APInt`'s slow paths and `BinaryOperator::Create` |

What stops the 2,462 linked functions that don't translate, by the first reason the emitter gives. Fixing one can expose
the next, so this is a floor on the work, not a list of it.

| First refusal | Functions | Whose |
| --- | --- | --- |
| A call to a function outside the module | 665 | [BIND-02](llvm-verification-tasks.md#bind-02-implementation-closure)'s closure, linked in |
| `!nonnull` or `!range` on a load | 602 | The emitter, [BIND-05](llvm-verification-tasks.md#bind-05-translating-llvms-own-c): each is poison when broken, as `noundef` and attributes already are |
| `memory(...)` on a call | 301 | BIND-05: the callee's promise has to be checked, or the callee translated with it |
| A call to an inline or template copy, `linkonce_odr` | 260 | BIND-05: a policy for the one-definition rule, which [Phase 3](roadmap.md#phase-3-c-and-rust-demonstrations) left open |
| A call to a function that was itself refused | 191 | Follows the rest |
| `!alias.scope` or `!noalias` | 176 | [SEM-06](llvm-verification-tasks.md#sem-06-memory-for-refinement)'s scoped `noalias`, refused until modelled |
| A type: vectors of pointers, `double` | 82 | BIND-05, and SEM-05 for `double` |
| A recursive function of more than 200 blocks | 45 | The emitter's limit |
| An instruction, mostly `inttoptr` | 42 | SEM-06's provenance and exposure. LLVM's `PointerIntPair` and `PointerUnion` hide bits in pointers |
| A global, an intrinsic such as `llvm.memmove`, a vtable constant, an attribute, `undef` | 98 | BIND-05, one at a time |

## The candidates

| | Meets the rule | Trusted, beyond what every theorem here trusts | At the pinned scale |
| --- | --- | --- | --- |
| 1. Compile the pass, prove its IR | **Yes** | clang's lowering of the pinned source, and that the shipped `opt` was built the same way | The whole closure through `ir-lean`, with LLVM's heap in the model. 3.1% of the slice above translates today |
| 2. Certifying passes | No: per run | Nothing about the pass. The emitter and the model, per run | Already works per instance, as [`tools/binding.py`](llvm-proof-binding.md). Every run costs a proof |
| 3. Hand-written models | No: the translation is a person's | The translation, backed by quotes and finite comparison | Linear in lines of C++, and needs no C++ in the model |
| 4. Generate the pass from Lean | No: another program | A generator from Lean to C++, and the glue to LLVM's data structures | A rewrite of each pass, which upstream would have to adopt |
| 5. A C++ semantics, from Clang's AST | Yes, in principle | A C++ semantics written here, which has to agree with what clang compiles | As 1, plus a C++ semantics |

Every route also trusts Lean's kernel, IRLean's semantics of LLVM IR, `ir-lean`'s emitter, and the reader of the
statement, as [trust](trust.md) says.

### 1. Compile the pass and prove its compiled code

Build each unit of the pass's C++ to IR with the pinned clang and the build's flags, translate it with `ir-lean`, and
prove the generated Lean makes only the proved rewrites. This is how [87 functions from LLVM itself](llvm.md) are
already proved, including `APInt::tcAdd`. The difference is the heap: a pass reads and writes LLVM's own objects, so a
theorem has to say what bytes in memory mean as IR.

- **The rule:** met. The theorem is about the IR of the code at the pinned hashes, as the pinned compiler lowers it.
  Its gap is the compiler's, which BIND-01 says every route has.
- **Trusted base:** clang lowering the pinned source to IR, and the same compiler building the shipped `opt` from
  equivalent IR. The shipped binary comes from nixpkgs' build, so its flags have to be the recorded ones, and nothing
  here compares them yet. The clang that compiles a pass is built by an earlier LLVM, whose InstCombine is the kind of
  code under proof: the usual bootstrapping trust, not a circular argument. The layout of LLVM's objects isn't trusted
  for soundness: it's in the IR, as offsets and value IDs, and the theorem's hypotheses say what a well-formed heap is,
  so a wrong layout makes a theorem that says nothing about real heaps, not a false one. That real heaps meet those
  hypotheses is BIND-04's to prove, and until it is, the theorem states it as an assumption.
- **At the pinned scale:** [measured above](#the-scale-measured). The closure has to be linked and translated whole, or
  each call out of it is a stop the theorem has to rule out. The emitter refuses most of the code today, for reasons
  that are each finite work, but there are many of them.
- **From SEM-06:** provenance and exposure for `ptrtoint` and `inttoptr`, since LLVM's ADT stores bits in pointers and
  `DenseMap` hashes them. Scoped `noalias`, which clang's inliner adds. Not the relation between a source's and a
  target's memory: that's for proving a rewrite that touches memory, which is the all-input dimension's work.
- **From the emitter:** the table above, then virtual calls, which it already handles as a choice among functions of
  the type whose address is taken. Over a linked closure, that's every override, and a bound on them is BIND-02's.
- **Proof size and Lean's memory:** [what it would cost](#what-it-would-cost).
- **A pin move:** every unit whose source, or anything it inlines, changed gets new IR. So can one whose source didn't,
  because the pin moves clang too: the dev shell's clang is the pinned LLVM's. Proofs follow the IR's blocks, so a
  change breaks the lemmas for the blocks it touched, and the rest have to be checked again. The roadmap's "proof lines
  broken per LLVM bump" is the number to watch, and nothing has measured it.

### 2. Certifying passes

Instrument each pass to emit a certificate with each run, and check it in Lean, as
[Crellvm](https://sf.snu.ac.kr/publications/crellvm.pdf) did for `mem2reg`, GVN and part of InstCombine with a checker
proved in Coq.

- **The rule:** not met. Each certificate is about one run, which is translation validation, and the task list says
  that [never counts](llvm-verification-tasks.md#translation-validation-isnt-proof-for-all-inputs) for all inputs. The
  pass's C++ is outside the trusted base on purpose, so nothing is proved about it.
- **What it would change about "100%":** done would stop being a property of LLVM and become one of each compilation.
  With a checker that stops the build when a certificate fails, the guarded compiler never emits an uncertified rewrite,
  for every input it finishes on. That's CompCert's argument for its validated passes, and it's a theorem about the
  compiler plus checker, not about the pass. A pass that's wrong on some input stays wrong, and the build stops there.
  "Every pass proved" would become "every run checked", which is a different and weaker claim about LLVM, and a
  stronger one about any one program.
- **Trusted base:** Lean's kernel, IRLean and the emitter, on each run's IR. The instrumentation is untrusted.
- **At the pinned scale:** per instance, this exists: `tools/binding.py` binds one `opt` run, and
  [`tests/passes.py`](passes.md) scores LLVM's own tests that way. A certifying pass would add hints so the proof is
  found rather than searched for. Crellvm's InstCombine needed 1.9 lines of proof-generating code per line of compiler
  (§6), and *inferred* from its Fig. 6, checking cost 570 to 2,500 times the pass.
- **From SEM-06:** `Refines` for memory, for any pass whose runs change code with memory. Most do.
- **From the emitter:** only what the optimized IR uses, not LLVM's C++.
- **Proof size and Lean's memory:** per run. One binding verify took about 10.5 s and peaked at 1.5 GiB in #52's pilot.
  The total grows with use, not with the pass.
- **A pin move:** the instrumentation is a patch to LLVM, rebased on each pin.
  [Crellvm's](https://sf.snu.ac.kr/crellvm/) downloads are one patched release, and it's been dormant since 2018. The
  checker changes only when IRLean does.

### 3. Hand-written models, with correspondence evidence

The [#47](llvm-cpp-correspondence.md) approach, scaled up: a Lean function per C++ function, step by step in the same
order, proved right for every input, with every code line quoted at a pinned hash and the answers compared with the
pinned `opt`.

- **The rule:** not met. The model is proved, but that the model is the C++ is a person's reading, backed by finite
  evidence. That's a proof-to-code gap, which the end condition counts as unfinished. It can't count as `code-binding`
  under these rules, however many quotes and comparisons back it. It can be one half of candidate 1, which is how the
  recommendation uses it.
- **Trusted base:** the translation. #47 shows what backs it: 42 quotes in 7 files at pinned SHA-256s, every code line
  of three functions quoted, and 3,938 generated `add`s answered as `opt` answers them. Its own list of what that misses
  includes vectors, constant expressions, and the pass around the function.
- **At the pinned scale:** linear in lines of C++, with no C++ in the model. #47 is a 203-line model and a 408-line
  proof for the 121 lines of its three functions, about 1.7 and 3.4 lines per line of C++. The proof is the all-input
  work, which every route needs. *Inferred:* at that ratio InstCombine's models alone are about 94,000 lines.
- **From SEM-06:** only for the models' all-input proofs of rewrites that touch memory.
- **From the emitter:** nothing.
- **Proof size and Lean's memory:** #47 checks in about 12 s, under Lean's `-M` 2000 MB.
- **A pin move:** the anchors fail where a quoted line changed. A person diffs, re-reads and re-translates, and the
  comparison runs again. Nothing finds a changed line that changes meaning without changing what's quoted, such as a
  changed constant in a header nobody quoted.

### 4. Generate the pass from Lean

Write the pass in Lean, prove it, and generate the C++ that replaces LLVM's.
[Vellvm's `vmem2reg`](https://www.cis.upenn.edu/~stevez/vellvm/Zhao13.pdf) (PLDI 2013) did this for `mem2reg`, in Coq,
extracted to OCaml, with code about as fast as LLVM's. [Alive](https://users.cs.utah.edu/~regehr/papers/pldi15.pdf)
(PLDI 2015) generated C++ for 334 InstCombine rewrites it had checked.

- **The rule:** not met. It proves the generated pass, whose files aren't the ones the inventory pins. LLVM's pass stays
  unproved. It would count as proving LLVM's pass only after upstream adopted the generated code, and then that code
  would need binding by candidate 1, unless the generator is proved too. LLVM hasn't adopted Alive's generated
  InstCombine, which a [later paper](https://people.cs.rutgers.edu/~sn349/papers/icse2016-alive-loops.pdf) found makes
  compilation loop forever on 184 sequences of rewrites.
- **Trusted base:** the generator, unless proved, and the glue between the generated code and LLVM's data structures,
  which is BIND-04's problem again.
- **At the pinned scale:** a second implementation of each pass, kept in step with upstream's.
- **From SEM-06 and the emitter:** SEM-06 for the all-input proofs. The emitter isn't involved.
- **A pin move:** upstream's pass moves and this one doesn't. The two diverge, and nothing says how far.

### 5. A C++ semantics, or Clang's AST translated to Lean

Translate the C++ itself rather than its IR. [BRiCk](https://skylabsai.github.io/BRiCk) does this for Rocq: `cpp2v`
turns Clang's AST into Rocq terms, over a separation logic for C++ built on Iris, and it's used on a C++
microhypervisor. [Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust to pure Lean, but it relies on Rust's
borrows to need no heap, and C++ has nothing in their place. A search found no C++-to-Lean translator past a work in
progress for C.

- **The rule:** met in principle, if the semantics is right.
- **Trusted base:** larger than candidate 1's. Both trust clang to build the binary. This one also trusts a C++
  semantics written here to agree with what clang compiles, across templates, overload resolution, object lifetimes and
  the rest of the standard. Candidate 1 reads what clang decided instead.
- **At the pinned scale, SEM-06 and the emitter:** the same proof work as candidate 1 over the same heap, plus a
  semantics for C++'s object model in place of SEM-06's memory.
- **A pin move:** as candidate 1, and the semantics has to follow clang's front end too.

Two more were looked at and left out. **Extracting the rewrites** from the C++, by symbolic execution or a Clang plugin
reading `PatternMatch` code, trusts the extractor to find all of them, so it's evidence, though a good source for
[INV-04](llvm-verification-tasks.md#inv-04-rewrite-level-inventory). **Reasoning about the binary**, by lifting `opt`'s
machine code as [arm-tv](https://www2.cs.utah.edu/~regehr/papers/arm-tv.pdf) lifts AArch64, removes the compiler from
the trusted base, which candidate 1 can't, and adds a machine semantics to everything candidate 1 needs.

## The recommendation, in detail

### Two theorems per unit

A unit is a C++ function as the pinned build compiles it, after inlining. For each:

1. **The model is right,** for every input: what
   [PASS-03](llvm-verification-tasks.md#pass-03-peephole-rewrites-for-all-inputs) and
   [AUTO-03](llvm-verification-tasks.md#auto-03-from-instances-to-every-width) prove anyway. #47's
   `simplifyAddInst_sound` is one.
2. **The compiled code is the model:** on every heap that holds well-formed IR, as
   [BIND-04](llvm-verification-tasks.md#bind-04-llvms-ir-in-memory-in-lean)'s abstraction says, the generated function
   returns what the model returns on that IR, and for code that changes IR, leaves the heap holding what the model
   produces.

The two compose into the claim the rule asks for, and neither trusts the translation that #47 does. The model is the
seam: one person can read it against the C++, and the proofs on each side don't change when the other's do. A
callee's theorem 2 is a lemma at each call, so a pass is bound bottom-up through BIND-02's closure.

### What a `code-binding` claim's evidence is

What [BIND-03](llvm-verification-tasks.md#bind-03-an-independent-verifier) has to replay, and refuse if any part
fails:

- The closure's files, from BIND-02, each with the SHA-256 the inventory records.
- The IR, compiled from those files by the pinned clang with flags recorded in the claim, and built again byte for byte.
- `ir-lean`'s Lean for that IR, generated again byte for byte, as `tools/binding.py` already checks for instances.
- Theorem 2 for each unit, with its statement built by the verifier from the generated function's name, the model's,
  and BIND-04's abstraction, and compared as an `Expr`, as `tools/binding_check.lean` compares a certificate's.
- Theorem 1 for each model, and the composition of the two into the claim that every rewrite the code makes is one of
  the proved ones.
- Lean's kernel replaying all of it through `leanchecker`, on the axioms BIND-03's policy allows.
- No cut. A call the theorem rules out by stopping the model, as the prototype does, makes the claim partial.

### Gates

Each gate depends only on the ones before it, and its check is what passes it. None has a date.

| Gate | Shows | Needs | Passed when |
| --- | --- | --- | --- |
| B0 | One real function, compiled at the pin, proved to compute #47's model | Nothing new | Passed by the [prototype](#the-prototype), with 6 calls cut and the heap as a hypothesis |
| B1 | BIND-04 for reading IR: `Value`, `Use`, `ConstantInt`, `APInt` and `Type`, as the matchers read them | Nothing new for these objects. The rest of BIND-04 needs SEM-06's provenance rules | The abstraction is proved preserved by the constructors a small pass calls, and the [layout probe](../prototypes/binding/layout_probe.cpp) agrees with it on the pinned `libLLVM` |
| B2 | The emitter takes the matcher layer whole: calls inside a linked closure, `!nonnull` and `!range`, `memory(...)` on calls, a one-definition-rule policy | BIND-02's closure for `simplifyAddInst` | `isKnownNegation` translates with no cut, and the share of the 18-file slice that translates is measured again |
| B3 | All of `simplifyAddInst` bound to #47's model at every width, with its closure | B1, B2, and `APInt`'s slow paths proved | Theorem 2 for it, with no cut and no delegation left in the model |
| B4 | Code that changes IR: InstSimplify's loop, with `replaceAllUsesWith`, use lists and erasing | B3, and BIND-04 for writing | Theorem 2 for `InstSimplifyPass::run`'s loop, given B3 for every opcode it reaches |
| B5 | A whole pass, end to end, which is [BIND-06](llvm-verification-tasks.md#bind-06-the-first-pass-bound-end-to-end) | B4, BIND-03, PASS-03, PASS-05 | BIND-06's acceptance, for the pass whose closure BIND-02 finds smallest |

### When to stop

Switch to the fallback, and say so in the task list, if any of these holds:

- Lines of proof per IR instruction for theorem 2 don't fall from B0 to B3, as lemmas about the heap get reused. The
  roadmap asks the same of [proof cost](roadmap.md#when-to-stop-or-change-course).
- B2 can't be passed without the emitter trusting something it refuses today, such as the one-definition rule, without
  a stated reason the maintainer accepts.
- A function the closure needs can't be checked by Lean's kernel within its memory limit, as already happens for
  `isprint`'s `step` ([LLVM's own code](llvm.md#what-the-proofs-turned-up)), and splitting it doesn't help.
- The proofs break on each pin move faster than they can be repaired.

## What it would cost

Measured: what this repo has paid to run compiled code in Lean, from [status](status.md). 0.63 lines per IR instruction
for `crc32_z`'s blocks, 1.56 for `adler32_z`'s, and 4.4 for `updatewindow`'s, which is mostly loads and stores, as a
pass's code is. In total, 9.5 to 14.6 lines of Lean per line of C. The prototype's `isKnownNegation` took
[4.1 lines per instruction, and 39 per line of C++](#what-it-cost). For comparison, seL4's functional-correctness proof
is [about 200,000 lines of Isabelle for 8,700 lines of C](https://trustworthy.systems/projects/OLD/l4.verified/numbers),
about 23 per line.

*Inferred:* at 0.63 to 4.4 lines per instruction, running the 404,004 instructions of the 18-file slice is 250,000 to
1.8 million lines of Lean, before any invariant about the heap. At 10 to 23 lines per line of C, InstCombine's 55,303
lines are 550,000 to 1.3 million, which is 3 to 6.5 times seL4's proof, and at the prototype's 39 they're 2.2 million.
That's before ValueTracking, InstructionSimplify and the IR library InstCombine calls.

Lean's memory is per module, not per closure: `ir-lean --split` writes a module per function, and each proof imports
only what it uses. The bound that matters is the largest function. `visitCallInst`'s 8,666 instructions are 3.4 times
`inflate`'s 2,569, whose translation [takes 8 s and 1.5 GB](status.md) to check. The prototype's 214 took 0.5 s and
839 MiB. *Inferred:* the largest functions in a pass will need splitting by hand, or more than a CI runner's memory.

## The fallback, and what it does to done

If the recommendation stops, keep theorem 1 for each model, and replace theorem 2 with #47's correspondence evidence:
quotes of every code line at pinned hashes, checked on each run, and the model compared with the pinned `opt` on
generated inputs. Per-run certificates, candidate 2, can add to that evidence, by checking each run's rewrite against
the model, and they're still finite.

Under the current rules, that evidence can't make `code-binding` complete, so no pass is ever done, and "100%" is out of
reach. For it to count, the end condition would have to change from "tied to its actual implementation" to "tied to a
model a person checked against it, with that evidence", and the task list would need a dimension for it, such as
`code-correspondence`, which a verifier replays but which `verified_done` doesn't count. That's a change to what
"proved" means for the program, so it's the maintainer's to make, written in the roadmap with its reason, as the
roadmap's rule for a gate that moves.

## The prototype

The recommended route on the smallest real case that #47's model covers: `llvm::isKnownNegation`, from
`ValueTracking.cpp`, which `simplifyAddInst` calls for its `add.negation` step. Its 30 lines, 22 of them code, inline
`PatternMatch`'s templates, and compile at the pin to 214 IR instructions in 57 blocks.
[`prototypes/binding/README.md`](../prototypes/binding/README.md) has the files and how to run them.

### What it proves

[`isKnownNegation_compiled`](../prototypes/binding/KnownNegationProof.lean), with the model's `isKnownNegation` from
[`SimplifyAddModel.lean`](../tests/cpp_correspondence/SimplifyAddModel.lean) on the right:

```lean
theorem isKnownNegation_compiled {x y : Operand w} (hw : w ≤ 64) (V : View M loc ty x y M.next)
    (R : StackRoom M) :
    ∃ M', KnownNegation._ZN4llvm15isKnownNegationEPKNS_5ValueES2_bb (some (ptrOf (loc x.ident)))
        (some (ptrOf (loc y.ident))) (some 0#1) (some 1#1) M =
      Outcome.ok (some (BitVec.ofBool (isKnownNegation x y)), M')
```

In words: take any memory where the two operands' objects are where `loc` says, laid out as
[`HeapView.lean`](../prototypes/binding/HeapView.lean) says, at distinct addresses, with nothing running that limits
what may be read, and with room for the two stack slots the function allocates. Call the function `ir-lean` generated
from the compiled C++ with `NeedNSW` false and `AllowPoison` true, as `simplifyAddInst` does. At any width up to 64, it
returns the model's answer, and never stops the model or reaches undefined behavior.

| Step | Result |
| --- | --- |
| Compile at the pin | `ValueTracking.cpp`, at the SHA-256 #47's `anchors.json` pins, with `targets.toml`'s flags for LLVM, by the dev shell's clang 23.1.3 |
| Take the function out | `llvm-extract`, and `check.sh` checks its text is unchanged apart from attribute group numbers and the order of predecessors in comments |
| Translate | **Stops here on its own.** `ir-lean` refuses the function for `memory(read)` on its call to `APInt::countLeadingZerosSlowCase`, and behind that are calls to two functions defined in other files and to an inline template's `linkonce_odr` copy. [`cut.py`](../prototypes/binding/cut.py) replaces the 6 calls to those 3 functions with calls that stop the model, and then it translates whole |
| Check the translation | 0.5 s and 839 MiB |
| Check the layout | [`layout_probe.cpp`](../prototypes/binding/layout_probe.cpp): 63 facts hold on objects the pinned `libLLVM` builds, from `i1` to `i128`, including that vector types are the only ones whose masked ID is 18 |
| Prove it | `HeapView.lean`'s 374 lines, 270 of them general lemmas about reading memory and the function's own stack slots, and `KnownNegationProof.lean`'s 493. 3.1 s and 928 MiB to check, the standard axioms only, `leanchecker` replays both, and `tests/check_axioms.lean` confirms the theorem is about the function `ir-lean` generated |
| Show the hypotheses can hold | `Example.view`: a heap built byte by byte, with `X = sub i8 0, Y`, meets `View`, and on it the function returns true |
| Must-break mutants | Two bugs put into the C++, swapping `m_Specific(B), m_Specific(A)` and matching `X = 0 - X`, change the IR and each stops the proof at the part it changes |

`check.sh` runs all of it in 28 s, with a peak of 1.56 GiB.

### Where it stops

- **The cuts.** The theorem is about the function with its 6 calls out of the module replaced by stops. It holds of
  the compiled function as clang emitted it only by an argument on paper: `= Outcome.ok` says no run it covers reaches
  a cut, and on runs that don't, the two functions run the same instructions. The cuts are on the paths for widths
  over 64, which call `APInt::countLeadingZerosSlowCase` in `APInt.cpp`, for vectors, which call an inline template's
  `matchVector`, and for `NeedNSW`, which calls `Instruction::hasNoSignedWrap` in `Instruction.cpp`. Removing them is
  gate B2.
- **The scope.** Widths up to 64, scalars, `NeedNSW` false and `AllowPoison` true, which is what `simplifyAddInst`
  passes. The model has no vectors.
- **The heap is a hypothesis.** Nothing proves that LLVM's constructors build heaps that meet `View`: that's BIND-04.
  A wrong layout would make the theorem say nothing about real heaps, rather than something false. The probe is
  evidence for one build on one target, and it found that APInt's invariant, which the compiled code relies on, isn't
  kept by a release build when a caller breaks a precondition.
- **The flags.** `-fno-strict-aliasing`, as for [LLVM's own code](llvm.md#what-it-assumes), and nothing compares them
  with nixpkgs' build of `opt`.
- **Reading only.** Nothing here changes IR. Code that does is gate B4.
- **The rest of #47.** `simplifyAddInst` and `foldOrCommuteConstant` stay translations a person checked.

### What it cost

867 lines of Lean for 214 IR instructions, about 4.1 an instruction, or 2.3 without the general lemmas. That's about
what `updatewindow` cost, 4.4, the repo's other proof of code that's mostly loads and stores, and not cheaper. Against
the 22 code lines of C++, it's about 39 lines of Lean each, since those lines inline `PatternMatch`'s templates.
*Inferred:* the general lemmas are what later functions would reuse, and B1 to B3 measure whether they do.

## What this means for the other tasks

| Task | What changes |
| --- | --- |
| [BIND-02](llvm-verification-tasks.md#bind-02-implementation-closure) | It's the first need: the census's largest refusal is calls out of the module. Its closure is the link set for candidate 1, and its bound on virtual calls is the emitter's set of targets. Since 2026-11-09, [`simplifyAddInst`'s closure](llvm-closure.md) is recorded: 2,070 functions and 240,134 IR instructions by direct calls, in 154 files with every copy of its inline functions, of which `ir-lean` translates 287 linked in one module, and the census still gives 3.1%. Its indirect calls have no usable bound yet, and B2 needs a one-definition-rule policy the maintainer accepts, which that page proposes |
| [BIND-03](llvm-verification-tasks.md#bind-03-an-independent-verifier) | Replays the evidence [above](#what-a-code-binding-claims-evidence-is) |
| [BIND-04](llvm-verification-tasks.md#bind-04-llvms-ir-in-memory-in-lean) | The prototype's `HeapView.lean` is a first slice of it. The [probe](../prototypes/binding/layout_probe.cpp) found APInt's invariant, that the bits above the width are 0, is only an assertion: in the pinned release build, `ConstantInt::get(i1, 7)` holds the word 7. So clean words are a hypothesis of every theorem, and each constructor has to be shown to keep them, under its own preconditions |
| [BIND-05](llvm-verification-tasks.md#bind-05-translating-llvms-own-c) | The census is its list, in order. The prototype's cut is its first item: a call out of the closure as a model stop, made by the emitter instead of by editing the IR |
| [BIND-06](llvm-verification-tasks.md#bind-06-the-first-pass-bound-end-to-end) | Gate B5. Pick the pass by the size of its closure, not of its entry file |
| [PASS-01](llvm-verification-tasks.md#pass-01-analyses-are-sound) | An analysis is bound the same way: its model is what its soundness is proved about |
| [PASS-03](llvm-verification-tasks.md#pass-03-peephole-rewrites-for-all-inputs) | Its proofs are theorem 1, about models written to be bound later |
| [PASS-05](llvm-verification-tasks.md#pass-05-composition-through-pipelines) | Unchanged: composition is about the claims, however they're bound |

## Limits of this note

- The census compiles 18 files at x86-64 with upstream's flags as `targets.toml` approximates them, not the closure,
  and not nixpkgs' exact build of `opt`. Its refusals are first reasons only.
- The cost figures extrapolate from C code this repo proved, which reads memory far less than a pass does, and from
  one read-only function. They could be low. They don't include invariants about the heap, which nothing here measures.
- The prototype is one read-only function. Code that changes IR, which is what makes a rewrite, isn't tried.
- The literature here is what the prior-art study read, and the few sources cited above. A search found no proof about
  a production compiler pass's own C++ at InstCombine's size, which isn't proof there is none.

## Reproduce

```console
nix develop
cmake -S . -B build -G Ninja && ninja -C build ir-lean
lake build IRLean
prototypes/binding/check.sh build/ir-lean build/binding-proto
tools/measure.py run --label census --heavy --max-tree-rss-mb 12000 -- \
  prototypes/binding/census.sh build/ir-lean build/binding-proto
```
