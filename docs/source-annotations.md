# Annotations on a refinement's source

Whether the emitter could read `!tbaa`, `noalias` and the other annotations that only add undefined behavior as if
they weren't there, on the source of a refinement and nowhere else, so that sopt, the superoptimizer, can read the IR a
default `-O3` build gives. Where the argument holds, where it breaks, what it would take, what it would buy and what it
would cost. For what any theorem means, read [trust](trust.md) first, and for the relation, [refinement](refinement.md).

**This is a proposal for the maintainer.** Nothing here is built or decided. [The decisions it
needs](#decisions-for-the-maintainer) come first.

LangRef is quoted from `llvm/docs/LangRef.md` at `llvmorg-23.1.3`, the pin, and LLVM's code from the same tree. Facts
about the repo were read at `c0d070c` on 2026-11-10. Numbers about real kernels are from the kernel corpus, a proposal
that isn't committed (`docs/kernels.md` on its own branch, measured on 2026-11-09 and 2026-11-10 at `df3e997`): they're
a proposal's numbers, and the [estimate](#what-it-would-buy) built on them is marked as one.

## The conclusion

- **It holds, with rules.** Reading these annotations as dropped is sound on a refinement's source: LangRef requires
  a transformation to drop any metadata attachment it can't preserve, and lets optimization attributes be "freely
  dropped", so the IR without them refines the IR with them, and a target that refines the first refines the second.
  It's unsound anywhere else: on a target, in a memory-safety theorem, or in any claim about what the source itself
  does.
- **The rules that make it hold:** the target is read by the emitter as it is today, which refuses every one of these,
  so the rewritten function is emitted with all of them dropped; a family is dropped whole, never in part; and
  certificates, verdicts and the board record that the source was read this way, while msc, ptf and every claim that
  isn't a refinement's source refuse it.
- **It buys nothing before F4.** Every annotation in scope sits on a memory access or a pointer, and a function with
  memory has no `Refines` claim until F4 ([refinement](refinement.md#the-relation)). A slice win doesn't need it: a
  slice has no loads, and the llama.cpp slices are already cut from a default `-O3` build.
- **After F4, by the proposal's numbers,** about 13 more of its 85 named kernels, and at most 15, would get past
  every refusal the proposal saw when read as built, besides the 3 that translate as built today. That's an estimate:
  the proposal records a function's first reason only, and the IR a default build gives isn't the relaxed IR it
  measured.
- **What it costs isn't known.** The rewritten function loses the alias facts later passes and code generation use.
  [What it costs](#what-it-costs) says how to measure that.
- **One break isn't this note's, and F4 has to settle it either way:** `noalias` on a caller's argument covers
  every access during the call, so a rewrite that changes which pointer an access is *based* on can make a caller
  undefined, whether or not the rewritten function has any annotation.

## Decisions for the maintainer

| # | Decision | Recommendation | The alternative, and what it costs |
| --- | --- | --- | --- |
| 1 | Whether to adopt the reading at all | **Yes, with the rules here, built with or after F4.** It gives whole-function wins on the IR a project ships, without modeling type-based and scoped aliasing | Model them instead, which the roadmap's [open questions](roadmap.md#open-questions) leave open and which needs a tag on every byte for `!tbaa` ([trust](trust.md#known-gaps-in-the-model)). Or prove only on IR compiled with `-fno-strict-aliasing`, as the kernel corpus proposes, about a different IR from the one that ships |
| 2 | What the target keeps | **Nothing in scope: the rewritten function drops every one, and its own `noalias` arguments go from its definition and from every call to it in the module** | Keep them on instructions the rewrite didn't touch. That rests on an argument about LLVM the model can't check, and it fails as stated for scope declarations and `noalias` arguments ([below](#a-rewrite-of-part-of-a-function)) |
| 3 | Value metadata: `!range`, `!nonnull`, `!align`, `!dereferenceable` and `!dereferenceable_or_null` on a load | **Model them**, as their attribute forms are. Then the target may keep them, and the search may use them | Drop them with the rest. Sound, and the search loses facts it could have used |
| 4 | How a win proved this way is labeled | **A third value for the source IR, "as built, read with its annotations dropped"**, beside the kernel corpus's "as built" and "relaxed", with the kinds dropped and the drop-only control's result on the board | Count it as "as built". That hides that the theorem rests on LangRef's rule for dropping, and that the target lost alias facts |
| 5 | Callers' `noalias` | **F4 says which relation its refinement keeps for pointers**, LangRef's *based on* or the model's provenance, before any whole-function win with memory counts | Leave it as a stated assumption on each win, which the roadmap calls "the last resort, and doesn't work for refinement" ([Phase 0](roadmap.md#phase-0-semantic-fidelity-and-trust-infrastructure)) |

## The claim

### In the repo's terms

Write `drop(P)` for IR `P` with every annotation in [the table below](#each-annotation) removed, and `⟦P⟧` for what
LLVM allows `P` to do. `IRLean.Refines src tgt` says `tgt` only does what `src` allows. [Trust](trust.md) gives the
condition for such a theorem to say the same of LLVM: "the source must have no more UB than LLVM, and the target no
less." The mode reads the source as `drop(src)` and the target as it is, and the claim is this chain:

1. `⟦tgt⟧` only does what the model's `Tgt.f` allows, because the model's target has no less undefined behavior than
   LLVM's. The target is read by the emitter as it is today, which refuses every annotation in scope, so there's
   nothing of this kind in it to read less of.
2. `Tgt.f` only does what `Src.f` allows: the theorem, `IRLean.Refines Src.f Tgt.f`.
3. `Src.f` only does what `⟦drop(src)⟧` allows, because the model has no more undefined behavior than LLVM on
   `drop(src)`. That's the fidelity every refinement already rests on, and for memory it's F4's
   ([refinement](refinement.md#what-it-says-about-llvm)).
4. `⟦drop(src)⟧` only does what `⟦src⟧` allows, by LangRef's rules for dropping, [next](#langrefs-rule).

So `⟦tgt⟧` only does what `⟦src⟧` allows. Steps 1 and 3 are the model's fidelity, as for any theorem, and step 4 is a
reading of LangRef, which can't be a theorem. Nothing in it needs LangRef to say exactly what each annotation means,
only that dropping it is allowed, and the table below checks each one's own wording points the same way.

It runs one way. `Src.f` has less undefined behavior than `⟦src⟧`, which is the dangerous direction for anything that
says what the source does: a theorem that the source returns, is safe, or meets a spec, is about `drop(src)`, and
`⟦src⟧` can still be undefined through a tag.

### LangRef's rule

Two rules carry step 4:

- **Metadata:** "A transformation is required to drop any metadata attachment that it does not recognize or cannot
  preserve." The exceptions it names are attachments to globals: `!func_sanitize`, `!type`, `!absolute_symbol`,
  `!implicit.ref` and `!associated`, none of them in scope. A rule that requires dropping is only right if dropping is
  always allowed, which is how this note reads it.
- **Parameter attributes:** "Optimization attributes do not have to match between call-site and function: The
  intersection of their implied semantics applies. Optimization attributes can also be freely dropped." It names
  `noalias`, `nonnull` and `dereferenceable` as optimization attributes, against ABI attributes such as `byval`, which
  "cannot be safely dropped".

LLVM's code reads them the same way. `Instruction::dropUBImplyingAttrsAndMetadata`, in `llvm/lib/IR/Instruction.cpp`,
keeps `!range`, `!nonnull` and `!align` when it moves an instruction, since they "produce poison, so they are safe to
speculate", and drops the rest, since "`!noundef` and various AA metadata must be dropped, as it generally produces
immediate undefined behavior."

`llvm.experimental.noalias.scope.decl` is a call, not an attachment, so neither sentence covers it. LangRef says it
"identifies where a noalias scope is declared", and nothing else about a run. Once every `!alias.scope` and `!noalias`
naming its scope is dropped, it identifies nothing a run can see, and deleting it is deleting a call with no effect.
That's this note's argument, not LangRef's words.

### Each annotation

Each row is something the emitter refuses today, by
[`tests/llvm_scope/ir-features.json`](../tests/llvm_scope/ir-features.json), with what LangRef says breaking it does.
Dropping is sound on the source for every row, by the rules above, and for the scope declaration by the argument after
them. The last column is what this note recommends.

| Annotation | Where it goes | LangRef 23.1.3 | Recommendation |
| --- | --- | --- | --- |
| `!tbaa` | Loads, stores, calls that access memory | "If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined." Undefined behavior only, through a pair of tagged accesses | Drop on the source, and on the target |
| `!tbaa.struct` | `llvm.memcpy` | The gaps between the fields it lists are "padding which does not carry useful data and need not be preserved." That's a choice, not undefined behavior: a copy may leave those bytes as anything. Dropping it copies every byte, one of the runs it allowed | Drop on both |
| `!alias.scope`, `!noalias` | Memory accesses, and `fence` | "If accesses from different collections alias, the behavior is undefined." | Drop on both, with every declaration of their scopes |
| `llvm.experimental.noalias.scope.decl` | A call | Where a scope is declared. Its position matters: in LangRef's loop example, outside the loop the two pointers "are noalias across *all* iterations", inside "only within *one* iteration" | Drop on both, always with every `!alias.scope` and `!noalias` naming its scope |
| `noalias` on an argument, or on an argument at a call | The function's definition, a call site | Pointers *based* on the argument and pointers not based on it don't both access a location modified "during the execution of the function". "If there are other accesses not based on the argument or return value, the behavior is undefined." It's an optimization attribute | Drop on the source. The target drops it from its definition and from every call to it in the module |
| `noalias` on a call's result | A call outside the module | The function "acts like a system memory allocation function". An optimization attribute. On a function's own result it's modeled already, as a check that stops the model ([trust](trust.md#what-the-model-does-at-its-edges)) | Drop on the source. The call touches memory, so it waits for F4 anyway ([calls](calls.md#calls-that-touch-memory)) |
| `llvm.access.group`, `llvm.mem.parallel_loop_access` | Memory accesses in a loop whose `llvm.loop` lists `llvm.loop.parallel_accesses` | "If there is a loop-carried dependency, the behavior is undefined." | Drop on both |
| `!invariant.load` | Loads | "every memory location read by that operation must contain the same value at all points in the program where that memory is dereferenceable; otherwise, the behavior is undefined." | Drop on both |
| `!invariant.group` | Loads, stores | Every access to the same pointer "can be assumed to load or store the same value". Experimental, and it "must be dropped when replacing one pointer by another based on aliasing information" | Drop on both. Clang adds it for C++ only with `-fstrict-vtable-pointers` |
| `!captures` | Stores of a pointer | Dereferencing a copy stored with `!{!"address"}` "would result in undefined behavior" | Drop on both |
| `!callees` | Indirect calls | "If ... any callee is not among the set of functions provided by the metadata, the behavior is undefined." | Drop on both |
| `!nofree`, `!noalias.addrspace` | Pointer values, memory accesses | `!nofree`: "the memory pointed by the pointer will not be freed after the attached instruction", and LangRef doesn't say what breaking it does. `!noalias.addrspace`: undefined if the object is in a listed address space | Drop on both. For `!nofree` it's the rule above that makes this sound, since its own text doesn't say |
| `writable`, `dead_on_unwind`, `dead_on_return` | Arguments | `writable` has the caller promise the bytes can be stored to, so LLVM may add "spurious stores on entry". The other two make memory written through the argument poison after the function unwinds or returns. Each only adds undefined behavior or poison, and none is an ABI attribute, the kind that "cannot be safely dropped" | Drop on both |
| `!range`, `!nonnull`, `!align` | Loads, and `!range` on calls | "a poison value is returned instead", for a value outside the range, null, or misaligned. Poison only | Model them, as the `range`, `nonnull` and `align` attributes are ("value promise" in the file). Dropping is the fallback |
| `!dereferenceable`, `!dereferenceable_or_null`, and `dereferenceable_or_null` as an attribute | Loads of a pointer, arguments, results | Undefined unless the value is "dereferenceable at the current program point", or null for the second | Model them, as `dereferenceable` is. Dropping is the fallback |

Two refused kinds have no meaning for a run, and belong in the file's *assumed* class, independently of this proposal:
`!nontemporal`, which "tells the optimizer and code generator that this load is not expected to be reused in the
cache", and `!mem.cache_hint`, which "is purely a performance hint: dropping or ignoring it must not change the
observable behavior of the program". A target may keep them.

Out of scope here: call-site promises such as `memory(...)` or `readonly` at a call, which the external-calls lane
refuses and which LangRef also lets be dropped, and FLAC's `"no-signed-zeros-fp-math"`, a string attribute LangRef at
the pin doesn't mention, so the rule above says nothing about it. `!noundef` is modeled already.

## Where it breaks

Nine places to look, each with whether it sinks the idea and what fixes it. None sinks it.

| # | Where | Sinks it? | Fixed by |
| --- | --- | --- | --- |
| 1 | A target that keeps an annotation | No | Reading the target as today, which refuses them |
| 2 | Part of a family dropped | No | Dropping a family whole |
| 3 | A rewrite of part of a function, the rest keeping theirs | No | Dropping in the whole function |
| 4 | `noalias` and which pointer an access goes through | Not this note's | In its own function, dropping it ([decision 2](#decisions-for-the-maintainer)). In its callers, F4 |
| 5 | Certificates and binding | No | A field in the manifest, and the replay that's already there |
| 6 | msc, ptf and claims about the source | No | Refusing the mode there, with tests |
| 7 | Inside a pipeline | No: a cost | Measuring it |
| 8 | What the search can no longer prove | No: a cost | Modeling the value metadata |
| 9 | Memory has no refinement yet | No: it waits | F4 |

### A target that keeps them

If the target keeps an annotation the model doesn't read, the model's target has less undefined behavior than LLVM's,
which [trust](trust.md#known-gaps-in-the-model) calls the wrong direction for a target. A rewrite that reorders two
accesses can make a kept `!tbaa` pair, or a kept `noalias`, false where it was true. So the target keeps none.

That needs no new check. The emitter refuses every annotation in scope today, and this note changes that only under
a mode given for the source. Reading the target without the mode refuses a target that kept one.

### Part of a family

A scope declaration and the metadata that names its scope mean something together. Dropping the declaration and keeping
the metadata could widen a scope: LangRef's loop example makes the same metadata noalias within one iteration, or
across all of them, by where the declaration is. Dropping the metadata and keeping the declaration is harmless, but
there's no reason to allow it. So the mode drops `!alias.scope`, `!noalias` and the declarations together, in the
whole function, and has no way to drop part.

### A rewrite of part of a function

Suppose the search rewrites a few instructions in a function, and the plugin puts them back into a function whose
other instructions keep their tags.

For `!tbaa` and the scoped metadata that looks safe. Each makes a run undefined only through a pair of accesses that
both carry tags, and a rewritten access with none is in no pair. Where LLVM's source is defined its tags all hold, the
model's source is that same run, and the target's run refines it, so the tagged accesses outside the rewrite are the
source's. But it's an argument about LLVM's semantics that the model can't check, since the model never sees a tag.
And it fails as stated in two places: a rewrite that moves, deletes or duplicates a scope declaration changes which
accesses a scope covers, and `noalias` on an argument isn't about tagged accesses at all
([next](#noalias-and-which-pointer-an-access-goes-through)).

So the rule is the whole function. The source is the whole function read with the mode, and the target is the whole
function with every annotation in scope dropped. Where a proof is about a region of it, the lemma that a refined cut
gives a refined function, which goes with F4 by [decision 9](roadmap.md#thirteen-decisions-of-2026-11-09-after-103),
turns it into this whole-function claim. Keeping tags outside the region is a later decision, worth taking only if the
drop-only control [below](#what-it-costs) shows a cost, and only with that argument checked somehow.

A slice win is different, and unaffected. A slice computes values, with no memory access, and putting its result back
is trusted, as decision 9's lower tier says. [`tests/llama/slices.py`](../tests/llama/slices.py) cuts the llama.cpp
slices from clang's `-O3` IR, which carries `!tbaa`, and drops metadata from a slice's lines, which a slice that
stops at loads doesn't need.

### `noalias` and which pointer an access goes through

LangRef's `noalias` on an argument is about every access "during the execution of the function", so it reaches into
everything the function calls. Two consequences:

- **The rewritten function's own `noalias`.** The source reads it as dropped, so the model lets the two pointers
  alias, and a target can access a location through a pointer *based* on another argument than the source did, which
  the model can't tell apart. If the target kept the attribute, that could be undefined. So the target drops it, from
  the definition and from every call to the function in the module, since a call's own `noalias` applies to the call
  as well ("the intersection of their implied semantics applies").
- **A caller's `noalias`.** If `g(ptr noalias %p, ptr %q)` calls the rewritten `f(%p, %q)`, `g`'s promise covers
  `f`'s accesses. A target of `f` that reads through `%p` where the source read through `%q`, at the same address, can
  make `g` undefined: if `g`'s run modifies that location, it's then accessed both through `%p` and not. Nothing in `f`
  can fix that, and it doesn't depend on the mode: any whole-function rewrite of a function with memory meets it.

How often a refinement in the model can do that isn't known. The plain case doesn't refine: `Mem.base` lets two
allocations share addresses ([memory](memory.md#what-it-leaves-out-or-does-differently)), so swapping one argument for
another because they compare equal reads the wrong allocation on some input. But the model's provenance and LangRef's
*based on* are different relations. LangRef's rules for *based* name `getelementptr`, `bitcast` and `inttoptr`, and not
a load, while the model's pointer keeps its allocation through memory. Where they differ, a rewrite can refine in the
model and change what an access is based on. F4 has to say which relation its refinement keeps: compare the arguments
each access is based on, which the model's tags could carry, as they carry [promises](design.md#decisions) now, or
restrict the search to rewrites that keep each access's base.

### Certificates and binding

A certificate has to say its source was read with the mode, or a reader takes it for a claim about the IR as it is.
[Binding](llvm-proof-binding.md) already fails closed: `translation_replay` regenerates both Lean modules byte for
byte, and regenerating the source without the mode refuses it, so a bundle recorded with the mode and not saying so is
`translation_replay_mismatch`. What's needed is the field that says so, [below](#binding-and-verify), and a claim kind
that's only a refinement: equivalence of `Src.f` and `Tgt.f` is true of `drop(src)`, and false of `src`, so it's
refused in this mode.

### Safety, proof tests and claims about the source

[msc](roadmap.md#names-and-languages-decided-on-2026-11-10) needs every undefined behavior LLVM has: "For safety proofs,
more UB than LLVM is conservative and less is unsound" ([trust](trust.md#known-gaps-in-the-model)). A source read with
the mode has less. A proof test's property, or a `verify` claim that a function returns, is about `drop(src)` the same
way. So each refuses the mode, and a module generated with it.

The safety bridge, `Safe src → Refines src tgt → Safe tgt`, could use a safety theorem about `drop(src)` for a target
emitted without the annotations, since that target is what LLVM runs. Nothing needs that yet, and it's not proposed.

### Inside a pipeline

The plugin of [decision 10](roadmap.md#thirteen-decisions-of-2026-11-09-after-103) applies a rewrite where `clang` or
`opt` runs it. Every pass after it, and code generation, sees the rewritten function without its alias facts: LICM, GVN,
DSE and the vectorizers in the middle, and in code generation the alias queries that read the same metadata from memory
operands: `MachineInstr::mayAlias`, and the DAG combiner, whose `-combiner-use-tbaa` is on by default. That's a cost,
not a soundness problem, and the later the plugin runs, the fewer passes pay it. The llama.cpp rewrites were applied to
clang's final `-O3` IR, before `llc`, where only code generation pays. Certify mode reads each rewrite's input with the
mode and its output without, so an output that kept an annotation is refused.

### What the search can no longer prove

A source read with the mode allows more runs: pointers that `!tbaa` or `noalias` said were apart may now alias, and a
value `!range` bounded may be anything. So no rewrite that needs those facts refines it. Reordering a load past a store
that only `!tbaa` keeps apart, or dropping a mask that only `!range` makes redundant, can't be proved. For the value
metadata that's why the recommendation is to model them, which the model has the checks for. For the aliasing
annotations, `clang -O3` has already used them in making the source, so what's lost is only what a further rewrite
would need. How much that is isn't known until the search runs: neither llama.cpp rewrite on `main` needed any.

### Memory has no refinement yet

Every annotation in scope is on a memory access or a pointer, and of memory [refinement](refinement.md#the-relation)
says: "There's no instance for `Mem`, `Ptr` or `PtrVal`." So the mode makes functions translate that still have no
`Refines` claim. F4 also has to give the source no more undefined behavior than LLVM in memory, which it doesn't have
today: a load from a dead stack object, `inbounds` on a freed allocation and uninitialized memory are all stricter than
LLVM ([trust](trust.md#known-gaps-in-the-model)). The mode adds nothing to those, and they hold it up.

## The change, if adopted

None of this is written. It's what it would take.

### The emitter

- **A mode, `--refinement-source`.** It drops every annotation the [table](#each-annotation) says to drop, and refuses
  everything else as today. Nothing else changes: no rule about any other item, no other way to drop one, and the
  default refuses them as now.
- **A record.** The generated module says it was read this way, in its header and in a declaration a tool can find, so
  a module handed to another tool can't pass as an exact one. `--report` lists, for each function, the kinds it
  dropped and how many, which is what coverage in this mode counts and what the board shows.
- **[IR features](ir-features.md).** The items move from *refused* to a new class, refused unless a refinement's source
  drops them. The `ir_features` check probes each in both modes: refused without, translated and named in the report
  with. The value metadata, if modeled, become *modeled*, and `!nontemporal` and `!mem.cache_hint` *assumed*.

### Binding and verify

- **[`tools/binding.py`](../tools/binding.py)** gets `claim.source_reading`, `"exact"` or `"annotations_dropped"`. The
  manifest's keys are exact, so that's `ir-lean.binding.manifest/3`, and a version 2 manifest is `manifest_invalid`, to
  be recorded again, as version 1's was. `"annotations_dropped"` is allowed only with `ir_instance_refinement`, and
  with `ir_instance_equivalence` it's `manifest_invalid`. `translation_replay` runs the emitter with the mode on
  `src_ir` and without it on `tgt_ir`, always.
- **The verdict says so.** A `bound` one's `establishes` says the target refines the input IR with those annotations
  dropped, `trusted` gains LangRef's rule for dropping, and `does_not_establish` gains anything about what the source
  does. The kinds dropped are in the verdict.
- **`verify`, `ptf` and msc refuse the mode** as `invalid_request`, and refuse a generated module that records it,
  since no claim they check is a refinement's source.

### Labels

[Decision 9](roadmap.md#thirteen-decisions-of-2026-11-09-after-103) labels a win by what's proved and what the proof
rests on, and the kernel corpus proposes a third label, the source IR, "as built" or "relaxed with
`-fno-strict-aliasing`". This adds a value to it: **as built, read with its annotations dropped.** The board shows the
kinds dropped in the rewritten function, and the drop-only control's result.

### Tests

What would show the mode can't reach a target, msc or ptf:

- **A target can't carry one.** For each item in scope, `tests/binding.py` records a bundle whose target keeps it, and
  binding refuses it, since the target is read without the mode. A manifest asking for the mode on the target isn't
  representable.
- **Not part of a family.** A source with a scope declaration and its metadata translates with both dropped, and no
  option drops one without the other.
- **A real run binds.** A source with `!tbaa`, a `noalias` argument and inlined scopes, and a target with none of them,
  binds as `ir_instance_refinement` in the mode, and is `unsupported` without it.
- **The cost of the reading is visible.** A rewrite that reorders a load past a store only `!tbaa` keeps apart is
  correct in LLVM and doesn't refine `drop(src)`: a proof fails with an error that isn't a resource limit, and a
  `¬ Refines` theorem shows the input where the two alias.
- **Everything else refuses it.** `verify` and `ptf` with the mode, or given a module that records it, answer
  `invalid_request`; msc does too once it's built; `ir_instance_equivalence` with it is `manifest_invalid`.
- **Must-break mutants.** An emitter that applies the mode to the target, one that drops a scope declaration and keeps
  its metadata, and a `tools/binding.py` that reads `source_reading` as `"exact"`, each make a test fail.

If it's adopted, SEM-06's trust gap in the [task list](llvm-verification-tasks.md#sem-06-memory-for-refinement),
"`tbaa` and scoped `noalias` are refused, and stay refused until modeled", changes to say they're dropped on a
refinement's source.

## What it would buy

From the kernel corpus proposal's tables of what the emitter does with each named kernel, as built and relaxed with
`-fno-strict-aliasing`. Its 85 named kernels are in its ten projects that aren't rejected. 3 translate as built, all
libsodium's, and 19 relaxed.

| Kernels | As built, first reason | Relaxed, first reason | With the mode, as built |
| ---: | --- | --- | --- |
| 13 | `!tbaa`, or a cycle with a function refused for it | None: they translate | Past every reason seen. Whether they translate is the estimate |
| 2 | `!tbaa` | `!range`, or `noalias` on an argument | Past both. What's behind them wasn't recorded, and no intrinsic they call is refused |
| 6 | A scope declaration, or a cycle with a function refused for `!tbaa` | A scope declaration, or a cycle with one refused for `noalias` | Still stopped: each calls an intrinsic the model refuses, `llvm.prefetch` or an x86 pack or multiply |
| 2 | FLAC's string attribute | `noalias`, `!alias.scope` | Still stopped by the string attribute, which LangRef doesn't define |
| 20 | `!tbaa` | Something else: an intrinsic, inline assembly, a call, or a promise at a call | Still stopped by that |
| 3 | None: they translate | None | Unchanged |
| 39 | Something else | Something else | Unchanged |

The 13 are libwebp's `BuildHuffmanTable` and `VectorMismatch_AVX2`, xxHash's `XXH64` and `XXH32`, zlib-ng's
`longest_match_avx512`, `compress_block`, `build_tree`, `insert_string`, `quick_insert_string` and
`zng_inflate_table`, and zstd's `ZSTD_encodeSequences_bmi2`, `ZSTD_btGetAllMatches_noDict_3` and `ZSTD_insertBt1`. The
2 are libdeflate's `deflate_decompress_bmi2` and libwebp's `SSE4x4_SSE2`.

**The estimate:** with the mode, as built, about 16 of the 85 translate, the 3 and the 13, and at most 18 with the 2.
That's 16 of the relaxed run's 19, all but FLAC's three, whose string attribute is outside this argument. It is an
estimate for three reasons: the proposal recorded only each function's first reason; IR built with strict aliasing is
a different program, which LLVM may have vectorized or reordered further, so it can meet a refusal the relaxed IR
didn't; and translating isn't elaborating, which the proposal didn't check. Running the proposal's
`bench/kernels/demand.py` with the mode would replace it with a count.

Over whole units the same holds. As built, 24 of the 798 functions in the units named translate, and `!tbaa` is the
first reason for 294 more and in a cycle with 27. Relaxed, 241 translate, 105 of them FLAC's, so by the same proxy about
136 would as built. Relaxed, 117 more stop first at a scope declaration, `noalias` or `!range`, which the mode drops. 15
of them are FLAC's, and what's behind the other 102 is unknown.

**None of it is a win before F4.** All 16 kernels take pointers and read memory through them, so each would translate
and have no `Refines` claim until F4. A slice win doesn't need the mode.

## What it costs

The rewritten function loses its alias facts from the point the rewrite is applied, and its `noalias` arguments. No
number for that exists. To measure it, build each win three ways:

1. **The baseline:** the project as built, by the kernel corpus's decision 3.
2. **The drop-only control:** the same build, with the plugin dropping every annotation in scope from the rewritten
   function at the point it would rewrite it, and rewriting nothing.
3. **The win:** the plugin dropping them and rewriting.

The win is 3 against 1, by the corpus's rule for measurably faster, as for any win, so the drop's cost is already inside
it. The control says how much of it the drop ate. Compare its object code with the baseline's first: where they're the
same, the drop cost nothing in that function, and only where they differ does it need timing, by the same rule. A
control that's measurably slower is the evidence that would make keeping tags outside the rewritten region worth its
argument ([decision 2](#decisions-for-the-maintainer)).

Against the relaxed route: `-fno-strict-aliasing` loses `!tbaa` in the whole program from the front end on, and the mode
loses every annotation in scope in one function from the rewrite on. Neither has been measured.

## What this doesn't settle

- **F4,** and its relation for pointers, which [`noalias`](#noalias-and-which-pointer-an-access-goes-through) needs.
- **Modeling `!tbaa` and scoped aliasing,** which the roadmap's open questions keep. The mode doesn't replace it: a
  model would let the target keep them, and the search use them.
- **Call-site promises and FLAC's string attribute,** each out of scope [above](#each-annotation).
- **A count:** the [estimate](#what-it-would-buy) until `demand.py` runs with the mode, and the cost until the first
  control is timed.
