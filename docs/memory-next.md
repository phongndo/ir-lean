# Calls that touch memory, `noalias`, and `!tbaa` on a refinement's source

The design for the three things that stop most of the [kernel corpus](kernels.md) after 2026-11-12, in the order
they'd be built, as [process](process.md#0-the-design-before-any-code) asks: reviewed before any code. For what any
theorem means, read [trust](trust.md) first, and for the relation, [refinement](refinement.md). Nothing here is built.

**Status: round 1 of review found six blockers, and this draft isn't approved.** [Review round 1](#review-round-1)
lists each finding, its class, and what it changes. Sections 1 to 3 below are the draft the review read; where a finding
overrides one, the finding's change stands, and round 2 rewrites the section. Only the
[prerequisite](#the-prerequisite-loads-that-thread-memory) is ready to build.

Measured on 2026-11-12 at `65d118d` ([kernels](kernels.md#what-lifting-one-kind-would-translate)): as built, `!tbaa`
alone would translate 256 more of the 798 functions; relaxed, with `-fno-strict-aliasing`, `noalias` on a parameter
alone would translate 90, and is all that stops 13 named kernels, every one of llama.cpp's five among them; calls
outside the module that touch memory come next. Those are counts of the refusal kinds measured, which include
`memory(...)`, `nofree` and the rest of the `noalias` family; what each slice here removes is narrower, and its own
count is round 2's to measure.

## One mechanism under all three: a call's footprint

Each needs the same thing the model doesn't have: for a running call, which bytes were read and which written, and
through which pointers. `Mem.Call` already has part of it. `written : Nat → Nat → Bool` records the bytes written
during a call that made promises about memory, and `Tag`s carry a promise on every pointer based on an argument,
LangRef's derived provenance, through copies, offsets, `select` and memory.

**The footprint** extends `Call` with, for each byte, three bits: read during the call, written during the call, and,
for each `noalias` argument, whether every access to it was through a pointer based on that argument. It's kept only
for calls that need it, as `tracked` keeps `written` today, so code without these promises pays nothing.

- **Invariants, as tests:** an access sets exactly its bytes' bits; a byte's bits only grow during a call; they're
  dropped when the call returns. `IRLean/ExecMem.lean` gets the same record, and `tests/exec_memory.sh` a mutant that
  forgets an access.
- **Reuses:** `Tag` and its propagation, `Mem.call`'s frame, `ExecMem`'s agreement proofs, and `Mem.le`'s cases for
  `calls`, which today asks both sides for the same running calls.

## 1. Calls outside the module that touch memory (F4)

**The claim.** A call to a function the module only declares, passing or returning pointers, or able to access memory
the function can reach, is modeled as LangRef allows it: the callee may read and write exactly the memory it can
reach, as its `memory(...)` attribute and the arguments' attributes narrow it, and its answer says what it wrote.
Theorems about such code hold for every world, as they do for calls without memory today.

**What the callee can reach** is the hard part, and it has to be exact on both sides: more than LLVM allows is wrong
for a refinement's source, and less is wrong for a safety proof and a refinement's target, as
[refinement](refinement.md#memorys-gaps-each-with-its-side) sets out for other gaps. It's every allocation that has
**escaped**:

- every global with external linkage, and every allocation the world returned or a global points to at the call;
- every allocation a pointer to which is passed to an outside call without `captures(none)`, or was stored into memory
  that had escaped, or returned from a function outside the run;
- and, transitively, every allocation a pointer stored in escaped memory points to, at the call.

`Alloc` gets an `escaped` bit, set by those, and never cleared, as LangRef's capture is never undone. A stack object
that never escaped is out of reach: what Alive2 does with its non-escaped local blocks, and what lets a callee not
clobber a local variable. A pointer argument with `captures(none)` gives the callee its allocation for the call only.

**What the call does,** for a callee whose `memory(...)` allows reading or writing argument or other memory:

- **Its event** is the callee, the arguments' lanes, pointers as their addresses, and the bytes it may read: the
  escaped allocations' bytes, and the arguments' allocations, as lanes. So two runs that give a callee different
  memory to read make different events, and a target that makes memory more defined before a call isn't certified.
  That's stricter than Alive2, which compares a call's inputs by refinement: a conservative restriction of this design.
- **Its answer** adds, for a callee that may write, new contents for each byte it may write: escaped, writable, and
  allowed by `memory(...)` and `readonly`, `writeonly` and `readnone` on the arguments. A byte it may not write keeps
  its value. A call is a call with effects, in the trace, if it may write; one that only reads answers from
  `World.read` as today, keyed by the memory it read.
- **A returned pointer** points into an escaped allocation, or to a new one the world made, which is then escaped.
  The new one is the same allocation on both sides, numbered by the world's answer, so `Mem.le` doesn't yet need
  renaming (F4's stage 3), as long as source and target make the same calls, which their equal traces already ask.
- **Callbacks into the module,** through a function pointer that escaped, are part of the answer, as they are today:
  whatever they wrote is in the new contents. A function whose address escaped keeps its promises refused as now:
  `norecurse`, `nosync`, `nofree` and a narrower `memory(...)` on a function whose calls outside the module touch its
  memory.
- **`Mem.withFrame` and `Mem.call` pass an `Exit` through,** so a function with a stack frame or promises about memory
  can make a call that may not come back. Today that's refused as `IRLean.World doesn't wrap yet`, which is 203
  functions in the corpus, none of them alone.

**Holds against:** a callee reading or writing memory it can't reach in LLVM, or not one it can; a pointer returned
into memory that hadn't escaped; a refinement whose target hands the callee different memory, which its event shows;
and every tool, crash and limit [the gates](rules.md#what-the-gates-promise) hold against. **Doesn't:** inline
assembly, `inttoptr`, which stays refused, and anything below LLVM IR.

**Invariants, as tests.** In `tests/calls`, each with a theorem and Alive2's verdict: a store before the call that the
callee may read can't be dropped; one to a local that never escaped can; a load after the call of memory the callee may
write can't be moved before it; of memory it can't reach, can. In `tests/real`, against native code: a callee that
writes through its argument, one that stores the argument where a later call reads it back, and one that returns a
pointer to a global. In `tests/real/ub.ll`: a callee writing through a `readonly` argument, and a function reading after
its call memory the callee freed.

**Slices.** (a) `Exit` through `withFrame` and `call`, with outside calls that touch no memory. (b) Escape, as above,
with its tests, changing no translation. (c) Calls that read reachable memory. (d) Calls that write it, and return
pointers. Each is a pull request, at most about 1,500 lines, with `docs/calls.md` and this page updated.

## 2. `noalias` on a parameter

**The claim.** LangRef: memory accessed through a pointer based on a `noalias` argument "is not also accessed, during
the execution of the function, via pointer values not *based* on the argument", for "memory locations that are
*modified*, by any means, during the execution of the function. If there are other accesses not based on the argument
or return value, the behavior is undefined." The model makes exactly that undefined.

**How.** Entering a function with a `noalias` argument gives that argument a fresh `Tag` with a `noalias` bit, and its
call a footprint. Each access during the call sets the byte's bits: accessed through a pointer carrying that tag,
accessed through one that doesn't, written. When a byte has all three, the run is undefined, at that access, as
`UB.noaliasAccess`. The bits only grow, so it doesn't matter which comes last. A call inside the function runs inside
its footprint, so its accesses count, and a call outside the module counts as accessing every byte it may read or
write, through the pointers it was given.

- **Based on** is LangRef's, through the tags, which already follow copies, offsets, `select`, `phi` and memory.
  `ptrtoint` and back is `inttoptr`, which stays refused, so a pointer can't lose its basis.
- **On a return value,** `noalias` is already modeled, as `Mem.le.noaliasResult`. At a call, `noalias` on an argument
  stays refused: it's a promise the caller makes about a callee the model might not run.
- **`!noalias`, `!alias.scope` and `llvm.experimental.noalias.scope.decl`** are scoped `noalias`, which LangRef
  defines less precisely, across inlined copies. They stay refused, and their route is section 3's, on a refinement's
  source only.

**Refinement.** `noalias` adds undefined behavior. A target that keeps every access the source makes, through the same
pointers, keeps the source's footprint, so `Mem.le` asks the target's footprint to be within the source's, byte by
byte, which every operation keeps when both sides make the same access. A rewrite that adds a `noalias` isn't
certified, and one that drops it is.

**Holds against:** an access not based on the argument to a byte modified during the call, by either side, in either
order, including through a callee; one through the argument to a byte modified around it. **Doesn't:** scoped
`noalias`, which is refused.

**Invariants, as tests.** In `tests/real/ub.ll`: a byte written through the argument and read through another pointer,
and the same in the other order, and through a callee, each undefined. In `tests/real/promises.ll`, against native
code: reads through both of a byte nothing writes; a write through the argument alone; and llama.cpp's form, a
`noalias` destination written while `noalias` sources are read. In `tests/refine`: dropping `noalias` refines, and
adding it doesn't.

**Slices.** (a) The footprint, and `noalias` in functions without calls outside the module. (b) With F4's calls. Each a
pull request, with `docs/memory.md`'s table and [trust](trust.md)'s gap rows updated.

## 3. `!tbaa`, and scoped `noalias`, on a refinement's source

**The claim** is [source annotations](source-annotations.md)'s, which this adopts as its recommendations stand: on the
source of a `Refines` claim, and only there, read `!tbaa`, `!tbaa.struct`, `!alias.scope`, `!noalias`,
`llvm.experimental.noalias.scope.decl` and `llvm.access.group` as dropped. LangRef lets a transformation drop them, so
the source without them refines the source with them, and a target that refines the first refines the second.

**What it needs from the above.** Its decision 5: the target touches only bytes the source touches, the same way, and
changes only bytes the source changes. That's the footprint's comparison, from section 2, applied to the whole function
being rewritten: a `Refines` claim with this mode asks the target's footprint to be within the source's. So it waits for
section 2's slice (a), and for F4 for functions that call outside the module.

**Holds against:** a target that reads or writes a byte the source doesn't, which a caller's `!noalias` or a program's
`!invariant.load` could have depended on; reading the source this way anywhere but a refinement's source, which every
other tool refuses by name; a target that keeps an annotation the source dropped. **Doesn't:** what a later pass does
with the rewritten function's lost alias facts, which [source annotations](source-annotations.md#what-it-costs) says
how to measure.

**Invariants, as tests.** `tools/verify.py` and `tools/binding.py` refuse the mode for anything but a refinement's
source, each case by name. Certificates and verdicts record the mode. A target that reads a byte the source doesn't is
refuted.

**Slices.** One pull request after section 2's slice (a): the emitter's mode, the claim's footprint condition, the
labels, and the tests.

## Order, and what it buys

| Step | Unblocks in the corpus, as measured | Waits on |
| --- | --- | --- |
| F4 (a), `Exit` through frames | Nothing alone; 83 more after `noalias` and calls touching memory | Nothing |
| `noalias` (a) | 90 functions relaxed, and 13 named kernels | The footprint |
| F4 (b) to (d) | 18 alone relaxed, and the most after `noalias` | F4 (a) |
| `!tbaa` on a source | 256 as built, for refinement claims only | `noalias` (a), and F4 for functions that call out |

Each is an estimate of what translates, not of what's proved: [kernels](kernels.md#what-lifting-one-kind-would-translate)
says why.

## Review round 1

On 2026-11-12, by an independent model at its highest effort, against LangRef and Alive2 at the pin. Each finding,
with the change it makes. B is a blocker, S a should.

| # | Finding | Class | Change |
| --- | --- | --- | --- |
| B1 | Reach starts only from escaped memory: a pointer stored in an allocation lent with `captures(none)` is reachable during that call; an exported helper the callee calls back can write an internal global; a private global nothing reachable points to isn't reachable | Model with fewer behaviors than LLVM, and more | Reach is the closure, at the call, of the call's borrowed arguments, the world's lasting capabilities, and the module's functions it can call back, with an invariant on `initial` |
| B2 | One `escaped` bit can't hold `captures(address)`, `read_provenance`, or an allocation reached through both a `readonly` argument and an unrestricted one | The same | Capabilities live on pointers, as `Tag`s do, through capture, stores and returned pointers, and permissions are per access path. Until then, capture forms other than none and full stay refused |
| B3 | `noalias` can't count a callee's possible accesses as actual ones: a read-only callee that reads neither pointer is defined | Model with more UB than LLVM | The world's answer says which bytes the callee actually read and wrote, through which pointers, within what it may; `noalias` uses those. So `noalias` with calls outside the module waits for F4's answers |
| B4 | A write that's undone later changes no bit, yet breaks an `!invariant.load` elsewhere: decision 5 needs changes, temporary ones included | Model with fewer distinctions than the claim needs | The footprint adds a bit per byte set when a write, or a callee, changes its value at any point. Section 3 compares that bit, target within source |
| B5 | An answer that only replaces bytes can't free an allocation, or make one and store its pointer through an argument | Model with fewer behaviors than LLVM | Answers create and free allocations, apart from the return type, with freshness, lifetime and promise checks |
| B6 | Passing `Exit` through frames loses memory a handler outside sees after unwinding: two functions differing only in what they leave in a global on unwind would refine | Model with fewer distinctions | `Exit.unwound` carries memory, compared by `Mem.le`; frames are cleaned up, and `initializes` cleared, on normal return only |
| S7 | `Call.le.written` asks source-written within target-written, for `writeonly`'s poison; the footprint asks the opposite | Two orders in one field | Keep `written` and its order as they are, and add the footprint as fields of its own, each with its order, and prove loads, `initializes` and call teardown keep both |
| S8 | Dropping `noalias` changes the tags returned pointers carry and `nextCall`, which pointer refinement and `Mem.le` ask to agree | Relation too strict for the claim | Design how a finished call's tags relate, or erase them, before promising that test |
| S9 | Equal traces don't make a world's allocation fresh, or the same on both sides: reads aren't in the trace | Unchecked invariant | A namespace for the world's allocations apart from the module's, or checked freshness with `next` kept in step, and allocating answers made events |
| S10 | Loads return no memory, so they can't record a read | Interface | [The prerequisite](#the-prerequisite-loads-that-thread-memory), its own pull request first |
| S11 | Alive2 at the pin accepts the B1 rewrite, has TODOs for escaped locals, and rejects parameter `noalias`: it can't be this design's oracle | Bug class 1: a limit counted as a pass | Fixtures written from LangRef, each with a mutant that has to fail, and Alive2's runs counted apart as unsupported where it can't decide |
| S12 | The 87% estimate counted refusal kinds this design keeps | Overclaim | Removed above; each slice measures what it removes |
| N13 | Alive2 compares a call's inputs by refinement, not equality | Wrong fact | Fixed above |

## The prerequisite: loads that thread memory

Every load, `loadInt`, `loadPtr`, `loadVec`, and `strlen`, returns the memory it leaves, as stores do, unchanged for
now. It changes no meaning: each new form is proved equal to the old one's value with the memory untouched, the emitter
binds the memory after each load, and `ExecMem`, the agreement proofs, the `Mono` and `Mem.le` lemmas, and the
existing proofs follow. Its invariant is that every translated function's Lean is the same up to those bindings, and
every test passes unchanged. It's what lets the footprint record a read, and it's the first pull request of all
three sections.
