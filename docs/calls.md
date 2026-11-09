# Calls outside the module

What a run does when it calls a function the module only declares, what `IRLean.Refines` asks of two runs that make
such calls, and what each attribute on the call lets a rewrite do. Also external globals, variadic calls, constant
expressions over globals and linkage. This is the design, written on 2026-11-09, and [slices](#slices) says which
parts are built. For what any theorem means, read [trust](trust.md) first, and for the relation,
[refinement](refinement.md).

**Why now.** On InstCombine's own tests at `llvmorg-23.1.3`, calls outside the module are the second-largest reason
the emitter refuses a pair, after floating point: of the 31,240 functions InstCombine changes, 2,787 are refused first
for `call to external @F`, 394 for an external global and 67 for a variadic call, in the stage-1 run on the commit
before F3 (`build/stage1/pairs.jsonl` on `feat/stage1-benchmark`, read through its own `REFUSAL_GROUPS`). They're also
the first thing [BIND-01](binding-approach.md#the-prototype) found the emitter refusing in LLVM's own compiled C++, and
the largest refusal in its census.

## The decision

- **The outside world is an input, quantified with the arguments.** A function that calls outside the module takes a
  `World`, which says how every such call answers, and the trace of calls with effects made before it. `Refines`
  quantifies over both the way it does over arguments, so source and target face the same world.
- **A call with effects is an event.** It's added to the trace, its answer depends on the trace, and the trace is part
  of how a run ends: a run that returns returns its trace, and a run that ends inside a call that never comes back ends
  with the trace up to that call. Two runs refine only with equal traces. A run that never finishes is compared by
  every prefix of its trace: after the source chooses its run, for every `n`, the two runs watched for their first `n`
  calls with effects have to agree.
- **A call without effects isn't.** A call that accesses no memory (`memory(none)`) answers from the callee and
  arguments alone, and one that only reads, from those and the trace. Neither goes in the trace. Which of the callee's
  possible answers a run gets is the run's choice, through F3's `IRLean.Choice`.
- **Attributes are promises the callee makes, and a broken one is undefined behavior,** as SEM-07 made `willreturn` and
  `mustprogress` for the module's own functions. So `memory(none) willreturn nounwind` makes a call removable, and the
  model certifies removing one.
- **Calls that touch memory the function can see wait for F4,** refused with a reason that says so.

The rest of this page is why, and what each choice lets through or refuses.

## What LLVM says

### LangRef, at the pin

From `llvm/docs/LangRef.md` at `llvmorg-23.1.3`:

- **`memory(...)`** (line 2261): "`memory(none)`: Does not access any memory." `read` means "The location is only
  read. Writing to the location is immediate undefined behavior." `none` means "No reads or writes to the location are
  observed outside the function." `inaccessiblemem` is "memory which is not accessible by the current module". "If the
  `memory` attribute is not specified, then `memory(readwrite)` is implied (all memory effects are possible)." A call's
  effects are `CallSiteEffects & (FunctionEffects | OperandBundleEffects)`.
- **`willreturn`** (line 2485): "If an invocation of an annotated function does not return control back to a point in
  the call stack, the behavior is undefined." It doesn't imply `nounwind`.
- **`nounwind`** (line 2509): "If the function does raise an exception, its runtime behavior is undefined."
- **`noreturn`** (line 2465): "This produces undefined behavior at runtime if the function ever does dynamically
  return."
- **`speculatable`** (line 2711): "the function does not have any effects besides calculating its result and does not
  have undefined behavior."
- **`mustprogress`** (line 2887): a function "is required to return, unwind, or interact with the environment in an
  observable way e.g., via a volatile memory access, I/O, or other synchronization."

LangRef doesn't say a `memory(none)` function answers the same for the same arguments. Until LLVM 16, `readnone` did:
the function "computes its result (or decides to unwind an exception) based strictly on its arguments" (LangRef at
`llvmorg-15.0.7`, line 1924). `memory(none)` replaced it and dropped that sentence. And a `memory(none)` function can
return `freeze poison`, a new value on each call.

### What LLVM's passes do with them

At the pin:

- **Removing a call.** `wouldInstructionBeTriviallyDead` (`llvm/lib/Transforms/Utils/Local.cpp`, line 422) removes an
  unused call only if `!I->mayHaveSideEffects()`, which is `mayWriteToMemory() || mayThrow() || !willReturn()`
  (`llvm/lib/IR/Instruction.cpp`, line 1346). So a call that writes nothing, can't unwind and will return is removable:
  `memory(none)` or `memory(read)`, with `nounwind` and `willreturn`.
- **Merging two calls.** EarlyCSE treats two calls as the same value when `CI->doesNotAccessMemory()`
  (`llvm/lib/Transforms/Scalar/EarlyCSE.cpp`, line 131). That's removing the second call and using the first's result.
- **Adding a call.** `isSafeToSpeculativelyExecute` allows a call only to a `speculatable` function: "The called
  function could have undefined behavior or side-effects, even if marked readnone nounwind"
  (`llvm/lib/Analysis/ValueTracking.cpp`, line 7415).

Nothing found duplicates a call so that one run makes it twice where it made it once. Unrolling and jump threading copy a
call onto paths a run takes one of.

## Prior art

**Alive2,** at `a68009c9e815`, the oracle `ir-lean` pins, in `ir/state.cpp`. `State::addFnCall` (line 1091) gives each
call in the source fresh outputs: a result, a flag saying the call is undefined, and a flag saying it doesn't return,
fixed by `willreturn` or `noreturn` (lines 1266 to 1271). Calls in the source whose inputs refine each other get equal
outputs (lines 1274 to 1283). The inputs are the arguments, plus, for a callee that can read memory, the memory and a
count of the calls that wrote before it (lines 949 to 970). In the target, "this fn call must match one from the
source, otherwise it's UB" (line 1291): a call takes the outputs of a source call whose inputs its own refine, and with
none, the target is undefined. A call's effect on memory is part of its outputs, so the memory the two sides end with
tells a dropped call that wrote apart. Alive2 has no unwinding: its outputs have no exception.

**Vellvm,** at `1d651e7a391c`, makes every call outside the module an event of its interaction tree,
`ExternalCall (t : dtyp) (f : dvalue) (args : list dvalue)` in `src/rocq/Semantics/LLVMEvents.v`, which "should never be
interpreted away": two programs are compared by the calls they make, in order.

## Two forms, and what each lets through

The usual answer, which both take: the target makes only the calls the source makes, in the same order, with arguments
that refine the source's, and each call's result is the same unknown on both sides. Two ways to say it:

- **Traces.** A run's outcome includes the list of calls it made. Results come from an environment that answers each
  call given the calls before it. Vellvm's form.
- **Shared answers.** No trace. Each call's result is an unknown both sides share, keyed by the callee and arguments,
  and it can be undefined or never return. Alive2's form, for a callee that touches no memory.

Each against the five wrong rewrites, for a call to `declare void @use(i8)`, which has no attributes, so it may write
any memory, unwind or never return. That's how 2,772 of the 2,787 refused InstCombine pairs above declare their callee:
with no memory attribute at all.

| Wrong rewrite | Traces | Shared answers, by callee and arguments |
| --- | --- | --- |
| Adding a call | Refused: the traces differ | Refused: the added call's answer can be undefined |
| Dropping one | Refused: the traces differ | Refused if the callee can't promise to return, since its answer can be never returning. **Let through** for a `willreturn nounwind` callee with effects: its answer is a value or undefined, so a source that made the call allows a target that didn't |
| Reordering two | Refused: the traces differ | Refused for `@use` itself: if `use(1)` never comes back and `use(2)` is undefined, the swapped target is undefined where the source isn't. **Let through** for `willreturn nounwind` callees with effects: each call gets the answer for its arguments, in either order |
| Changing an argument | Refused: the traces differ | Refused: the new arguments' answer can be undefined |
| Calling twice where the source calls once | Refused: the traces differ | **Let through:** the second call gets the first's answer |

Alive2 doesn't let these through, because a callee that may write memory isn't keyed by its arguments alone: its inputs
include the memory and the count of writes before it, and the memory the run ends with is compared. In a model with no
memory, that state is the trace. So the shared-answer form is right only for calls without effects.

Traces have the opposite problem: every call is an event, so they refuse the right rewrites LLVM makes to calls without
effects, [above](#what-llvms-passes-do-with-them): removing an unused `memory(none) willreturn nounwind` call, and merging
two.

So this design takes both: **traces for calls with effects, shared answers for calls without.** It refuses all five
wrong rewrites for a call with effects, and for a call without, refuses exactly the ones LLVM doesn't make.

## The model

In a new module, `IRLean/World.lean`.

```lean
/-- A value crossing into or out of a call outside the module: each lane as a number, or poison. -/
abbrev Lanes := List (Option Nat)

/-- A call outside the module: the callee's name, and each argument's type, with the attributes that change how it's
passed, and lanes. -/
structure Event where
  callee : String
  args : List (String × Lanes)

/-- The calls with effects a run has made, newest first. -/
abbrev Trace := List Event

/-- How a call outside the module answers. -/
inductive Answer where
  | ret (v : Lanes)  -- returns this; lanes the type doesn't have are poison
  | undefined        -- the callee's run is undefined
  | stays            -- never comes back: runs forever, ends the program, or jumps out of the caller
  | unwinds

/-- How the outside world answers every call. -/
structure World where
  effect : Trace → Answer                -- a call with effects, given the trace ending with it
  read : Trace → Event → Nat → Answer    -- a call that only reads, given the trace before it, and the run's choice
  pure : Event → Nat → Answer            -- a call that accesses no memory, given only the call, and the run's choice

/-- How a run that calls outside the module ends, with the trace it made. -/
inductive Exit (α : Type) where
  | done (v : α) (t : Trace)   -- returned `v`
  | halted (t : Trace)         -- the call at the head of `t` never came back
  | unwound (t : Trace)        -- the call at the head of `t` unwound, and so did this function
  | cut (t : Trace)            -- the run was about to make the call at the head of `t`, past those it was watched for

/-- What a function that calls outside the module does: for each way its run chooses, and each number of calls with
effects to watch it for, how it ends. -/
def Talks (α : Type) : Type := Choice → Nat → Outcome (Exit α)
```

A function that calls outside the module, or calls a function that does, takes `(w : World) (h : Trace)` after its
arguments and memory, and returns `Talks α`. Every other function is emitted as before, so no existing proof changes.

### What a call does

The call's kind comes from its effects, LangRef's `CallSiteEffects & FunctionEffects`, with argument memory dropped
when no argument is a pointer:

| Kind | Effects | Its answer | In the trace |
| --- | --- | --- | --- |
| Pure | none | `w.pure e i`, where `e` is the call and `i` the run's choice at this place | Only if it unwinds |
| Reading | reads only | `w.read h e i`: also the trace before it, since earlier calls with effects may have written what it reads | Only if it unwinds |
| With effects | may write | `w.effect (e :: h)` | Always, before it answers |

The choice `i` is the block's next chooser, `c'.pick k`, numbered with the `freeze`s as
[refinement](refinement.md#the-model) says, so a function with a call without effects makes choices. The world gives
each call without effects a set of possible answers, indexed by a number, and each run picks one per call: for every
way the target picks, the source must have a way that allows it. So merging two calls is a refinement, since the source
can pick the same answer twice, and duplicating one isn't, since the target may pick two different ones. That's
LangRef's `memory(none)`, which doesn't promise the same answer for the same arguments, and not Alive2's, which does.

How an answer becomes the call's outcome, given what the declaration and the call promise:

| Answer | A call with effects | A call without effects |
| --- | --- | --- |
| `ret v` | Returns `v`'s lanes as the call's type. Undefined under `noreturn` | The same |
| `undefined` | Undefined | Undefined |
| `stays` | Ends the run, `halted` with the trace ending in this call. Undefined under `willreturn` | Never finishes, `none`. Undefined under `willreturn` |
| `unwinds` | Undefined under `nounwind`. Otherwise ends the run, `unwound`, with the trace ending in this call | The same, with the call added to the trace for the observation |

Before a call with effects answers, the run checks how many calls it's watched for: one that would make the trace
longer than that ends the run `cut`, with the trace so far and that call at its head, before it answers. A run that ends `halted`, `unwound` or `cut` passes it up
through the module's own callers, the way `Mem` threads memory. Unwinding through a function or a call marked
`nounwind` is undefined.

### Refinement

```lean
instance [Refine α] : Refine (Exit α) where
  le a b := match a with
    | .done x t => ∃ y, b = .done y t ∧ Refine.le x y
    | .halted t => b = .halted t
    | .unwound t => b = .unwound t
    | .cut t => b = .cut t

instance [Refine α] : Refine (Talks α) where
  le a b := ∀ ct, ∃ cs, ∀ n, Refine.le (a cs n) (b ct n)
```

With the existing instances around it, `Refines src tgt` says: for every argument, every world and every trace before
the call, every way the target chooses has a way the source chooses whose run allows the target's, watched for any
number of calls with effects. Undefined behavior in the source still allows anything, for that world and that many
calls: if the source, given these answers, reaches undefined behavior before the cut, LLVM may assume it does, and the
answers already say every call before it came back.

**Why a run is watched for every number of calls.** A run that never finishes gives `none`, which says nothing of the
calls it made. A target that calls `@use` before a loop that never ends, and a source that doesn't, both give `none`.
Watched for no calls, the target ends `cut` at its call, and the source still runs forever, so they differ. In
general, watching for `n` calls shows the first `n + 1` calls of the run, the last only by what it was, so every
prefix of a run's trace, finite or not, is something the relation compares.

**Why the cut shows the call it stops at.** Without it, the call after the `n` watched for would be seen only by
what it answers, and a run that then spins silently shows nothing. A source that picks between `use(1); spin` and
`use(2); return`, for a target that does `use(2); spin`, would agree at every `n` with one source run per world: cut
off with no calls at `n = 0`, and past it, `use(1); spin` where `use(2)` returns, giving `none` like the target. No
source run does what the target does when both calls return. Cut off with the call at its head, at `n = 0` the source
shows `use(1)` and the target `use(2)`.

**Why the watching comes after the source's choice.** The source has to pick one run that agrees with the target's at
every `n`. A source that could pick per `n` could match each prefix with a different run: one that spins silently where
the target's `use(); spin` is watched past its call, and one that makes the call and returns where it's watched up to
it. No single run of that source does what the target does, so that would certify a wrong rewrite. The world is an
input, before the target's choice, and the cut is quantified last. The source's choice may depend on the world, as
refinement between sets of runs allows: what matters is that some run of the source, with these answers, does what
the target's does.

**The price.** A source that reaches undefined behavior after a call with effects is defined when watched for fewer
calls, so the call can't be dropped before the undefined behavior even under `willreturn nounwind`, which LLVM's
`simplifyUnreachable` does. Keeping the call and replacing what follows still refines.

### The five wrong rewrites, in this model

For `declare void @use(i8)`, with effects:

| Wrong rewrite | Why it's refused |
| --- | --- |
| Adding a call | The target's trace has a call the source's doesn't |
| Dropping one | The source's trace has a call the target's doesn't, in a world where the call returns. Watched for no calls, the source is cut and the target isn't |
| Reordering two | The traces differ in order |
| Changing an argument | The traces differ in the argument |
| Calling twice | The target's trace has one more call |

For `declare i8 @f(i8) memory(none)`, without effects:

| Rewrite | LLVM | This model |
| --- | --- | --- |
| Adding an unused call | Wrong unless `speculatable` | Refused: the world can answer `undefined`, or `unwinds` without `nounwind` |
| Dropping an unused call | Right with `willreturn nounwind` | Right with both: every answer is a return or undefined. Without `willreturn`, `stays` makes the source never finish. Without `nounwind`, the source unwinds |
| Reordering two | Right with `willreturn nounwind` on both | Right with both: every answer is a return or undefined, and the source picks the target's. Without `willreturn`, refused: one that never returns hides the other's undefined behavior. Without `nounwind`, refused: whichever unwinds first decides the trace the run ends with |
| Changing an argument | Wrong | Refused: the new call's answers can differ |
| Merging two into one | Right | Right: the source picks the same answer twice |
| Calling twice where the source calls once | Wrong, by LangRef | Refused: the target's two picks can differ |

### Who keeps a promise

The callee does, and nothing checks it: its body isn't in the module. The model makes a broken promise undefined, as
LangRef does, by the answers it allows: a `noreturn` callee that returns, a `nounwind` one that unwinds, and a
`willreturn` one that never comes back are all `UB.outsideCall`. That's SEM-07's rule for the module's own promises, applied
to promises about code the module can't see. So a theorem covers every callee that keeps the promises its declaration
and the call make, and a run where one doesn't is undefined in the model and in LLVM alike. A target that adds a
promise, such as `willreturn` on a call, is undefined in a world where the callee breaks it, and the source isn't, so it
doesn't refine.

| Attribute | On a call outside the module, it licenses |
| --- | --- |
| `memory(none)` | No event: the call can be dropped, merged or reordered against calls with effects, as the table above says |
| `memory(read)` and other read-only effects | The same, except it can't move across a call with effects, since its answer depends on the trace |
| `willreturn` | `stays` is undefined. For a call without effects, with `nounwind`, that makes it removable. A call with effects stays in the trace |
| `nounwind` | Dropping or reordering it: `unwinds` is undefined |
| `noreturn` | Nothing removable: a return is undefined, so the code after the call is unreachable |
| `mustprogress` | What it does on a module's own function: under a caller's promise, a call without effects to a `mustprogress` callee that isn't `willreturn`, and never comes back, stops the model as `progressUnsettled`, through `IRLean.promised` |

Refused on a call outside the module, until something needs them: `nosync`, `nofree`, `norecurse`, `nocallback`,
`convergent`, `returns_twice` and `builtin`, which the model doesn't check, so a target that added one would be certified
on a callee that breaks it; `speculatable`, which would rule out every answer but `ret`, and is what adding a call
needs; operand bundles; and a calling convention that differs from the declaration's, which LangRef makes undefined.

The same goes for promises the *caller* makes about what its calls do, which a callee outside the module could break:
`norecurse` on a function that calls outside the module, since the callee may call back into it, and `nosync`, `nofree`
and a `memory(...)` narrower than the callee's on a function that makes a call with effects or that reads. Each is
refused there. Unwinding through a call marked `nounwind`, to a function in the module that calls outside it, is
undefined, like unwinding through a function marked so.

### What stays out, and what a theorem assumes

- **Arguments are compared exactly.** An event is the callee and its arguments' lanes, so a target that passes a value
  where the source passed poison has a different trace, and doesn't refine in the model. LLVM allows it, and Alive2 does
  too. Allowing it needs the world to answer a more defined call the way the less defined one allows, which is a
  hypothesis on `World` every proof would carry. It's left for when InstCombine's pairs show it costs much.
- **The callee may call back into the module.** Whatever it does there is part of its answer. A claim about one
  function holds for every world, so for every callback too, as Alive2 assumes.
- **A call with effects under a promise to progress is refused**: in a function marked `mustprogress` or `willreturn`,
  in one with loops marked `llvm.loop.mustprogress`, or calling a function that makes one. LangRef counts interacting
  with the environment as progress, and `IRLean.runPromised` would call a loop that only does that undefined. Of the
  2,787 InstCombine pairs above, the 2,100 with no pointer in either side have no promise on either side's function.
- **A call to a `noreturn` function returning `void`** keeps the existing model stop, `noReturnCall`, unchanged.
- **A function with a stack frame, or that makes promises about memory,** wraps its body in `Mem.withFrame` or
  `Mem.call`, which don't pass an `Exit` through yet, so a call outside the module there is refused until they do.
- **Calls through a pointer** to anything outside the module keep stopping the model, `unknownCallee`.

## Calls that touch memory

They wait for F4, `Refines` with memory (SEM-06). A call touches memory when it passes or returns a pointer, or when the
function has memory and the call may access memory other than `inaccessiblemem`. In a function with no memory, a call
that writes any memory is a call with effects, and that's sound: the function reads no memory, so nothing it does can
see what the call wrote, except later calls, whose answers the trace keys. In a function with memory, the call could
write what the function reads next, and the model would need to say what it wrote: F4's job.

Until then they're refused by name: `call to external @F, which touches memory: F4`. So they're counted, and not
silently in another group. A call that touches only `inaccessiblemem`, which LangRef says "is not accessible by the
current module", is a call with effects even in a function with memory, since nothing the function reads can change.

F4 would key a call that reads the function's memory by that memory, as Alive2 does, and have a call that writes give a
new memory as part of its answer, for the parts the callee can reach.

## External globals

An external global is an address the model doesn't know. A function that uses one has memory, since it mentions a
pointer, so it has no `Refines` claim until F4 either way. What changes is whether it translates at all.

Supportable now: the global as a pointer to an allocation the module doesn't create. `Mem.initial` leaves it out, and a
theorem that needs it there says so, with its size from the declared type, as `Mem.Object` does for one object. Then:

- **Address arithmetic,** `getelementptr` and comparing two pointers, translates as it does for any pointer.
- **Loads and stores** translate too, reading whatever the theorem's memory holds. With `Mem.initial` alone they find
  no allocation, which is `badAccess`: more undefined behavior than LLVM, conservative for a safety proof and wrong for
  a refinement's source, so F4 has to settle it.
- **Constant `getelementptr` expressions** over an external global are checked the way they are over one the module
  defines: refused unless every step plainly stays inside the declared type.
- **Refused:** an external global whose type isn't sized, `extern_weak` ones, which may be null, and thread-local ones.

So the 394 InstCombine pairs refused for an external global would move to `memory`, the group stage 1 counts as
translated without a claim, or to the next refusal each has.

## Variadic calls

A variadic call to a function outside the module is an event like any other: each argument after the fixed ones is
part of it. Its type is part of the event too, since a variadic callee can receive `(i64 1, i64 2)` and `(i128 1, i64
2)` in the same lanes and read them differently, and so are `signext`, `zeroext` and `inreg`, which change what it
receives. So they're admitted where the same call without `...` would be. Of the 67 InstCombine pairs refused first for a variadic call, 66 mention a pointer, mostly
a format string, so they wait for F4 with the rest.

Defining a variadic function stays refused: `va_start` and `va_arg` read memory the model doesn't lay out.

## Constant expressions and linkage

- **Constant expressions over globals** are the emitter's existing rules, unchanged. External globals get the same,
  above.
- **Linkage.** A call to a declaration names whatever definition the program links. That's what makes it an unknown
  function, so its linkage doesn't matter. A call to a `linkonce_odr` or `weak_odr` definition in the module stays
  refused, as [trust](trust.md#known-gaps-in-the-model) says: the copy that runs may be another translation's. Treating
  it as a call outside the module, an unknown function with the declaration's promises, would be sound, but would throw
  away the body the module has. Whether a theorem may assume the module's copy is the one that runs is the
  one-definition-rule policy, which BIND-05's binding lane owns.

## What it changes for binding

[BIND-01's census](binding-approach.md#the-scale-measured) refuses 665 linked functions first for a call outside the
module, and 301 for `memory(...)` on a call. Almost all are LLVM's C++, which passes pointers: those wait for F4, now
refused as touching memory. What this lane gives binding is calls without effects and with integer arguments, in any
function, and the trace form for when F4 adds memory to an answer. Linking a pass's closure into one module, which turns
most of the census's calls into calls inside the module, and the one-definition-rule policy are the binding lane's.

## Slices

Each is a pull request, merged when green, with this page updated to say what's built.

1. **Calls that access no memory.** `IRLean/World.lean`: `Event`, `Trace`, `Answer`, `World`, `Exit`, its `Refine`
   instance, `Talks` and its instance, the call helpers and their laws, and one new reason, `UB.outsideCall`, in
   `IRLean.Basic`. The emitter threads `w` and `h` through functions that call outside the module, and translates pure
   calls, in any function. Tests in `tests/calls`, as `tests/freeze` does for F3. **Built** on 2026-11-09:
   `tests/calls` has eleven rewrites, four right and seven wrong, each with its theorem, and Alive2 gives seven the
   same verdict and four the one this page says it gives by design. One reason, `UB.outsideCall`, covers every broken
   promise and unwinding through `nounwind`, since the negative-verification statements list every reason.
2. **Calls with effects, and calls that only read,** in functions without memory, and calls touching only
   `inaccessiblemem` in any function. The emitter refuses calls that touch memory by name. Most of the coverage gain is
   here: of the 2,787 pairs refused first for `call to external`, 2,100 have no pointer in either side, 4 of them with
   floating point, which stays refused.
3. **External globals,** and constant expressions over them, as above.
4. **Variadic calls** to functions outside the module, as above.

## Tests

`tests/calls.sh`, like `tests/freeze.sh`: each case in `tests/calls` is a source and a target, translated, with a
theorem in `tests/calls/CallsModel.lean` proving its verdict, built with warnings as errors, on the standard axioms, and
replayed by `leanchecker`. Alive2 gives each case a verdict, and each disagreement has a stated reason. The cases are the
tables above, right and wrong: for calls with effects, adding, dropping, reordering, changing an argument and calling
twice, each refuted with `¬ Refines`; for calls without effects, dropping and merging under the right attributes,
certified, and the same without them, refuted. Where Alive2 and the model disagree by design, it's one of: Alive2 has
no unwinding, so it allows reordering or dropping calls that may unwind; it treats `memory(none)` as giving the same
answer for the same arguments, so it allows duplicating one; and it allows an argument that refines the source's.
