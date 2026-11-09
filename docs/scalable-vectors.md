# Scalable vectors

How the model reads `<vscale x N x iM>`, `llvm.vscale` and `vscale_range`, and the decision of 2026-11-09 that
`vscale` is a parameter that `IRLean.Refines` quantifies over, not a choice. For what any theorem means, read
[trust](trust.md) first.

## What LangRef says

At the pin, LangRef 23.1.3 says of the type: "For scalable vectors, the total number of elements is a constant
multiple (called vscale) of the specified number of elements; vscale is a positive power-of-two integer that is
unknown at compile time and the same hardware-dependent constant for all scalable vectors at run time." Of
`llvm.vscale`: "`vscale` is a positive power-of-two integer that is constant throughout program execution, but is
unknown at compile time. If the result value does not fit in the result type, then the result is a poison value."
And of `vscale_range(<min>[, <max>])`: it "indicates `vscale` is a power-of-two within a specified range", with `max`
0 for no maximum, and "Functions that don't include this attribute make no assumptions about the range of `vscale`."

So `vscale` is a fact about the machine: one value for a whole run, the same in every function.

## The decision: a parameter

**`vscale` is a parameter every function takes, and `Refines` quantifies over it like any argument, the same value on
both sides.** In a module where anything depends on it, a scalable type, `llvm.vscale` or `vscale_range`, every
function takes an `IRLean.VScale` first, `vs'`, and passes it to every function it calls. `VScale` is `2 ^ log`, so
every value is a positive power of two and every positive power of two is one: quantifying over it is quantifying
over every `vscale` LangRef allows. A `<vscale x N x iM>` is a `Vec (vs'.val * N) M`.

`vscale_range` doesn't narrow the quantifier. A function with it may assume `vscale` is in its range, so a run outside
the range is undefined, checked when the function is entered. For refinement that's the right side of each:

- **A target that adds `vscale_range`** is undefined where the source isn't, outside the range, so it doesn't refine.
  An optimizer can't add the promise.
- **A target that drops it** is defined where the source was undefined, which refines.
- **A source with it** allows anything outside its range, as LLVM's optimizer assumes.

The reason the model gives for a run outside the range is `UB.assumeFailed`, since the attribute is an assumption
the function makes, as `llvm.assume` is. A reason of its own would change the list of reasons every committed
negative-verification statement spells out, for no difference in what any claim says.

### Why not a choice

[F3](refinement.md#runs-that-make-choices) gives the model one way to say a run can go more than one way:
`IRLean.Choice`, which `Refines` quantifies as "for every way the target chooses, some way the source chooses". If
`vscale` were a choice, the source could choose a different `vscale` from the target's: a target that returns `4`
would refine a source that returns `llvm.vscale`, since for every way the target runs, the source could choose 4. On
a machine whose `vscale` is 8, the source returns 8 and the target 4. An optimizer can't assume the source runs on
another machine than the target. A parameter shared by both sides is what LangRef's "the same hardware-dependent
constant" says.

### Why not something else

- **One `vscale` for the whole module, as a section variable or a global:** emitted code is plain definitions, and
  each function's type has to say what it depends on for `Refines` to quantify over it.
- **Only the functions that use it take it:** every function then needs to know which callees do, as for choices,
  and a function without scalable types still has to take it when it has `vscale_range`, which changes what it means.
  Taking it everywhere in such a module is simpler, and a function that doesn't use it computes the same for every
  value.

## What's modeled

| Item | How |
| --- | --- |
| `<vscale x N x iM>` | `Vec (vs'.val * N) M`. Every operation on vectors of integers in `IRLean.Vec` and `IRLean.Lanes` takes any number of lanes, so each works lane by lane as on a fixed-width vector |
| Constants | A splat, `splat (iM k)`, is `Vector.replicate (vs'.val * N) k`, and `zeroinitializer` and `poison` likewise |
| `shufflevector` | LLVM allows only two masks on a scalable vector: all zero, lane 0 in every lane, which is `Vec.splat0`, and poison |
| `llvm.vscale` | `VScale.value`: `vscale`, or poison if it doesn't fit |
| `llvm.stepvector` | `Vec.stepvector`: lane `i` is `i`, truncated to the lane width, on fixed-width vectors too |
| `llvm.vector.reverse` | `Vec.reverse`, on fixed-width vectors too |
| `llvm.vector.insert`, `llvm.vector.extract` | `Vec.insertSub` and `Vec.extractSub`: a run of lanes from the index, times `vscale` when the part is scalable, and poison if the run isn't all lanes of the vector, as LangRef says. On fixed-width vectors too |
| `vscale_range` | `VScale.range`, at the function's entry |

`IRLean.Scalable` also has an instance of `Refine` for functions whose result type depends on their argument, as one
taking a `VScale` does, below `IRLean.Refine`'s own instance for functions, so nothing that elaborated before picks a
different instance.

## What's refused

- Scalable vectors of floating point or pointers, as for fixed-width ones.
- A scalable vector in memory: a `load` or `store` of one, a `getelementptr` over one, and an `alloca` of one. `Mem`
  counts bytes, and these are a multiple of `vscale`. Memory is F4's.
- A recursive function, or one with more than 32 blocks, in a module where anything depends on `vscale`: only the
  flat blocks and `step` take it so far.
- A scalable vector passed to or returned from a call outside the module. [Calls](calls.md#the-model) pass each value
  as its lanes, and the emitter lists the lanes of integers and fixed-width vectors of them only, so far.
- `bitcast` of a scalable vector, and the scalable intrinsics besides the five above, such as
  `llvm.get.active.lane.mask`, the `llvm.vp.*` family and `llvm.vector.splice.*`, and the target intrinsics that
  take scalable vectors, such as AArch64's SVE ones.

## How it's checked

Alive2 can't read scalable vectors, so `tests/scalablecheck.py`, the `scalablecheck` test, ties them to what can be
checked:

- Each of 43 operations on `<vscale x 4 x i8>`, run at `vscale` 1, 2 and 4, gives exactly what the same operation on
  4, 8 and 16 lanes gives, lane for lane, on random inputs with poison lanes, undefined behavior included. The
  fixed-width operations are checked against Alive2 and the constant folder by `opcheck` and `vecopcheck`.
- LLVM's constant folder folds operations on scalable splats without knowing `vscale`. The model gives that splat in
  every lane, at each `vscale`.
- `llvm.vscale` gives `vscale`, and poison at `i2` from `vscale` 4, and a function with `vscale_range(2,4)` or
  `vscale_range(2,0)` is undefined exactly outside the range, for `vscale` 1 to 16.

`llvm.stepvector` and `llvm.vector.reverse`, which neither Alive2 nor the constant folder knows at the pin, and
`llvm.vector.insert` and `llvm.vector.extract`, are checked against native code on fixed-width vectors, in
[`tests/real/lanes.ll`](../tests/real/lanes.ll).

A proof about a function that takes `vscale` is for every `vscale`, so `bv_decide`, which needs fixed widths, can't
close it alone: it needs induction on `vs'.log`, or a lemma that a lane-by-lane function's result depends only on its
lanes. None is written yet.
