# Memory safety

What a memory-safety theorem from `ir-lean` claims, the model of memory it's about, and what that model leaves out.
[Trust](trust.md) has what every theorem rests on, and all of it applies here.

## What's proved

| Proof | About | What it says |
| --- | --- | --- |
| [`UpdateWindow.lean`](../tests/proofs/UpdateWindow.lean) | zlib's `updatewindow`, from `inflate.c` | It returns 0 with no undefined behavior or model stop, changes nothing but the window's first `wsize` bytes and three fields, and leaves its invariant holding for the next call. So the same holds across any number of calls |
| [`MemoryModel.lean`](../tests/proofs/MemoryModel.lean) | The model itself | What it does with accesses out of bounds, after a free or return, through null or poison, misaligned, and with bad frees and overlapping copies, each naming the undefined behavior it gives |

`updatewindow` copies what `inflate` just wrote into the sliding window that later back-references read. At `-O2` it's
11 blocks and 83 IR instructions, with three `memcpy`s, and each is safe only if the state is: `wnext` inside the window,
the window as big as `wsize` says, and `copy` bytes of output behind `end`.
[Phase 1](roadmap.md#phase-1-zlib-inflate-memory-safety) needs it as a contract, since `inflate` calls it, though this
one covers only calls after the window is allocated, through a `strm` that carries no promises.

```lean
theorem updatewindow_safe {m : Mem} {copy : BitVec 32} (hu : m.Unrestricted)
    (S : Stream m z zo s w ws wbits wsize whave wnext)
    (O : Output m w e eo (min copy.toNat (size wbits wsize).toNat)) :
    ∃ m' whave' wnext',
      updatewindow (some ⟨z, BitVec.ofNat 64 zo, []⟩) (some ⟨e, BitVec.ofNat 64 eo, []⟩) (some copy) m =
        Outcome.ok (some 0#32, m') ∧
      Stream m' z zo s w ws wbits (size wbits wsize) whave' wnext' ∧
      wnext'.toNat < (size wbits wsize).toNat ∧
      Mem.Changes m.afterCall m' (Touched s w (size wbits wsize).toNat)
```

`size wbits wsize` is the window's size once it's set up: `wsize`, or `1 << wbits` the first time. `Touched` is that
many bytes at the start of the window, and bytes 60 to 72 of the state, which hold `wsize`, `whave` and `wnext`.

Since `Stream` holds again afterwards, `updates_safe` follows: for any list of calls, each with its own output and
`copy` that meet `Output`, every call returns, and the whole sequence changes only `Touched`. That's the shape of the
claim [Phase 1](roadmap.md#phase-1-zlib-inflate-memory-safety) wants for `inflate`, for one of the functions it calls.

### The preconditions

- **No running call restricts memory:** `m.Unrestricted`, which holds outside any call, and inside a call of a
  function with no `memory(...)` attribute and nothing that tracks writes. `strm` and `end` carry no promises of their
  own. `updatewindow`'s own `readonly`, `nofree` and `captures(none)` on both are checked on each access, not
  assumed.
- **`Stream`:** `strm`, at offset `zo` of allocation `z` and 8-aligned, holds a pointer to the start of allocation `s`
  in its `state` field. `s` is at least 80 bytes, writable and 8-aligned. It holds `wbits`, `wsize`, `whave` and
  `wnext` at x86-64 Linux's offsets, and in `window`, a pointer to the start of allocation `w`, which is `ws` bytes
  and writable. `z`, `s` and `w` are different allocations, and the pointers stored in them carry no tags.
- **`Fits`:** before the window is in use, when `wsize` is 0, `wbits < 32` and `2 ^ wbits ≤ ws`. After, `wnext ≤ wsize ≤
  ws`. zlib keeps `wbits` between 8 and 15, which this allows.
- **`Output`:** `end` is offset `eo` of allocation `e`, which isn't `w`, with `eo` at most `e`'s size and at least
  `min copy (size wbits wsize)`, so `copy` bytes before `end`, or a whole window's worth if that's less. `inflate`
  passes `next_out` and how much it wrote, so this holds when its caller's buffer is valid.
- **Every allocation it uses is an `Object`:** not allocation 0, smaller than `2 ^ 63`, not at address 0, and not
  crossing the top of the address space, as LangRef requires. `Mem.base` promises none of this.
- **The window is already allocated.** If it isn't, `updatewindow` allocates it through `strm->zalloc`, a call through a
  pointer to code outside the module, which stops the model, so nothing is proved about that path. That's the path
  `inflate`'s first output after `inflateInit` takes.
- **`strm` carries no promises.** `inflateSetDictionary` passes one tagged with its own `readonly`, `nofree` and
  `captures(address)`, so this doesn't cover that call as it stands.

`initial_safe` meets all of these with one memory, a stream as `inflateReset` leaves one whose 32 KiB window was
already allocated, so they can all hold at once. It has `wsize` 0, and the memory the theorem gives back meets them
again with `wsize` set.

### Four preconditions are needed

For each of these four, a state that breaks it is undefined in the model. Each theorem holds for every memory that
fits, and adds hypotheses that pick out the path where the bug shows: breaking one alone doesn't always matter, since a
call that copies nothing, say, touches no window. The other preconditions have no theorem like this.

| Theorem | Breaks | On the path where | The model gives |
| --- | --- | --- | --- |
| `window_too_small` | `wsize ≤ ws` | `copy` is at least `wsize` | `badAccess`: copying a whole window writes past its end |
| `wnext_past_wsize` | `wnext ≤ wsize` | `copy` is less than `wsize`, and `wnext + copy` is past the window | `badAccess`: `wsize - wnext` wraps around, so the copy isn't cut off at the window's end |
| `output_too_short` | Room behind `end` | `wsize` is set and more than `copy`, and `end` has fewer than `copy` bytes before it | `noundefPoison`: `end - copy` with `inbounds` is poison, and `memcpy`'s argument is `noundef` |
| `window_freed` | A live window | `copy` is at least `wsize`, and only the state is assumed, not all of `Stream` | `badAccess`: `state->window` dangles, and `memcpy`'s `dereferenceable(1)` on it fails |

`tests/proofs.sh` also puts three memory bugs into `inflate.c`, each of which has to stop the proof: not cutting the
copy off at `copy`, which reads past what the output has, a `wsize` twice the window, and copying one byte too many.

### What it doesn't say

- Which bytes end up in the window. That's correctness, and would be another theorem.
- Anything about `inflate`. Neither caller, `inflate` or `inflateSetDictionary`, translates, since they call functions in
  other files, such as `crc32`, `adler32` and `inflate_fast`, and showing that `inflate` keeps `Stream` is Phase 1's
  work.
- Anything about `whave`, which this function doesn't need bounded. Reading the window back will.
- Anything below the IR, beside it or around it: native code, other threads, the stack's size, or the rest of the
  program.

## What memory-safe means here

[Trust](trust.md#what-a-theorem-covers) calls a function memory-safe when the model never stops on a memory error for
inputs meeting the preconditions. `updatewindow_safe` says more, and it has to: the function returns, with no undefined
behavior of any kind and no model stop, and `Changes` says which bytes it may have changed. A theorem that allowed other
undefined behavior would say nothing about LLVM, where everything after undefined behavior is undefined. One that allowed
a model stop would say nothing about what LLVM does from there.

`Changes m m' touched` is what makes it more than "no undefined behavior": every allocation keeps whether it exists,
its size and its flags, every byte outside `touched` is as it was, and nothing else about memory changes. So the
function can't have left anything else changed, in any allocation. It compares the memory before and after, so a byte
written and then put back wouldn't show.

It's a theorem about one function. It says nothing about the program around it, about native code, or about the
source, and it needs the model to match LLVM, which the rest of this doc and [Trust](trust.md#known-gaps-in-the-model)
qualify.

## The model of memory

`Mem`, in [`Mem.lean`](../IRLean/Mem.lean), is memory as the model holds it.

### What it represents

| Aspect | How | Checked by |
| --- | --- | --- |
| Objects | Allocations numbered from 1, each with a size, its bytes, and whether it's writable, came from `malloc`, or came from `alloca`. Globals, `alloca` and `malloc` make them | `MemoryModel.lean`, `memory_errors` |
| Bounds | An access is undefined unless all its bytes are inside its allocation. An `inbounds` step that leaves the allocation and the byte just past it is poison | `load_past_end`, `store_past_end`, `load_before_start`, `gep_before_start`, and [the GEP rules](trust.md#closed) against Alive2 |
| Aliasing | Two pointers alias exactly when they reach overlapping bytes of one allocation. Memory is bytes with no types, as in LLVM IR, so there are no type-based rules, and `tbaa` and scoped `noalias` metadata are refused | `memcpy_overlap`, and the GEP rules |
| Provenance | A pointer is an allocation, an offset and tags. An access reaches only its own allocation, whatever its address is, and a pointer stored in memory keeps its provenance | `past_end_any_layout`, and `wrong_provenance` in `memory_errors.ll` |
| Heap lifetime | `free` removes the allocation, so any later access through any pointer into it is undefined. Freeing twice, freeing a stack object or global, or freeing an interior pointer is undefined | `use_after_free`, `double_free`, `free_not_heap`, `free_interior` |
| Stack lifetime | A function's `alloca`s are removed when it returns, so writing through a pointer that got out is undefined. With `llvm.lifetime.start` and `.end`, an `alloca` outside its lifetime reads as poison and writing it is undefined, as LangRef says | `dangling_after_return`, `load_after_lifetime_end`, `store_after_lifetime_end`, `dangling_stack` in `memory_errors.ll`, and `ub.ll` |
| Constants | Writing a constant global is undefined | `store_readonly`, and `store_to_constant` in `memory_errors.ll` |
| Alignment | A load or store is undefined unless its address is a multiple of its alignment, in the layout `Mem.base` gives. `memset` and `memcpy` take theirs from the `align` attribute on the pointer, which makes a misaligned one poison, so it's undefined as a poison pointer, not as `misaligned` | `load_misaligned`, and `memset_misaligned` and `memcpy_misaligned` in `ub.ll` |
| Null and poison | Null points to allocation 0, which code from the emitter never makes. Accessing through a poison pointer is undefined | `load_null`, `load_poison`, `store_poison` |
| Copies | `memcpy` between ranges that overlap without being the same is undefined | `memcpy_overlap` |
| Uninitialized memory | A read gives poison, which is stricter than LLVM's `undef` | [Trust](trust.md#known-gaps-in-the-model) |
| Promises | `readonly`, `memory(...)`, `captures` and the rest, through tags on pointers and running calls | `ub.ll`, `promises.ll` |
| The allocator's choices | Where each allocation is, `Mem.base`, and whether each `malloc` fails, `Mem.failAlloc`, are oracles, so a theorem for every `Mem` holds whatever they are | By construction |

### What it leaves out, or does differently

| Aspect | What the model does | Direction |
| --- | --- | --- |
| Addresses | `Mem.base` is unconstrained: allocations can overlap, start at 0, wrap, or ignore the alignment an `alloca`, global or `malloc` promises. A theorem assumes `Object` of each allocation it uses, and the alignment its accesses need. Nothing says two allocations don't overlap, which no theorem here needs | Each theorem states its layout |
| Null | `Mem.empty` has no allocation 0. `alloca` and `malloc` number from `next`, which starts at 1, and the emitter numbers globals from 1, but `Mem.addGlobal` would make allocation 0 if asked. So a theorem about any `Mem` has to assume `m.allocs 0 = none` | Stated where it's needed |
| A stack object after its function returns | Gone, so a load is undefined. LangRef calls it dead, and loading from a dead stack object gives poison | More UB. Fine for safety, wrong for the source side of a refinement |
| `inbounds` on an allocation that's gone | Poison, since the model has forgotten its size. LangRef counts a pointer in bounds of a deallocated object as in bounds | More UB. Fine for safety |
| `inttoptr`, exposure, round trips through integers | Refused. `ptrtoint` gives an address, with no notion of exposure | Refused, so sound |
| A stored pointer read as an integer, or part of one, or integer bytes other than zero read as a pointer | The model stops | No answer |
| `tbaa`, scoped `noalias` metadata, `noalias` arguments | Refused | Refused, so sound |
| Atomics, volatile, other threads, data races | Refused | Refused, so sound |
| Address spaces other than 0, or memory other than 64-bit little-endian | Refused | Refused, so sound |
| Stack overflow, `alloca` failing | Never happen, and recursion depth is unbounded | A function proved safe can still overflow a real stack |
| `realloc`, `calloc`, other allocators, objects that grow | Calls to them are refused, or stop the model through a pointer | Refused, so sound |
| Leaks | Not a safety property here, and not tracked | Out of scope |

### Memory in a refinement

A safety theorem is about one function. A [refinement](refinement.md#functions-with-memory) compares two, and since
2026-11-10 `IRLean.Refines` has an instance for functions with memory: both get the same memory, and the memories they
leave are related by `Mem.le`, in [`MemRefine.lean`](../IRLean/MemRefine.lean), which asks for the same allocations and
bytes the source's allow. For a refinement the direction of each difference above matters by side: more undefined
behavior than LLVM is conservative for safety and for a target, and wrong for a source.

| Aspect above | For a refinement |
| --- | --- |
| Uninitialized memory read as poison | Wrong in a source that reads it. In the memory a run leaves, an uninitialized byte allows any byte but poison, which is right whether it's `undef` or poison |
| A stack object after its function returns | Wrong in a source that loads through a pointer to one |
| `inbounds` on an allocation that's gone | Wrong in a source that does it |
| Addresses, `Mem.base` | Fine on both sides: a claim for every layout covers the real ones |
| A stored pointer read as an integer, and the other way | No claim: a source that stops the model allows nothing, and a target that does isn't allowed |
| The allocator's choices | Both sides face the same `base` and `failAlloc`, and number their allocations the same. A target that allocates differently has no claim yet |

[Refinement](refinement.md#memorys-gaps-each-with-its-side) has what a claim has to assume for each.

## Writing a memory-safety proof

[`Safety.lean`](../IRLean/Safety.lean) keeps memory abstract, so a proof never unfolds a chain of writes:

| Piece | What it is |
| --- | --- |
| `Mem.Object m b n` | Allocation `b` is live, `n` bytes long, and placed as LangRef requires |
| `Mem.Writable`, `Mem.HoldsInt`, `Mem.HoldsPtr` | It isn't constant, and what some of its bytes hold |
| `Mem.Unrestricted`, `Mem.TagsAllow` | No running call restricts memory, and a pointer's tags allow an access |
| `Mem.Changes m m' touched` | `m'` is `m` with at most those bytes changed. `trans` and `mono` compose it, and it keeps `Object`, `Writable` and what's held outside `touched` |
| `Object.loadInt`, `.loadPtr`, `.storeInt`, `.memcpy`, `.gep`, `.gep_back` | Each operation on memory described this way, giving its result and a `Changes` |
| `access_past_end`, `access_gone`, `memcpy_past_end`, `Object.gep_back_out`, `dereferenceable_gone` | The same, for what the model rules out |
| `call_unrestricted`, `call_stop` | Through `Mem.call`, for a function that promised nothing about memory |

[`MemRefine.lean`](../IRLean/MemRefine.lean) adds lemmas that hold on any memory, with calls that track writes and
restrict access among those running, which the ones above assume away with `Mem.Unrestricted`:

| Piece | What it is |
| --- | --- |
| `Mem.storeInt_eq`, `storeInt_ok`, `storeInt_error_or_ok`, `access_ok_iff` | What a store is, what one that returns did, and what a valid access says |
| `Mem.check_write`, `access_write_self`, `storeInt_write_self` | A store leaves every check and the same access as they were, so a second store through the pointer returns too |
| `Mem.loadInt_write_self`, `loadInt_of_storeInt` | A load of what was just stored gives it back, if a promise lets it read |
| `Mem.storeInt_overwritten`, `write_write_le` | Two stores through one pointer leave what the second alone would |
| `Mem.check_ne_model`, `storeInt_ne_stop` | Where no running call restricts memory, a check and a store never stop the model |

A store goes like this, and the memory after it stays a variable:

```lean
obtain ⟨m1, h1, F1, H1⟩ := O.storeInt W (by omega) (.inr (by omega)) hu (Mem.tagsAllow_nil _ _ _) x
-- h1 : m.storeInt (some ⟨s, BitVec.ofNat 64 60, []⟩) (some x) 4 = Outcome.ok m1
-- F1 : Mem.Changes m m1 (fun b i => b = s ∧ 60 ≤ i ∧ i < 64), H1 : m1.HoldsInt s 60 x
```

`UpdateWindow.lean` proves each block this way, one lemma each, and `run_ok` puts them together.

## What the proof depends on

`UpdateWindow.lean` is about the generated `Inflate.updatewindow`, so it depends on how the emitter prints it: block
names and arguments, and how each `getelementptr`, `memcpy` and attribute comes out. A change that prints any of those
differently can break a block lemma, and the fix belongs in the proof. It also depends on zlib's source at the version
the flake pins, and on the x86-64 Linux layout of `z_stream` and `inflate_state`.
