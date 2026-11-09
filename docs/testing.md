# Testing

How to run the checks, and what each one shows. For what the results add up to, see [status](status.md).

## Tests

The dev shell works on Linux and on Apple silicon Macs. The proofs compile for x86-64 Linux on every host, so
they check the same IR everywhere. On Macs, `lint` and `lsp` fail on C++ only: `clang-tidy` and `clangd` report
errors there that don't appear on Linux, so use `-LE 'lint|slow'` to skip them.

Run `lake build`, then `ctest --test-dir build`. Add `-LE slow` to skip `zlib_slow`. With that, on 32 cores, a first
run takes about a minute. A run with nothing changed takes about 4 s, apart from `llvm` and `superopt`, which check
everything every time, in about a minute.

| Test | What it checks |
| --- | --- |
| `opcheck` | Each integer operation against LLVM's constant folder, and against Alive2 for exact poison and UB behavior. Fails without `alive-tv`, or if it can't check a variant. `--no-alive` is the opt-out. Prints Alive2's LLVM version and this code's |
| `gepcheck` | `getelementptr`'s flags against Alive2, on many layouts, since native code can't see poison pointers |
| `differential` | Emitted Lean against natively compiled code, on real C |
| `vectors_pointers` | The same for vectors, function pointers, pointers in globals and the heap, GEPs LLVM defines, and promises kept, failing if any input is skipped |
| `undefined` | Code LLVM calls undefined stops the model, since comparing with native code can't show that |
| `memory_errors` | Memory errors through the emitter each stop the model for their own reason: out of bounds, after a free, through a dangling pointer or the wrong provenance, null, misaligned, an overlapping copy, a write to a constant, and frees of what `malloc` didn't return |
| `model_stops` | Where LLVM doesn't say it's undefined, the model stops without an answer |
| `model_stops_are_not_undefined` | `--expect-ub` says those aren't undefined |
| `emitter` | What the emitter refuses and accepts on purpose, IR that fails LLVM's verifier, a value named like a name emitted code binds, checks only seen by running, the default namespace, and that `opcheck` can't pass quietly without Alive2 |
| `fuzz` | The same comparison on random functions, optimized at random levels |
| `proofs` | The proofs against freshly generated Lean, that each theorem names its generated function, that breaking the C stops the proof with an error that isn't running out of time or memory, that a proof can only rest on the standard axioms and `bv_decide`'s, with no `implemented_by` or `extern`, and that `leanchecker` replays it |
| `llvm` | [LLVM's own code](llvm.md): functions from `llvm-project` at the pinned tag, compiled as upstream does, against their proofs, checked as `proofs` checks them, with an injected bug for each that has to stop its proof with an error of its own. Prints the score. `--manifest` writes what each theorem says and rests on, and what stopped each bug's proof |
| `llvm_scope` | The checks on [claims about LLVM's passes and the task list](llvm-verification-tasks.md), without LLVM: no claim counts as done without an independent verifier, finite translation validation never counts for all inputs, a stale hash or evidence outside the repo is refused, and the list's scope line matches the inventory. Python only |
| `llvm_scope_check` | The inventory of every name the pinned LLVM registers a pass or codegen implementation under, derived again from its source, `opt` and `llc`, and compared byte for byte, so the denominator can't move quietly. About 5 s, and no Lean |
| `superopt` | What a search finds for real functions, against Alive2 and a Lean theorem that names both and says they do the same, and that a wrong rewrite fails both, with an error in Lean and a counterexample from Alive2. An Alive2 timeout is never a pass. `--bench` also measures it against `clang -O3`, which CI doesn't, since timings vary |
| `names` | Every word Lean reserves is avoided in generated names |
| `undef_freeze` | [An experimental `undef` and `freeze` semantics](undef-freeze.md), not the model's: it builds with warnings as errors, LangRef's examples get LangRef's verdicts, four shortcuts each certify a wrong rewrite it rejects, both modules rest on the standard axioms and `leanchecker` replays them, two false proofs and a `sorry` are refused, five edits to a copy of it each stop the theorem they target, and Alive2 gives the same verdict on 31 rewrites. One process at a time, each Lean process capped at 2 GB, about 17 s of CPU |
| `verify` | [`tools/verify.py`](verify.md) gives each status and reason when it should, refuses proofs that cheat, and no required check can be missing from a proved result |
| `verify_negative_static` | [What counts as a certificate](llvm-negative-verification.md): a stored proved result is certified, and broken, stale or mismatched ones aren't, nor answers from checkers that hang, crash or print nonsense. Python only |
| `verify_negative` | Wrong LLVM rewrites, and right ones outside the model, are never certified through `tools/verify.py`, and four right ones are. Runs alone, one Lean process at a time, about 2 minutes |
| `replay_challenge_static` | [Challenging replay certificates](replay-challenge.md): manifests `tools/binding.py` has to refuse before it reads a tool, and its runner calling a crash, a timeout or running out of memory unknown, and leaving nothing running. A finding it shows is accepted as known, and the contract's answer too. Python only, about 4 s |
| `replay_challenge_alive` | The same: Alive2 agrees with LangRef, worked out by hand, on 17 poison and flag rewrites and every case in `tests/verification_negative`, with and without `undef` arguments, and two disagreements have the reason given checked. A certified case Alive2 finds wrong fails. One capped `alive-tv` at a time, about 5 s |
| `replay_challenge` | The same: IRLean's model fails each poison and flag rewrite on exactly the inputs worked out by hand, which hold Alive2's counterexample, and `tools/binding.py` on real `opt` runs gives the reasons `binding` doesn't reach, with Alive2 agreeing with each bound bundle. Runs alone, one Lean process at a time, about 75 s |
| `binding` | [Binding a certificate to LLVM](llvm-proof-binding.md): one real `instcombine` rewrite is bound, and a certificate is refused, unsupported, unknown or an error, with the reason it should give, when its theorem's type, a file, the pass, the triple, the data layout, llvm-project, a tool or the cache doesn't match, when the model can't judge the function, and when a limit stops it. Never `bound` otherwise. Runs alone, one Lean process at a time, about 5 minutes |
| `contracts` | [Semantic contracts](llvm-semantic-contracts.md): LangRef's integer poison rules, as Lean predicates the model meets at every width. They build with warnings as errors, LangRef's poison examples hold, seven semantics LangRef rules out each fail their contract, both modules rest on the standard axioms and `leanchecker` replays them, a false proof and a `sorry` are refused, and five edits to a copy of `IRLean/Int.lean` each stop the theorem they target with an error that isn't a resource limit. One Lean process at a time, each capped at 2 GB, about 12 s |
| `refine` | [Refinement](refinement.md): `IRLean.Refines` builds with warnings as errors and rests on the standard axioms, right rewrites refine and nine known-wrong ones provably don't, memory has no claim, the claim `tools/binding_check.lean` builds is the statement a certificate elaborates, a false proof fails, and two edits to a copy of `IRLean/Int.lean` each stop the case guarding them. One Lean process at a time, each capped at 2 GB, about 10 s |
| `cpp_correspondence` | [LLVM's C++](llvm-cpp-correspondence.md): a model of the pinned `simplifyAddInst`, proved right at every width, its quotes of the C++ at the pinned hashes and lines, with every code line quoted, and its answers against `opt -passes=instsimplify` on generated `add`s, with a changed quote, a missing one and two broken models each caught. One Lean process at a time, each capped at 2 GB, about 12 s |
| `zlib` | All of zlib translates, and real calls into it match native code, failing if any input is skipped |
| `zlib_slow` | The same for the calls that slide `deflate`'s window, the slowest of them |
| `lint` | Every formatter and linter below, for every language |
| `lsp` | Every language server below starts, opens real files, and reports no errors in them |

The dev shell sets `CTEST_PARALLEL_LEVEL`, how many tests run at once, and `LEAN_JOBS`, how many Lean processes
each runs at once, from the machine's cores and memory. Compiled modules stay in `build/lean-cache`, so a run only
recompiles what changed. `proofs` keeps its compiled modules and the checks that passed in `build/proof-cache`, and
the other tests keep what Lean printed and what Alive2, `clang-tidy` and the language servers passed in
`build/result-cache`. These are named after everything they read, so a test only repeats what could come out
differently, and only a pass is kept. CI doesn't keep those two directories, so it works everything out on every
run. To do the same locally, delete them.

`tests/bench.py` times what you wait for after each kind of change, from a cold build to an edit to the model, with
real edits it undoes afterwards.

`tests/proof_bench.py build/ir-lean` times checking each proof on its own, against the Lean the tests generate, and
the peak memory each one takes. `--llvm CrtUdivmoddi4` adds a target's proof, and `--proof Crc32=FILE` checks another
version of a proof on the same obligations, so two versions can be compared. [Status](status.md#what-checking-costs)
has what it measured.

## Formatters, linters and language servers

| Language | Formatter | Linter | Language server |
| --- | --- | --- | --- |
| C++ | `clang-format` | `clang-tidy` | `clangd` |
| C test inputs | `clang-format` | `clang -Wall -Wextra` | `clangd` |
| Lean | None exists | Lean's own linters, with `lake build --wfail`, and warnings as errors in `tests/llvm.py` | `lake serve` |
| Python | `ruff format` | `ruff check`, `ty check` | `ty server`, `ruff server` |
| Shell | `shfmt` | `shellcheck` | `bash-language-server` |
| Nix | `nixfmt` | `statix`, `deadnix` | `nixd` |
| CMake | `gersemi` | `cmakelint` | `neocmakelsp` |
| TOML | `taplo fmt` | `taplo lint` | `taplo lsp` |
| YAML | `yamlfmt` | `actionlint` | `yaml-language-server` |
| Markdown | `rumdl fmt` | `rumdl check` | `rumdl server` |
| LLVM IR test inputs | None exists | `opt -passes=verify` | None exists |

`tests/lint.sh` runs them all, and `tests/lint.sh --fix` has the formatters rewrite what they can.
`editorconfig-checker` also checks whitespace in every file, which is the only check on how Lean files are
laid out. CI runs all of this, the tests and the proofs on every pull request and push to `main`, and
`zlib_slow` on pushes to `main`. To run `zlib_slow` on a branch before merging it, use
`gh workflow run CI --ref BRANCH`.

Python scripts need nothing beyond the standard library, and run through `uv`, which also pins `ruff` and
`ty` in `uv.lock`.

`clangd` needs `build/compile_commands.json`, which `cmake` writes. To open the proofs in an editor, first
run this, so the language server can find the generated modules they import:

```console
tests/proofs.sh build/ir-lean --generate build/generated
```
