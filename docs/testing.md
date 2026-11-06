# Testing

How to run the checks, and what each one shows. For what the results add up to, see [status](status.md).

## Tests

The dev shell works on Linux and on Apple silicon Macs. The proofs compile for x86-64 Linux on every host, so
they check the same IR everywhere. On Macs, `lint` and `lsp` fail on C++ only: `clang-tidy` and `clangd` report
errors there that don't appear on Linux, so use `-LE 'lint|slow'` to skip them.

Run `lake build`, then `ctest --test-dir build`, which takes about 25 minutes. Add `-LE slow` to skip
`zlib_slow` and take about 5.

| Test | What it checks |
| --- | --- |
| `opcheck` | Each integer operation against LLVM's constant folder, and against Alive2 for exact poison and UB behavior. Fails without `alive-tv`, or if it can't check a variant. `--no-alive` is the opt-out. Prints Alive2's LLVM version and this code's |
| `gepcheck` | `getelementptr`'s flags against Alive2, on many layouts, since native code can't see poison pointers |
| `differential` | Emitted Lean against natively compiled code, on real C |
| `vectors_pointers` | The same for vectors, function pointers, pointers in globals and the heap, GEPs LLVM defines, and promises kept, failing if any input is skipped |
| `undefined` | Code LLVM calls undefined stops the model, since comparing with native code can't show that |
| `model_stops` | Where LLVM doesn't say it's undefined, the model stops without an answer |
| `model_stops_are_not_undefined` | `--expect-ub` says those aren't undefined |
| `emitter` | What the emitter refuses and accepts on purpose, the default namespace, and that `opcheck` can't pass quietly without Alive2 |
| `fuzz` | The same comparison on random functions, optimized at random levels |
| `proofs` | The proofs against freshly generated Lean, that breaking the C breaks the proof, and that a proof can only rest on the standard axioms and `bv_decide`'s |
| `names` | Every word Lean reserves is avoided in generated names |
| `zlib` | All of zlib translates, and real calls into it match native code, failing if any input is skipped |
| `zlib_slow` | The same for the calls that slide `deflate`'s window, at minutes each |
| `lint` | Every formatter and linter below, for every language |
| `lsp` | Every language server below starts, opens real files, and reports no errors in them |

`LEAN_JOBS` sets how many Lean processes run at once, 4 by default. What limits it is memory. Compiled modules
stay in `build/lean-cache`, so a run only recompiles what changed.

## Formatters, linters and language servers

| Language | Formatter | Linter | Language server |
| --- | --- | --- | --- |
| C++ | `clang-format` | `clang-tidy` | `clangd` |
| C test inputs | `clang-format` | `clang -Wall -Wextra` | `clangd` |
| Lean | None exists | Lean's own linters, with `lake build --wfail` | `lake serve` |
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
