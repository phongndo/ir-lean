# llvm-lean

A Lean backend for LLVM IR.

LLVM backends lower IR to code for a target. This project adds Lean as a target:
LLVM IR goes in and Lean comes out, whichever front end produced the IR.

## Status

Nothing is built yet. `nix develop` provides LLVM and Lean.
