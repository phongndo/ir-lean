"""ir-lean's shared Python, standard library only. Every tool in tools/ and every test in tests/ runs
processes, hashes files, calls Lean and writes JSON through it, so each of those is done one way, in one
place:

- `proc`: running a command under a time limit and a memory cap, killing everything it started, measuring what
  it cost, and the machine's heavy-job lock.
- `hashing`: SHA-256 of bytes, files and trees, streamed, and in parallel for trees.
- `lean`: `lean`, `lake` and `leanchecker` with their limits, Lean's messages and limits, and the axiom audit.
- `schemas`: every versioned JSON schema the repo writes, and reading and writing them.
- `pins`: the toolchain the repo pins, and the identity of the binaries on PATH.
- `model`: what IRLean declares that Python needs, such as `IRLean.UB`'s constructors.
- `verdict`: the one place Python decides that something is proved, certified, refuted or caught.

docs/python.md says what goes here and what doesn't. A script reaches it with

    sys.path.insert(0, str(Path(__file__).resolve().parents[N] / "tools"))

where N takes it to the repo's root, as Python only looks next to the script.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
