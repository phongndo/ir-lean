"""Every versioned JSON schema the repo writes, and reading, writing and checking records of them.

A record names its schema in a `schema` field, as `ir-lean.NAME/VERSION`. A change a reader of the old version
would misread takes a new version. A reader checks the name and version before it reads anything else, and
refuses a record of another schema, rather than reading what it can of it.

Each schema is named once, here, and every tool and test takes the name from here. tests/irlean_test.py fails
if a schema is written anywhere else, or if two of these name one schema.
"""

from __future__ import annotations

import json
import os
import re
import secrets
from pathlib import Path
from typing import Any

# The pattern every schema name follows.
NAME = re.compile(r"ir-lean\.[a-z0-9][a-z0-9_.-]*/[1-9][0-9]*")

# tools/measure.py: what one command cost. docs/corpus.md.
MEASUREMENT = "ir-lean.measurement/1"
# tools/corpus/capture.py: a captured case, and the toolchain a corpus was captured with. docs/corpus.md.
CORPUS_CAPTURE = "ir-lean.corpus.capture/1"
CORPUS_PIN = "ir-lean.corpus.pin/1"
# tools/verify.py: a request, and its result. docs/verify.md.
VERIFY = "ir-lean.verify/1"
VERIFY_REQUEST = "ir-lean.verify.request/1"
# tools/binding.py: a bundle's manifest, and a verdict on it. docs/llvm-proof-binding.md.
BINDING_MANIFEST = "ir-lean.binding.manifest/2"
BINDING_VERDICT = "ir-lean.binding.verdict/1"
# tools/prooftest/prooftest.py: a request, its result, the store of counterexamples, and bench.py's report.
# docs/proof-tests.md.
PROOFTEST = "ir-lean.prooftest/1"
PROOFTEST_REQUEST = "ir-lean.prooftest.request/1"
PROOFTEST_STORE = "ir-lean.prooftest.store/1"
PROOFTEST_BENCH = "ir-lean.prooftest.bench/1"
# tools/store/store.py: the lemma store's answers and index. docs/lemma-store.md.
STORE = "ir-lean.store/1"
STORE_LOOKUP = "ir-lean.store.lookup/1"
STORE_ADMISSION = "ir-lean.store.admission/1"
STORE_INDEX = "ir-lean.store.index/1"
# tests/passes.py: the scorer's instances, runs, score and self-check. docs/passes.md.
PASSES_INSTANCE = "ir-lean.passes.instance/1"
PASSES_RUN = "ir-lean.passes.run/1"
PASSES_SCORE = "ir-lean.passes.score/1"
PASSES_SELFCHECK = "ir-lean.passes.selfcheck/1"
# bench/instcombine/stage1.py: a pair, the summary, and the corpus of known miscompilations, from the stage-1
# benchmark lane, which isn't on main on 2026-11-09. Named here first, so its schemas are known when it lands.
STAGE1_PAIR = "ir-lean.stage1.pair/1"
STAGE1_SUMMARY = "ir-lean.stage1.summary/1"
STAGE1_KNOWN_WRONG = "ir-lean.stage1.known-wrong/1"
# tests/ir_features.py: everything the pinned IR can contain, each item modeled, refused or assumed (SEM-08).
# docs/ir-features.md.
IR_FEATURES = "ir-lean.ir-features/1"
# tools/x86_rank.py: how often clang -O3 leaves a call to each x86 intrinsic in real kernels.
# docs/x86-intrinsics.md.
X86_RANK = "ir-lean.x86-rank/1"
# tests/llvm_rewrites.py: the inventory of chunk 1's rewrites, one file per pass. docs/rewrite-inventory.md.
REWRITES = "ir-lean.rewrites/1"
# tests/peephole.py: a family's registry of folds, a model's comparison with opt, the scoreboard, and E3's
# measure. docs/rewrite-proofs.md.
PEEPHOLE_FOLDS = "ir-lean.peephole.folds/1"
PEEPHOLE_COMPARISON = "ir-lean.peephole.comparison/1"
PEEPHOLE_SCORE = "ir-lean.peephole.score/1"
PEEPHOLE_MEASURE = "ir-lean.peephole.measure/1"
# irl, the command line and MCP server, in Go: every command's contract, from `irl capabilities`. Go can't
# import this, so irl/schema_test.go checks irl names the same one. docs/irl.md.
IRL_CAPABILITIES = "ir-lean.irl.capabilities/1"
# tests/verify_negative.py: a case, the envelope around a checker's answer, and the report.
# docs/llvm-negative-verification.md.
NEGATIVE_CASE = "ir-lean.verification-negative.case/1"
NEGATIVE_ENVELOPE = "ir-lean.verification-negative.envelope/1"
NEGATIVE_REPORT = "ir-lean.verification-negative.report/1"
# bench/kernels: the kernel corpus's manifest, and what the emitter makes of its candidates' kernels.
# docs/kernels.md.
KERNELS_MANIFEST = "ir-lean.kernels.manifest/1"
KERNELS_DEMAND = "ir-lean.kernels.demand/1"
# bench/kernels/harness.py, the benchmark harness: a baseline's or a candidate's build and the checks it
# passed, a comparison's plan, written before it runs, one session's timed pairs, and the verdict the rule
# gives them, and a session's attempt, which holds its place before it runs and what it did if it failed.
# docs/kernels.md. A build of version 2 compares what each function refers to and the unit's data, and
# checks with the build's own arguments, so its record says more than version 1's did with the same fields:
# version 1, of the controls of 2026-11-10, is read for what it compared, and no win rests on it.
KERNELS_BUILD = "ir-lean.kernels.build/2"
KERNELS_BUILD_1 = "ir-lean.kernels.build/1"
KERNELS_PLAN = "ir-lean.kernels.plan/1"
KERNELS_SESSION = "ir-lean.kernels.session/1"
KERNELS_ATTEMPT = "ir-lean.kernels.attempt/1"
KERNELS_COMPARISON = "ir-lean.kernels.comparison/1"
# bench/kernels/board.py: an entry on the results board, a proved win or a rewrite that doesn't count, with
# its labels, proof and measurements. docs/board.md.
BOARD_WIN = "ir-lean.board.win/1"

ALL = {
    value: key
    for key, value in dict(globals()).items()
    if key.isupper() and isinstance(value, str) and NAME.fullmatch(value)
}


class SchemaError(ValueError):
    """A record that isn't one of the schema it was read as."""


def check(record: Any, schema: str) -> dict[str, Any]:
    """`record`, if it's a JSON object naming `schema`. Raises SchemaError otherwise."""
    if schema not in ALL:
        raise SchemaError(f"{schema} isn't a schema this repo knows")
    if not isinstance(record, dict):
        raise SchemaError(f"not a JSON object, so not {schema}")
    found = record.get("schema")
    if found != schema:
        raise SchemaError(f"schema {found!r}, not {schema}")
    return record


def loads(text: str | bytes, schema: str) -> dict[str, Any]:
    """A record of `schema` from JSON text. Raises SchemaError if it isn't JSON, or isn't one."""
    try:
        record = json.loads(text)
    # Bytes that aren't UTF-8 raise UnicodeDecodeError, which is a ValueError as JSONDecodeError is.
    except ValueError as error:
        raise SchemaError(f"not JSON, so not {schema}: {error}") from error
    return check(record, schema)


def read(path: str | os.PathLike[str], schema: str) -> dict[str, Any]:
    """A record of `schema` from a file. Raises SchemaError if it isn't one, and OSError if it can't be
    read."""
    return loads(Path(path).read_bytes(), schema)


def dumps(record: dict[str, Any], schema: str, **options: Any) -> str:
    """`record`, checked to be `schema`, as JSON. `options` are json.dumps's, so each writer keeps its own
    form."""
    return json.dumps(check(record, schema), **options)


def write(
    path: str | os.PathLike[str], record: dict[str, Any], schema: str, newline: bool = True, **options: Any
) -> None:
    """Writes `record`, checked to be `schema`, to `path` in one step: to a file beside it, then renamed over
    it, so a reader never sees half of one. `options` are json.dumps's, and a newline ends it unless `newline`
    is
    false."""
    text = dumps(record, schema, **options) + ("\n" if newline else "")
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Opened as any new file is, so the umask gives it the mode a plain write would.
    tmp = path.with_name(f".{path.name}.{os.getpid()}.{secrets.token_hex(4)}")
    try:
        with tmp.open("x") as f:
            f.write(text)
        os.replace(tmp, path)
    except BaseException:
        tmp.unlink(missing_ok=True)
        raise
