"""Asks Alive2 whether functions refine each other, sharing one `alive-tv` process between many of them, as
starting it is most of what a small check costs. A function it can't say is right runs again on its own, so
what a caller reads about a failure or a timeout doesn't depend on what else was in the file. What it has
proved isn't asked again, for the same `alive-tv`.

`alive-tv` exits 0 whether it found the transformation correct or incorrect, and even when its solver times
out, so a verdict is read from its summary, not its exit code, and anything but a proof of every function or a
counterexample is unknown. A crash is the exception: a process a signal killed may have printed `correct` for
some functions before it died, which isn't clean evidence, so `run` reports that it died instead of returning
the partial output, as it does a timeout, and `verdict` reads it as unknown.

A source that's undefined on every input is refined by any target, so `alive-tv` counts it correct, with only
a warning. `--fail-src-ub` makes it a failure to prove instead, which `verdict` reads as unknown: a check that
proves nothing about the target mustn't pass as one that does."""

import concurrent.futures
import os
import re
import shutil
import tempfile

# tests/differential.py puts tools/ on the path, where the shared library is.
from differential import RESULTS
from irlean import hashing, proc

# Functions in one process. Enough that starting it stops mattering, and few enough that one slow function
# doesn't hold up many others.
CHUNK = 32
CORRECT = "Transformation seems to be correct!"
# How long one `alive-tv` process may take. Past this, what it would have said is unknown.
TIMEOUT_SECONDS = 300
# Inputs are values or poison, as IRLean's are. And a source that's undefined everywhere isn't a proof: the
# pinned alive-tv spells that `--fail-src-ub`.
FLAGS = ("--disable-undef-input", "--fail-src-ub")
# For a caller that asks each pair both ways round, as tests/vecopcheck.py does: where the model says an
# operation is undefined, the target is too, so a source undefined everywhere is what's checked, and where the
# model gives a value, the other direction fails if the operation is undefined.
BOTH_WAYS = ("--disable-undef-input",)
SUMMARY = re.compile(
    r"^\s*(\d+) (correct|incorrect|failed-to-prove) transformations$|^\s*(\d+) Alive2 errors$", re.M
)
PROVED = os.path.join(RESULTS, "alive-proved")
# Entries in that file before it starts again, which is many versions of everything.
PROVED_KEPT = 100000


def run(source, target, work, flags=FLAGS):
    """What `alive-tv` says about two files of the same functions. If it doesn't finish, that's said instead,
    with no summary, so `verdict` reads it as unknown."""
    with tempfile.TemporaryDirectory(dir=work) as d:
        a, b = os.path.join(d, "a.ll"), os.path.join(d, "b.ll")
        for path, text in ((a, source), (b, target)):
            with open(path, "w") as f:
                f.write(text)
        r = proc.run(["alive-tv", *flags, a, b], timeout=TIMEOUT_SECONDS)
    if r.limit is not None:
        return f"ERROR: alive-tv didn't finish in {TIMEOUT_SECONDS} s\n"
    if r.exit != 0:
        # alive-tv exits 0 for a complete run, whether it found the transformation correct or incorrect. Any
        # other exit -- a signal death, 255 for IR it can't read, a crash code like 134, or 1 for a function
        # it couldn't analyse -- means it didn't finish, so whatever it printed first isn't clean evidence:
        # none of it is returned, `proved` finds nothing, and each pair the chunk held is asked again alone.
        reason = f"signal {-r.exit}" if r.exit < 0 else f"exit {r.exit}"
        return f"ERROR: alive-tv ended abnormally ({reason})\n"
    return r.output


def summary(output):
    """The counts at the end of what `alive-tv` printed, or None if they aren't all there."""
    counts = {}
    for m in SUMMARY.finditer(output):
        if m.group(1) is not None:
            counts[m.group(2)] = int(m.group(1))
        else:
            counts["errors"] = int(m.group(3))
    return counts if len(counts) == 4 else None


def verdict(output, functions=1):
    """`correct` if `alive-tv` proved all of a file's `functions`, `incorrect` if it found one wrong, and
    otherwise `unknown`: a timeout, a failure to prove, an error of its own, or output that isn't what it
    prints. `None` is how `refinements` says it proved a pair."""
    if output is None:
        return "correct"
    counts = summary(output)
    if counts is None:
        return "unknown"
    if counts["incorrect"]:
        return "incorrect"
    if counts["correct"] == functions and not counts["failed-to-prove"] and not counts["errors"]:
        return "correct"
    return "unknown"


def proved(output):
    """The numbers of the functions `alive-tv` says are right. It prints each one's result after a line of
    dashes, and the source function comes first."""
    found = set()
    for part in output.split("-" * 40 + "\n")[1:]:
        name = re.search(r"^define .*?@f(\d+)\(", part, flags=re.M)
        if name and CORRECT in part:
            found.add(int(name.group(1)))
    return found


def named(function, n):
    return function.replace("@F(", f"@f{n}(")


def check_chunk(job):
    declarations, pairs, work, flags = job
    source = declarations + "".join(named(s, n) for n, (s, _) in enumerate(pairs))
    target = declarations + "".join(named(t, n) for n, (_, t) in enumerate(pairs))
    found = proved(run(source, target, work, flags))
    return [
        None if n in found else run(declarations + s, declarations + t, work, flags)
        for n, (s, t) in enumerate(pairs)
    ]


def refinements(declarations, pairs, work, flags=FLAGS):
    """For each (source, target) pair of functions named @F, None if the source is proved to refine the
    target, and otherwise what `alive-tv` says with that pair alone."""
    tool = os.path.realpath(shutil.which("alive-tv") or "alive-tv")
    # The flags are in the key, so what was proved under other flags is asked again.
    keys = [hashing.sha256_text(f"{tool}\0{' '.join(flags)}\0{declarations}\0{s}\0{t}") for s, t in pairs]
    try:
        with open(PROVED) as f:
            known = set(f.read().split())
    except OSError:
        known = set()
    asked = [n for n, key in enumerate(keys) if key not in known]
    chunks = [asked[i : i + CHUNK] for i in range(0, len(asked), CHUNK)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        results = pool.map(
            check_chunk, [(declarations, [pairs[n] for n in chunk], work, flags) for chunk in chunks]
        )
        outputs = [None] * len(pairs)
        for chunk, result in zip(chunks, results, strict=True):
            for n, output in zip(chunk, result, strict=True):
                outputs[n] = output
    remember([keys[n] for n in asked if outputs[n] is None], len(known))
    return outputs


def remember(proved, known):
    """Adds to the file of what's proved, all in one write so that tests running at once don't mix lines."""
    if not proved:
        return
    os.makedirs(RESULTS, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND | (os.O_TRUNC if known > PROVED_KEPT else 0)
    fd = os.open(PROVED, flags, 0o644)
    try:
        os.write(fd, "".join(key + "\n" for key in proved).encode())
    finally:
        os.close(fd)
