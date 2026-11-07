"""Asks Alive2 whether functions refine each other, sharing one `alive-tv` process between many of them, as
starting it is most of what a small check costs. A function it can't say is right runs again on its own, so
what a caller reads about a failure or a timeout doesn't depend on what else was in the file. What it has
proved isn't asked again, for the same `alive-tv`."""

import concurrent.futures
import hashlib
import os
import re
import shutil
import subprocess
import tempfile

from differential import RESULTS

# Functions in one process. Enough that starting it stops mattering, and few enough that one slow function
# doesn't hold up many others.
CHUNK = 32
CORRECT = "Transformation seems to be correct!"
PROVED = os.path.join(RESULTS, "alive-proved")
# Entries in that file before it starts again, which is many versions of everything.
PROVED_KEPT = 100000


def run(source, target, work):
    """What `alive-tv` says about two files of the same functions."""
    with tempfile.TemporaryDirectory(dir=work) as d:
        a, b = os.path.join(d, "a.ll"), os.path.join(d, "b.ll")
        for path, text in ((a, source), (b, target)):
            with open(path, "w") as f:
                f.write(text)
        r = subprocess.run(
            ["alive-tv", "--disable-undef-input", a, b],
            text=True,
            capture_output=True,
            timeout=300,
            check=False,
        )
    return r.stdout + r.stderr


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
    declarations, pairs, work = job
    source = declarations + "".join(named(s, n) for n, (s, _) in enumerate(pairs))
    target = declarations + "".join(named(t, n) for n, (_, t) in enumerate(pairs))
    try:
        found = proved(run(source, target, work))
    except subprocess.TimeoutExpired:
        found = set()
    return [
        None if n in found else run(declarations + s, declarations + t, work)
        for n, (s, t) in enumerate(pairs)
    ]


def refinements(declarations, pairs, work):
    """For each (source, target) pair of functions named @F, None if the source is proved to refine the
    target, and otherwise what `alive-tv` says with that pair alone."""
    tool = os.path.realpath(shutil.which("alive-tv") or "alive-tv")
    keys = [hashlib.sha256(f"{tool}\0{declarations}\0{s}\0{t}".encode()).hexdigest() for s, t in pairs]
    try:
        with open(PROVED) as f:
            known = set(f.read().split())
    except OSError:
        known = set()
    asked = [n for n, key in enumerate(keys) if key not in known]
    chunks = [asked[i : i + CHUNK] for i in range(0, len(asked), CHUNK)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        results = pool.map(check_chunk, [(declarations, [pairs[n] for n in chunk], work) for chunk in chunks])
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
