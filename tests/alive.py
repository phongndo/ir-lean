"""Asks Alive2 whether functions refine each other, sharing one `alive-tv` process between many of them, as
starting it is most of what a small check costs. A function it can't say is right runs again on its own, so
what a caller reads about a failure or a timeout doesn't depend on what else was in the file."""

import concurrent.futures
import os
import re
import subprocess
import tempfile

# Functions in one process. Enough that starting it stops mattering, and few enough that one slow function
# doesn't hold up many others.
CHUNK = 32
CORRECT = "Transformation seems to be correct!"


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
    chunks = [pairs[i : i + CHUNK] for i in range(0, len(pairs), CHUNK)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as pool:
        results = pool.map(check_chunk, [(declarations, chunk, work) for chunk in chunks])
    return [r for chunk in results for r in chunk]
