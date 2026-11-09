#!/usr/bin/env python3
"""Says whether a change needs CI's test jobs, as `tests=true` or `tests=false` for $GITHUB_OUTPUT, and why on
stderr.

It doesn't only when every file it changes is Markdown it adds or edits, and no file in the repo that isn't
Markdown names that file, ignoring case. A test reads a document by naming it, as tests/llvm_scope.py does
docs/llvm-verification-tasks.md and tests/llvm_scope/coverage.json does its evidence, so a document no file
outside Markdown names isn't read by any test. A name in a comment counts too, which is conservative.
Removing or renaming a file always needs the tests, since a test can check that a file it was told about
exists. The lint job's tests, which check every Markdown file, run on every pull request, so what their
scripts name doesn't count.

This reads only file names and git: it doesn't know what a test reads in any other way, such as every document
by a pattern. A test that does that has to be added to the rule here.

usage: .github/needs-tests.py BASE HEAD
"""

import subprocess
import sys

# What the tests labeled `lint` in CMakeLists.txt run. The lint job runs them whatever this says.
LINT = ("tests/lint.sh", "tests/lsp.py")


def git(*args: str, found: bool = False) -> str:
    """What git prints. With `found`, exit code 1 means nothing was found, not an error, as for `git grep`."""
    r = subprocess.run(["git", *args], capture_output=True, text=True, check=False)
    if r.returncode != 0 and not (found and r.returncode == 1 and not r.stderr):
        sys.exit(f"git {' '.join(args)} failed with exit code {r.returncode}: {r.stderr}")
    return r.stdout


def readers(name: str, head: str) -> list[str]:
    """The files at `head` that name `name`, ignoring case, apart from Markdown and the lint job's scripts."""
    others = [":(exclude)*.md", *(f":(exclude){f}" for f in LINT)]
    found = git("grep", "-l", "-z", "-i", "-F", "-e", name, head, "--", *others, found=True)
    # Each is printed as HEAD:PATH.
    return [f.split(":", 1)[1] for f in found.split("\0")[:-1]]


def needs_tests(base: str, head: str) -> tuple[bool, str]:
    """Whether the change from `base` to `head` needs the tests, and why."""
    fields = git("diff", "--name-status", "--no-renames", "-z", base, head).split("\0")[:-1]
    changes = list(zip(fields[::2], fields[1::2], strict=True))
    if not changes:
        return True, "it changes no file, so nothing says what it needs"
    for status, path in changes:
        if not path.lower().endswith(".md"):
            return True, f"it changes {path}, which isn't Markdown"
        if status not in ("A", "M"):
            return True, f"it removes, renames or retypes {path} ({status})"
    for _, path in changes:
        name = path.rsplit("/", 1)[-1]
        if found := readers(name, head):
            return True, f"{name} is named in {', '.join(found)}, so a test may read it"
    return False, "it only adds or edits Markdown that no file but Markdown names: " + ", ".join(
        p for _, p in changes
    )


def main() -> int:
    if len(sys.argv) != 3:
        sys.exit(__doc__.rsplit("usage: ", 1)[1].strip())
    needed, why = needs_tests(sys.argv[1], sys.argv[2])
    print(f"The tests {'run' if needed else 'are skipped'}: {why}", file=sys.stderr)
    print(f"tests={'true' if needed else 'false'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
