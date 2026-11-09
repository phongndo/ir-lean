#!/usr/bin/env python3
"""Checks .github/needs-tests.py, which lets a pull request skip CI's test jobs when it only adds or edits
documents no test reads.

In a scratch git repo, each change has to get the answer given. Then, in this repo, each document a test
is known to read has to have a reader, so a change to it runs the tests, and the scripts the rule leaves out
as the lint job's have to be exactly what the tests labeled `lint` run. About a second, and only git.

usage: tests/needs_tests_test.py BUILD_DIR
"""

import importlib.util
import json
import os
import sys
import tempfile
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import proc  # noqa: E402

SCRIPT = ROOT / ".github" / "needs-tests.py"
# Documents tests read, and what reads each.
KNOWN_READERS = {
    "docs/llvm-verification-tasks.md": "tests/llvm_scope.py",
    "docs/llvm-cpp-correspondence.md": "tests/cpp_correspondence.py",
    "docs/verify.md": "tests/verify.py",
    "docs/chunks.md": "tests/chunks_test.py",
}

# The scratch repo's first commit.
BASE = {
    "README.md": "# A repo\n",
    "docs/free.md": "Nothing reads this.\n",
    "docs/read.md": "A test reads this.\n",
    "docs/cited.md": "A test's data names this.\n",
    "docs/linted.md": "Only the lint job names this.\n",
    "docs/index.md": "See free.md and read.md.\n",
    "tests/t.py": 'open("docs/read.md").read()\n',
    "tests/data.json": '{"evidence": "DOCS/CITED.MD"}\n',
    "tests/lint.sh": "rumdl check docs/linted.md\n",
}
# Each change from BASE, as files to write (None removes one), and whether it needs the tests.
CASES: list[tuple[str, dict[str, str | None], bool]] = [
    ("edits a document nothing names", {"README.md": "# Edited\n"}, False),
    ("adds a document", {"docs/new.md": "New.\n"}, False),
    ("edits two documents nothing reads", {"docs/free.md": "Edited.\n", "README.md": "# Edited\n"}, False),
    ("edits a document only another document names", {"docs/free.md": "Edited.\n"}, False),
    ("edits a document only the lint job's script names", {"docs/linted.md": "Edited.\n"}, False),
    ("edits a document a test names", {"docs/read.md": "Edited.\n"}, True),
    ("edits a document test data names in another case", {"docs/cited.md": "Edited.\n"}, True),
    (
        "edits one document nothing reads and one a test reads",
        {"docs/free.md": "x\n", "docs/read.md": "y\n"},
        True,
    ),
    ("removes a document", {"docs/free.md": None}, True),
    ("renames a document", {"docs/free.md": None, "docs/moved.md": BASE["docs/free.md"]}, True),
    ("edits a test", {"tests/t.py": "pass\n"}, True),
    ("edits a document and a test", {"docs/free.md": "Edited.\n", "tests/t.py": "pass\n"}, True),
    ("edits the lint job's script", {"tests/lint.sh": "true\n"}, True),
    ("adds a file that isn't Markdown", {"docs/figure.svg": "<svg/>\n"}, True),
    ("changes nothing", {}, True),
]


def load_script() -> Any:
    spec = importlib.util.spec_from_file_location("needs_tests", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def checked(argv: list[str], **kw: Any) -> str:
    """What `argv` prints. Raises RuntimeError if it fails."""
    r = proc.run(argv, **kw)
    if r.exit != 0:
        raise RuntimeError(f"{' '.join(argv)} exited with {r.exit}: {r.err}")
    return r.out


def git(repo: Path, *args: str) -> str:
    env = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t"}
    env["GIT_COMMITTER_EMAIL"] = "t@t"
    return checked(["git", "-C", str(repo), *args], env=env).strip()


def write(repo: Path, files: Mapping[str, str | None]) -> None:
    for path, content in files.items():
        if content is None:
            (repo / path).unlink()
        else:
            (repo / path).parent.mkdir(parents=True, exist_ok=True)
            (repo / path).write_text(content)


def scratch(failures: list[str]) -> int:
    with tempfile.TemporaryDirectory() as d:
        repo = Path(d)
        git(repo, "init", "--quiet", "--initial-branch=main")
        write(repo, BASE)
        git(repo, "add", "-A")
        git(repo, "commit", "--quiet", "-m", "base")
        base = git(repo, "rev-parse", "HEAD")
        for name, files, expected in CASES:
            git(repo, "checkout", "--quiet", "--detach", base)
            write(repo, files)
            git(repo, "add", "-A")
            git(repo, "commit", "--quiet", "--allow-empty", "-m", name)
            r = proc.run([sys.executable, str(SCRIPT), base, "HEAD"], cwd=repo)
            want = f"tests={'true' if expected else 'false'}"
            if r.exit != 0 or r.out.strip() != want:
                failures.append(f"{name}: expected {want}, got {r.out.strip()!r}, exit {r.exit}: {r.err}")
            else:
                print(f"ok    {name}: {want}. {r.err.strip()}")
    return len(CASES)


def this_repo(build: Path, failures: list[str]) -> int:
    script = load_script()
    os.chdir(ROOT)
    for doc, reader in KNOWN_READERS.items():
        found = script.readers(Path(doc).name, "HEAD")
        if reader not in found:
            failures.append(f"{doc}: {reader} reads it, and the rule finds only {found}")
        else:
            print(f"ok    {doc}: a change to it runs the tests, as {reader} reads it")
    shown = checked(["ctest", "--test-dir", str(build), "--show-only=json-v1", "-L", "^lint$"])
    commands = {str(Path(t["command"][0]).relative_to(ROOT)) for t in json.loads(shown)["tests"]}
    if commands != set(script.LINT):
        failures.append(
            f"the tests labeled lint run {sorted(commands)}, and the rule leaves out {script.LINT}"
        )
    else:
        print(
            f"ok    lint: the scripts left out, {', '.join(script.LINT)}, are what the tests labeled lint run"
        )
    return len(KNOWN_READERS) + 1


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit(__doc__.rsplit("usage: ", 1)[1].strip())
    failures: list[str] = []
    ran = scratch(failures) + this_repo(Path(sys.argv[1]), failures)
    for f in failures:
        print(f"FAIL  {f}")
    print(f"{ran - len(failures)}/{ran} cases behave")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
