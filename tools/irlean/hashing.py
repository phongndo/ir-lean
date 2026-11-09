"""SHA-256 of bytes, text, files and trees, the one way the repo hashes anything.

Files are read a piece at a time, so a large one isn't held in memory whole, and a tree's files are hashed on
several threads at once. Hashes establish identity, not correctness: two files hashing the same are the same
bytes, whatever they mean. docs/llvm-proof-binding.md says what tools/binding.py rests on them for, and
`tree_hash` keeps the rules it gives: every entry read back one way, and no link leading to anything unhashed.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

# Threads hashing a tree's files at once. Reading a file and hashing it both let other threads run.
THREADS = min(8, os.cpu_count() or 1)
NIX_STORE = "/nix/store"


def new(data: bytes = b"") -> Any:
    """A SHA-256 to update a piece at a time, for a hash of several things."""
    return hashlib.sha256(data)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    """The SHA-256 of `text` as UTF-8."""
    return hashlib.sha256(text.encode()).hexdigest()


def sha256_file(path: str | os.PathLike[str]) -> str:
    """A file's SHA-256, read a piece at a time."""
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def sha256_parts(*parts: str | bytes) -> str:
    """The SHA-256 of each part followed by a NUL. A part with a NUL in it can make two lists of parts hash
    the
    same, so this is for parts that can't hold one, such as text."""
    h = hashlib.sha256()
    for p in parts:
        h.update(p if isinstance(p, bytes) else p.encode())
        h.update(b"\0")
    return h.hexdigest()


def canonical(obj: Any) -> bytes:
    """`obj` as JSON in one fixed form, to hash or compare: sorted keys, no spaces, UTF-8."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def walk(*roots: Path) -> list[Path]:
    """Every file, directory and link under `roots`, or `roots` themselves if they're files, without following
    links, in a fixed order."""
    out = []
    for root in roots:
        if not root.is_dir() or root.is_symlink():
            out.append(root)
            continue
        for d, subdirs, files in os.walk(root):
            out += [Path(d) / name for name in subdirs + files]
    return sorted(out)


def kind(path: Path) -> bytes:
    """What `path` is, without following a link."""
    mode = path.lstat().st_mode
    for test, name in ((stat.S_ISLNK, b"link"), (stat.S_ISREG, b"file"), (stat.S_ISDIR, b"dir")):
        if test(mode):
            return name
    return b"other"


class UntrustedLink(ValueError):
    """A link in a tree leads somewhere `tree_hash` doesn't hash."""

    def __init__(self, path: Path, target: str) -> None:
        super().__init__(f"{path} leads to {target}, which isn't checked")
        self.path, self.target = path, target


def sha256_files(paths: list[Path], threads: int = THREADS) -> dict[Path, str]:
    """Each file's SHA-256, on `threads` threads, each a piece at a time."""
    with ThreadPoolExecutor(threads) as pool:
        return dict(zip(paths, pool.map(sha256_file, paths), strict=True))


def tree_hash(base: Path, *roots: Path) -> str:
    """Every file under `roots` by its path from `base` and its bytes, and every link by its target. A link
    has to lead inside `roots`, whose files are hashed themselves, or into the Nix store, which is read-only.
    One leading anywhere else could reach a file nothing hashes, so it raises UntrustedLink. So a link has to
    be a bare file name, naming a sibling that's hashed itself and isn't a directory, or an absolute path into
    the store that stays there. Nothing is normalized: `..`, a root that's a link, and a link to a directory
    could each lead through something only tracked as a link, and what it leads to could change unseen.

    Each entry goes in as its path, a NUL, its kind and a NUL, and then a file's SHA-256, 32 bytes, or a
    link's target and a NUL. A path or a target can't hold a NUL, so the bytes read back one way, and no two
    trees give the same ones: a file can't pass for two, or a directory for an empty file. Files are hashed on
    THREADS
    threads, each a piece at a time."""
    entries = walk(*roots)
    tracked = {str(p) for p in entries}
    kinds = {path: kind(path) for path in entries}
    contents = sha256_files([p for p in entries if kinds[p] == b"file"])
    digest = hashlib.sha256()
    for path in entries:
        digest.update(os.fsencode(path.relative_to(base)) + b"\0" + kinds[path] + b"\0")
        if kinds[path] == b"link":
            raw = os.readlink(path)
            sibling = "/" not in raw and raw not in (".", "..") and str(path.parent / raw) in tracked
            store = raw.startswith(NIX_STORE + "/") and Path(raw).resolve().is_relative_to(NIX_STORE)
            if path in roots or path.is_dir() or not (sibling or store):
                raise UntrustedLink(path, raw)
            digest.update(os.fsencode(raw) + b"\0")
        elif kinds[path] == b"file":
            digest.update(bytes.fromhex(contents[path]))
    return digest.hexdigest()


def files_hash(base: Path, paths: list[Path]) -> str:
    """Files by their paths from `base`, sorted, each as its path, a NUL and its SHA-256, which reads back one
    way: a path can't hold a NUL, and a hash is 32 bytes."""
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(os.fsencode(path.relative_to(base)) + b"\0" + bytes.fromhex(sha256_file(path)))
    return digest.hexdigest()


def stamp(*roots: Path) -> dict[str, tuple[int, ...]]:
    """What `lstat` says of every entry under `roots`. Any write, replacement, new file or removal changes it:
    a write moves the change time, which a process without root can't set back. It checks that nothing changed
    while untrusted code could run, as hashing it all again each time would take seconds."""
    out = {}
    for path in walk(*roots):
        st = path.lstat()
        out[str(path)] = (st.st_mode, st.st_ino, st.st_size, st.st_ctime_ns, st.st_mtime_ns)
    return out


def snapshot(*dirs: Path) -> dict[str, str]:
    """Every entry under `dirs`, without following links: a file by its hash, a link by its target."""
    out = {}
    for d in dirs:
        for root, subdirs, files in os.walk(d):
            for name in subdirs + files:
                p = Path(root) / name
                out[str(p)] = (
                    f"link {os.readlink(p)}" if p.is_symlink() else "dir" if p.is_dir() else sha256_file(p)
                )
    return out
