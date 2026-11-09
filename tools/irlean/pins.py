"""The toolchain the repo pins, and what's on PATH: each binary by path, SHA-256 and version.

The pins are in three files:

- tests/llvm/targets.toml's `[project]`: the llvm-project repository, tag, commit and Nix hash that LLVM's
  `opt`, `clang` and `llc` are built from, and that tests/llvm.py proves things about.
- lean-toolchain: the Lean toolchain elan runs.
- nix/shell.nix: the Alive2 commit `alive-tv` is built from, on the pinned LLVM.

A pin says which version a tool has to be. `tool` says which binary is on PATH, by its resolved path and hash,
which is what a result records so a reader can tell two toolchains apart. Nix's derivation is trusted for a
binary coming from its pinned source: hashing it shows it's the same file, not where it came from.
"""

from __future__ import annotations

import re
import shutil
import tomllib
from dataclasses import dataclass
from functools import cache
from pathlib import Path

from . import ROOT, hashing, proc

LLVM_PIN = ROOT / "tests" / "llvm" / "targets.toml"
LEAN_PIN = ROOT / "lean-toolchain"
ALIVE2_PIN = ROOT / "nix" / "shell.nix"
LLVM_VERSION = re.compile(r"LLVM version (\S+)")


@cache
def llvm() -> dict[str, str]:
    """The llvm-project this repo pins: its repository, tag, commit and nix_hash."""
    project = tomllib.loads(LLVM_PIN.read_text())["project"]
    return {k: project[k] for k in ("repository", "tag", "commit", "nix_hash")}


def llvm_version() -> str:
    """The LLVM version the pin's tag names, such as 23.1.3."""
    return llvm()["tag"].removeprefix("llvmorg-")


def lean() -> str:
    """The Lean toolchain lean-toolchain pins."""
    return LEAN_PIN.read_text().strip()


@cache
def alive2() -> dict[str, str]:
    """The Alive2 commit nix/shell.nix builds `alive-tv` from, and its source's hash."""
    text = ALIVE2_PIN.read_text()
    block = text[text.index('repo = "alive2"') :]
    rev = re.search(r'rev = "([0-9a-f]{40})"', block)
    nix_hash = re.search(r'hash = "(sha256-[^"]+)"', block)
    if rev is None or nix_hash is None:
        raise ValueError(f"{ALIVE2_PIN} doesn't name Alive2's commit and hash")
    return {"repository": "https://github.com/AliveToolkit/alive2", "rev": rev[1], "nix_hash": nix_hash[1]}


def which(program: str) -> Path | None:
    """Where `program` is on PATH, with every link resolved, or None."""
    found = shutil.which(program)
    return Path(found).resolve() if found else None


@dataclass(frozen=True)
class Tool:
    """A binary on PATH: its resolved path, SHA-256, and what `--version` printed."""

    name: str
    path: Path
    sha256: str
    version: str

    @property
    def llvm_version(self) -> str | None:
        """The LLVM version it says it is, for LLVM's tools and Alive2, or None."""
        m = LLVM_VERSION.search(self.version)
        return m[1] if m else None

    def matches_llvm_pin(self) -> bool:
        return self.llvm_version == llvm_version()


def tool(program: str, timeout: float = 60) -> Tool | None:
    """`program` on PATH, hashed, with its version, or None if it isn't there."""
    path = which(program)
    if path is None:
        return None
    r = proc.run([path, "--version"], timeout=timeout)
    return Tool(program, path, hashing.sha256_file(path), r.output.strip() if r.ok else "")
