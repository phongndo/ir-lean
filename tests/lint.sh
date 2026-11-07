#!/usr/bin/env bash
# shellcheck disable=SC2329 # `check` calls these functions.
# Runs the formatters and linters for every language in the repo, and fails if any of them complain.
# Lean has no formatter, so `editorconfig-checker` is the only check on how its files are laid out.
# usage: tests/lint.sh [--fix]
# `--fix` first has the formatters rewrite what they can. It needs build/ to exist, with ir-lean built.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 1

# Tracked files and new ones, but not ignored ones.
files() { git ls-files --cached --others --exclude-standard "$@" | while read -r f; do [ -e "$f" ] && echo "$f"; done; }
mapfile -t cpp < <(files 'src/*.cpp' 'src/*.h')
mapfile -t c < <(files 'tests/real/*.c')
mapfile -t ll < <(files 'tests/real/*.ll')
mapfile -t shell < <(files '*.sh')
mapfile -t toml < <(files '*.toml')
mapfile -t yaml < <(files '*.yml' '*.yaml')
mapfile -t markdown < <(files '*.md')
mapfile -t nix < <(files '*.nix')

if [ "${1:-}" = --fix ]; then
  clang-format -i "${cpp[@]}" "${c[@]}"
  uv run --quiet ruff format
  shfmt -w -i 2 "${shell[@]}"
  nixfmt "${nix[@]}"
  gersemi -i --quiet CMakeLists.txt
  taplo fmt --no-auto-config "${toml[@]}" 2>/dev/null
  yamlfmt "${yaml[@]}"
  rumdl fmt --quiet "${markdown[@]}"
fi

# Every check runs at once, and each writes what it found to its own numbered file.
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
checks=0
check() {
  local name=$1
  shift
  checks=$((checks + 1))
  (
    if "$@" >"$out/$checks.log" 2>&1; then
      printf 'ok    %s\n' "$name"
    else
      printf 'FAIL  %s: %s\n' "$name" "$*"
      head -c 4000 "$out/$checks.log"
      : >"$out/failed"
    fi
  ) >"$out/$checks.result" &
}

check 'C and C++ format' clang-format --dry-run --Werror "${cpp[@]}" "${c[@]}"
# clang-tidy's analyzer takes seconds, so a pass is kept, named after everything it reads. CI doesn't keep
# build/result-cache, so it runs every time there.
tidy() {
  local key
  key=$({
    command -v clang-tidy
    printf '%s\n' "$1"
    cat .clang-tidy build/compile_commands.json "${cpp[@]}"
  } | sha256sum | cut -d' ' -f1)
  [ -e "build/result-cache/tidy-$key" ] && return
  clang-tidy -p build --quiet "$1" || return 1
  mkdir -p build/result-cache
  : >"build/result-cache/tidy-$key"
}
for f in "${cpp[@]}"; do
  check "C++ lint, $f" tidy "$f"
done
# clang warns about the linker flags Nix passes, which this command has no use for.
check 'C lint' clang -fsyntax-only -Wall -Wextra -Werror -Wno-unused-command-line-argument "${c[@]}"
verify_ir() {
  local f
  for f in "$@"; do
    opt -passes=verify -disable-output "$f" || return 1
  done
}
check 'LLVM IR is valid' verify_ir "${ll[@]}"

check 'Python lockfile' uv lock --check
check 'Python format' uv run --quiet ruff format --check
check 'Python lint' uv run --quiet ruff check
check 'Python types' uv run --quiet ty check

check 'Shell format' shfmt -d -i 2 "${shell[@]}"
check 'Shell lint' shellcheck "${shell[@]}"

check 'Nix format' nixfmt --check "${nix[@]}"
check 'Nix lint' statix check .
check 'Nix unused code' deadnix --fail "${nix[@]}"

check 'CMake format' gersemi --check --quiet CMakeLists.txt
check 'CMake lint' cmakelint --linelength=110 CMakeLists.txt

check 'TOML format' taplo fmt --check --no-auto-config "${toml[@]}"
check 'TOML lint' taplo lint --no-auto-config "${toml[@]}"

check 'YAML format' yamlfmt -lint "${yaml[@]}"
check 'GitHub Actions lint' actionlint

check 'Markdown format and lint' rumdl check "${markdown[@]}"

check 'Whitespace, in every language' editorconfig-checker -disable-indent-size

# The Lean lint needs the modules this writes.
check 'Lean generated modules' tests/proofs.sh build/ir-lean --generate build/generated
wait "$!"
check 'Lean lint' lake build --wfail IRLean Proofs

wait
for ((i = 1; i <= checks; i++)); do
  cat "$out/$i.result"
done
[ ! -e "$out/failed" ]
