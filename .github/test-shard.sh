#!/usr/bin/env bash
# Runs the tests for one of CI's test jobs. A job named after a ctest label runs the tests with that label.
# `rest` runs every test without one of LABELS, the other test jobs' names, that the `lint` and `slow` jobs
# don't run, so a test with no label still runs. First it checks CI runs each test exactly once.
# usage: .github/test-shard.sh LABEL
#        .github/test-shard.sh rest LABEL...
set -euo pipefail
cd "$(dirname "$0")/.."

job=$1
shift
labels=("$@")
alternatives=$(IFS='|' && echo "${labels[*]}")

# The ctest arguments that pick a job's tests, one to a line. `lint` and `slow` are as ci.yml's jobs pick them.
select_tests() {
  case $1 in
  lint | slow) printf '%s\n' -L "$1" ;;
  rest) printf '%s\n' -LE "lint|slow|^($alternatives)\$" ;;
  *) printf '%s\n' -L "^$1\$" ;;
  esac
}

tests() { ctest --test-dir build --show-only "$@" | sed -n 's/^ *Test *#[0-9]*: //p'; }

if [ "$job" = rest ]; then
  if [ ${#labels[@]} -eq 0 ]; then
    echo "usage: $0 rest LABEL..." >&2
    exit 2
  fi
  picked=$(for other in lint slow "${labels[@]}" rest; do
    mapfile -t selection < <(select_tests "$other")
    tests "${selection[@]}"
  done)
  wrong=0
  while read -r test; do
    count=$(grep -cxF -- "$test" <<<"$picked" || true)
    if [ "$count" -ne 1 ]; then
      echo "FAIL  CI runs $test in $count jobs, not 1. Give it one of these labels, or none: ${labels[*]}"
      wrong=1
    fi
  done < <(tests)
  [ "$wrong" -eq 0 ] || exit 1
fi

mapfile -t selection < <(select_tests "$job")
exec ctest --test-dir build --no-tests=error --output-on-failure "${selection[@]}"
