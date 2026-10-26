#!/bin/sh
# Runs every algorithm `Examples/RunnableFloat.lean` instantiates, through
# `Examples/RunCheck.lean`, and compares what it prints with what is committed.
# `RunnableFloat.lean` only proves each algorithm *compiles* at a float scalar;
# this is the check that it *runs*, to a result with no NaN and no missing
# value, and that the result does not silently change.
#
# Two parts.
#   1. Coverage, textual and needing no build: every `def` of RunnableFloat.lean
#      must be run in RunCheck.lean (as `RunnableFloat.<name>` on a line that is
#      not a comment) or listed in its `skipped` table (a `("<name>", "<reason>")`
#      line). A new runnable algorithm cannot escape execution.
#   2. The run, through the interpreter for the reason `check-demo.sh` is:
#      linking an executable against Mathlib takes tens of minutes. `lake exe
#      runcheck` is the same `main`, for a human with the time. The exit code is
#      nonzero if a row is not `ok`; the diff then names the row.
#
# Needs a built tree for part 2. `sh scripts/check-runcheck.sh coverage` runs
# part 1 only.

set -eu

cd "$(dirname "$0")/.."

runnable=src/CORALean/Examples/RunnableFloat.lean
runcheck=src/CORALean/Examples/RunCheck.lean
expected=scripts/expected/runcheck-expected.txt

missing=0
for name in $(sed -n 's/^def \([^ ]*\).*/\1/p' "$runnable"); do
  # `[^A-Za-z0-9_'₀-₉.]` after the name: `Z` is not `Z_plus`, and `RunnableFloat.d`
  # is not `RunnableFloat.d.foo`; a following `.` is a projection, so allowed.
  if grep -v '^[[:space:]]*--' "$runcheck" |
       grep -Eq "RunnableFloat\.$name([^A-Za-z0-9_'₀-₉]|\$)" ||
     grep -Eq "^[[:space:]]*\(\"$name\"," "$runcheck"; then
    :
  else
    printf 'runcheck: RunnableFloat.%s is neither run nor skipped in %s\n' "$name" "$runcheck"
    missing=1
  fi
done
if [ "$missing" -ne 0 ]; then
  exit 1
fi
printf 'runcheck: every def of %s is run or skipped\n' "$runnable"

if [ "${1:-}" = coverage ]; then
  exit 0
fi

raw=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$raw" "$actual"' EXIT INT TERM

status=0
lake env lean --run "$runcheck" > "$raw" || status=$?
tr -d '\r' < "$raw" > "$actual"

if diff -u "$expected" "$actual"; then
  printf 'runcheck: output matches %s\n' "$expected"
else
  printf 'runcheck: output differs from %s - a result changed\n' "$expected"
  exit 1
fi
if [ "$status" -ne 0 ]; then
  printf 'runcheck: a row is not ok (see the status column)\n'
  exit 1
fi
