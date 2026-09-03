#!/bin/sh
# Runs the demo and compares what it prints with what is committed, so an
# enclosure that silently widens fails the build instead of passing it. A
# soundness theorem cannot notice that: `_outer` is as true of a box the size of
# the state space as of a tight one.
#
# Through the interpreter rather than `lake exe demo`. An executable has to
# link, and linking against Mathlib means compiling the C it emitted for every
# module the demo reaches — tens of minutes, against under a second here. It is
# the same `main` over the same oleans; `lake exe demo` is for a human with the
# time.
#
# Needs a built tree, so this is not the pre-commit hook's business the way
# `check-conventions.sh` is.

set -eu

cd "$(dirname "$0")/.."

expected=scripts/demo-expected.txt
raw=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$raw" "$actual"' EXIT INT TERM

lake env lean --run src/Demo.lean > "$raw"
# On Windows the runtime writes CRLF and the committed file is LF, which would
# otherwise make every line differ.
tr -d '\r' < "$raw" > "$actual"

if diff -u "$expected" "$actual"; then
  printf 'demo: output matches %s\n' "$expected"
else
  printf 'demo: output differs from %s — an enclosure changed\n' "$expected"
  exit 1
fi
