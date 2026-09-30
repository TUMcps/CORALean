#!/bin/sh
# Runs the oracle on requests.jsonl and diffs its output against expected.jsonl,
# then checks the ok responses against check_sound.py's independent, exact-
# rational soundness check. `lake exe oracle` by default; override with
# ORACLE="cmd", e.g. the interpreter:
#   ORACLE="lake env lean --run src/CORALean/Examples/Oracle.lean" \
#     sh experiments/oracle/selftest.sh

set -eu

cd "$(dirname "$0")/../.."

ORACLE="${ORACLE:-.lake/build/bin/oracle}"
REQ=experiments/oracle/requests.jsonl
EXPECTED=experiments/oracle/expected.jsonl
actual=$(mktemp)
expected_norm=$(mktemp)
actual_norm=$(mktemp)
trap 'rm -f "$actual" "$expected_norm" "$actual_norm"' EXIT INT TERM

# shellcheck disable=SC2086 -- ORACLE may be a multi-word command (the interpreter backend)
$ORACLE < "$REQ" > "$actual"

# `ping`'s "version" is the current git commit, which a fixture committed at one commit cannot
# pin against a later one; normalised out of both sides before the diff, so the self-test
# checks everything `ping` reports except that one always-moving field.
norm() { sed -E 's/"version":"[0-9a-fA-F]+"/"version":"GITREV"/' "$1"; }
norm "$EXPECTED" > "$expected_norm"
norm "$actual" > "$actual_norm"

if diff -u "$expected_norm" "$actual_norm"; then
  printf 'selftest: output matches %s (version field normalised)\n' "$EXPECTED"
else
  printf 'selftest: output differs from %s\n' "$EXPECTED"
  exit 1
fi

# Required, not optional: a missing `python3` fails the self-test loudly rather than the
# diff above silently standing in for the soundness check it never ran.
if ! command -v python3 >/dev/null 2>&1; then
  printf 'selftest: python3 not found -- cannot run check_sound.py\n' >&2
  exit 1
fi
python3 experiments/oracle/check_sound.py "$REQ" "$actual"
