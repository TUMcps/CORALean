#!/bin/sh
# The shell steps of `.gitlab-ci.yml`'s `release-oracle-build` job, in a script so they run
# locally: builds `oracle` and `oracle-unsound`, runs both self-tests against the LINKED
# binaries (not the interpreter: the release ships what lake links), copies them to
# `$OUT/oracle-linux-x86_64` and `$OUT/oracle-unsound-linux-x86_64`, writes their `.sha256`
# files, and writes `$OUT/release-description.md` with `ldd` and the minimum glibc they need.
# Then, unless DRY_RUN is set, uploads all four files to the project's Generic Package
# Registry as `oracle/$CI_COMMIT_TAG`, which needs CI_JOB_TOKEN, CI_API_V4_URL, CI_PROJECT_ID.
#
#   DRY_RUN=1 OUT=/some/scratch sh scripts/build/release-oracle.sh
#
# Linux only: `ldd` and `objdump -T` read ELF. OUT defaults to `release/`.

set -eu

cd "$(dirname "$0")/../.."

OUT="${OUT:-release}"
TAG="${CI_COMMIT_TAG:-untagged}"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

lake build oracle oracle-unsound

sh experiments/oracle/selftest.sh
UNSOUND=1 ORACLE=.lake/build/bin/oracle-unsound \
  REQ=experiments/oracle/requests-unsound.jsonl \
  EXPECTED=experiments/oracle/expected-unsound.jsonl sh experiments/oracle/selftest.sh

cp .lake/build/bin/oracle "$OUT/oracle-linux-x86_64"
cp .lake/build/bin/oracle-unsound "$OUT/oracle-unsound-linux-x86_64"
(
  cd "$OUT"
  for f in oracle-linux-x86_64 oracle-unsound-linux-x86_64; do
    sha256sum "$f" > "$f.sha256"
    sha256sum -c "$f.sha256"
  done
)

# The newest GLIBC_x.y symbol version a binary references is the oldest glibc it runs on.
glibc_min() {
  objdump -T "$1" | grep -o 'GLIBC_[0-9][0-9.]*' | sort -uV | tail -1
}

{
  printf 'CORALean %s: the JSON-lines `oracle` and `oracle-unsound`, Linux x86_64.\n\n' "$TAG"
  printf 'Source commit `%s`. Verify with `sha256sum -c <name>.sha256`.\n' "$(git rev-parse --short HEAD)"
  for f in oracle-linux-x86_64 oracle-unsound-linux-x86_64; do
    printf '\n### `%s`\n\n' "$f"
    printf 'sha256 `%s`, %s bytes. Minimum glibc: `%s`.\n\n' \
      "$(cut -d' ' -f1 "$OUT/$f.sha256")" "$(wc -c < "$OUT/$f" | tr -d ' ')" "$(glibc_min "$OUT/$f")"
    printf '```\n%s\n```\n' "$(ldd "$OUT/$f")"
  done
} > "$OUT/release-description.md"
cat "$OUT/release-description.md"

if [ -n "${DRY_RUN:-}" ]; then
  printf 'release-oracle: DRY_RUN, not uploading\n'
  exit 0
fi

base="$CI_API_V4_URL/projects/$CI_PROJECT_ID/packages/generic/oracle/$TAG"
for f in oracle-linux-x86_64 oracle-unsound-linux-x86_64; do
  for g in "$f" "$f.sha256"; do
    curl --fail --silent --show-error --header "JOB-TOKEN: $CI_JOB_TOKEN" \
      --upload-file "$OUT/$g" "$base/$g"
  done
done
printf 'release-oracle: uploaded to %s\n' "$base"
