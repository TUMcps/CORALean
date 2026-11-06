#!/bin/sh
# The shell steps of `.gitlab-ci.yml`'s `github-oracle` job, in a script so they run locally:
# builds and self-tests `oracle` and `oracle-unsound` through `release-oracle.sh` (DRY_RUN, no
# GitLab upload), packs both into `$OUT/oracle-linux-x86_64.tar.xz` with its `.sha256`, and pushes
# them to the public GitHub repository as the tag `oracle-<yyyymmdd>-<short sha>`. The tag is a
# commit of its own, outside main's history, so the 50 MB archive never enters main. CORA.cpp's CI
# downloads it from https://github.com/TUMcps/CORALean/raw/<tag>/oracle-linux-x86_64.tar.xz and
# checks the hash its `scripts/coralean.cmake` pins.
#
#   DRY_RUN=1 OUT=/some/scratch sh scripts/build/github-oracle.sh
#
# Without DRY_RUN it needs the SSH key of `github-mirror` in ~/.ssh/id_ed25519 and GitHub's host
# key in ~/.ssh/known_hosts (the job writes both). GitHub refuses files over 100 MB in a push, the
# raw executables are about 150 MB each, xz brings both to about 50 MB.

set -eu

cd "$(dirname "$0")/../.."

OUT="${OUT:-release}"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
SHA=$(git rev-parse --short=9 HEAD)
TAG="oracle-$(date -u +%Y%m%d)-$SHA"
ARCHIVE=oracle-linux-x86_64.tar.xz

CI_COMMIT_TAG="$TAG" DRY_RUN=1 OUT="$OUT" sh scripts/build/release-oracle.sh

(
  cd "$OUT"
  tar -cf - oracle-linux-x86_64 oracle-unsound-linux-x86_64 | xz -9 -T0 > "$ARCHIVE"
  sha256sum "$ARCHIVE" > "$ARCHIVE.sha256"
  size=$(wc -c < "$ARCHIVE" | tr -d ' ')
  if [ "$size" -ge 100000000 ]; then
    printf 'github-oracle: %s is %s bytes, over GitHub'"'"'s 100 MB push limit\n' "$ARCHIVE" "$size"
    exit 1
  fi
)

if [ -n "${DRY_RUN:-}" ]; then
  printf 'github-oracle: DRY_RUN, not pushing %s\n' "$TAG"
  exit 0
fi

# The tag's commit: the archive, its hash and the release description, nothing else.
repo=$(mktemp -d)
git -C "$repo" init -q
cp "$OUT/$ARCHIVE" "$OUT/$ARCHIVE.sha256" "$repo/"
cp "$OUT/release-description.md" "$repo/README.md"
git -C "$repo" add "$ARCHIVE" "$ARCHIVE.sha256" README.md
git -C "$repo" -c user.name="CORALean CI" -c user.email="coralean-ci@invalid" \
  commit -q -m "CORALean oracle $TAG (source commit $SHA)"
git -C "$repo" push git@github.com:TUMcps/CORALean.git "HEAD:refs/tags/$TAG"
printf 'github-oracle: pushed %s, sha256 %s\n' "$TAG" "$(cut -d' ' -f1 "$OUT/$ARCHIVE.sha256")"
