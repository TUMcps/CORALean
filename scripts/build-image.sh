#!/bin/sh
# Builds the CI image described in docker/Dockerfile, tagged by the two files it
# is a function of: the toolchain and the dependency manifest.
#
#   sh scripts/build-image.sh                          build only
#   sh scripts/build-image.sh --push <registry/repo>   build and push
#
# The registry is a choice, not a constant. gitlab.lrz.de's own registry is the
# better target when it is enabled — CI pulls from the same host it clones from,
# authenticates with the job token, and no second account is involved. Docker
# Hub works too, at the cost of its own anonymous pull limit, which is the kind
# of thing that put us here.

set -eu

cd "$(dirname "$0")/.."

TOOLCHAIN=$(sed 's|.*:||' lean-toolchain)
REV=$(sed -n 's/.*"rev": "\([0-9a-f]\{40\}\)".*/\1/p' lake-manifest.json | head -1)
TAG="${TOOLCHAIN}-$(echo "$REV" | cut -c1-8)"

REPO="coralean-ci"
PUSH=""
if [ "${1:-}" = "--push" ]; then
  PUSH=1
  REPO="${2:?usage: build-image.sh --push <registry/repo>}"
fi

echo "toolchain: $TOOLCHAIN"
echo "mathlib:   $REV"
echo "tag:       $REPO:$TAG"

# A context of exactly the three files the image is built from, so an edit under
# `src/` invalidates no layer and nothing sends 7 GB of `.lake` to the daemon.
CTX=$(mktemp -d)
trap 'rm -rf "$CTX"' EXIT
cp lean-toolchain lakefile.toml lake-manifest.json "$CTX/"
cp docker/Dockerfile "$CTX/Dockerfile"

# The daemon is a Windows service under Git Bash, and takes a Windows path.
CTXD="$CTX"
if command -v cygpath >/dev/null 2>&1; then CTXD=$(cygpath -w "$CTX"); fi

docker build -t "$REPO:$TAG" -t "$REPO:latest" "$CTXD"

if [ -n "$PUSH" ]; then
  docker push "$REPO:$TAG"
  docker push "$REPO:latest"
  echo "pushed $REPO:$TAG"
  echo "now set the build job's image: to that, and commit"
fi
