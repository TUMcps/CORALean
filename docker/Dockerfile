# The CI build environment, with every dependency already in place.
#
# CI talks to GitHub four times — elan's installer, the toolchain release, the
# Mathlib clone, and the eight further clones inside `lake exe cache get` — and
# GitHub rate-limits anonymous requests per IP, which a shared university runner
# exhausts. No clone strategy fixes that; the answer is to stop cloning in CI.
#
# So the dependencies are resolved *here*, on a machine whose network works, and
# the result is shipped as an image. `lake exe cache get` runs during the build
# rather than in CI, which is also what guarantees the layout is one Lake
# accepts: it is Lake that produced it.
#
# Rebuild when `lean-toolchain` or `lake-manifest.json` changes, and tag with
# both — the image is a function of exactly those two files.
#
#   sh scripts/build-image.sh                 build
#   sh scripts/build-image.sh --push <repo>   build and push

FROM debian:bookworm-slim

RUN apt-get update -qq \
 && apt-get install -y -qq --no-install-recommends \
      curl git ca-certificates mawk findutils \
 && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH

COPY lean-toolchain /deps/lean-toolchain

RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none \
 && elan toolchain install "$(cat /deps/lean-toolchain)" \
 && elan default "$(cat /deps/lean-toolchain)"

COPY lakefile.toml lake-manifest.json /deps/

WORKDIR /deps

# A package root has to exist for Lake to resolve the package at all; it is the
# manifest that decides what gets fetched, so an empty one is enough and is
# removed again once the dependencies are down.
RUN mkdir -p src \
 && printf '' > src/CORALean.lean \
 && lake exe cache get \
 && rm -rf src

# A job points `.lake/packages` at this and builds. Nothing in CI reaches the
# network.
LABEL org.opencontainers.image.description="CORALean CI: Lean toolchain and \
resolved dependencies, so a build needs no network"
