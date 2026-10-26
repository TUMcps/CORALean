#!/bin/sh
# Builds FLINT, and the GMP and MPFR it needs, from source into a user prefix,
# for the optional FLINT backend (`Flint p`, README "FLINT backend
# (optional)"). Nothing else in the tree needs it: the default `lake build` and
# CI never link FLINT.
#
#   bash scripts/build/install-flint.sh            # into $HOME/.local/flint-prefix
#   FLINT_PREFIX=/opt/flint bash scripts/build/install-flint.sh
#
# Then `lake -K flint=on build bench-flint`, with the same FLINT_PREFIX in the
# environment if it is not the default.
#
# Needs a C compiler, make and a network connection. GNU m4, which GMP's
# configure requires, is built into the prefix first when it is not on PATH. No
# root: everything lands under the prefix.
#
# Versions are pinned so that a rebuild reproduces the backend the
# differential test was run against:
#   m4 1.4.19 (only if missing), GMP 6.3.0, MPFR 4.2.2, FLINT 3.6.0.
#
# Every library is built static and position-independent. The bench links them
# into one relocatable object whose only global symbols are the shim's
# `coralean_flint_*` (see `c/flint_shim.c`), because Lean's runtime carries its
# own, older GMP (6.1.2, linked statically), and two GMPs in one symbol
# namespace would bind FLINT's calls to whichever copy the linker saw first.

set -eu

PREFIX=${FLINT_PREFIX:-$HOME/.local/flint-prefix}
JOBS=${JOBS:-$(nproc 2>/dev/null || echo 4)}

M4_VERSION=1.4.19
GMP_VERSION=6.3.0
MPFR_VERSION=4.2.2
FLINT_VERSION=3.6.0

SRC=$PREFIX/src
mkdir -p "$SRC"
PATH=$PREFIX/bin:$PATH
export PATH

fetch() {
  # fetch URL FILE: download once, keep for rebuilds.
  if [ ! -f "$SRC/$2" ]; then
    curl -fL --retry 3 -o "$SRC/$2.part" "$1"
    mv "$SRC/$2.part" "$SRC/$2"
  fi
}

unpack() {
  # unpack FILE DIR: a fresh tree each time, so a failed build leaves no state.
  rm -rf "${SRC:?}/$2"
  tar -xf "$SRC/$1" -C "$SRC"
}

if ! command -v m4 >/dev/null 2>&1; then
  fetch "https://ftp.gnu.org/gnu/m4/m4-$M4_VERSION.tar.xz" "m4-$M4_VERSION.tar.xz"
  unpack "m4-$M4_VERSION.tar.xz" "m4-$M4_VERSION"
  (cd "$SRC/m4-$M4_VERSION" &&
    ./configure --prefix="$PREFIX" &&
    make -j"$JOBS" && make install)
fi

fetch "https://ftp.gnu.org/gnu/gmp/gmp-$GMP_VERSION.tar.xz" "gmp-$GMP_VERSION.tar.xz"
unpack "gmp-$GMP_VERSION.tar.xz" "gmp-$GMP_VERSION"
(cd "$SRC/gmp-$GMP_VERSION" &&
  ./configure --prefix="$PREFIX" --enable-static --disable-shared --with-pic &&
  make -j"$JOBS" && make install)

fetch "https://ftp.gnu.org/gnu/mpfr/mpfr-$MPFR_VERSION.tar.xz" "mpfr-$MPFR_VERSION.tar.xz"
unpack "mpfr-$MPFR_VERSION.tar.xz" "mpfr-$MPFR_VERSION"
(cd "$SRC/mpfr-$MPFR_VERSION" &&
  ./configure --prefix="$PREFIX" --with-gmp="$PREFIX" \
    --enable-static --disable-shared --with-pic &&
  make -j"$JOBS" && make install)

fetch "https://github.com/flintlib/flint/releases/download/v$FLINT_VERSION/flint-$FLINT_VERSION.tar.gz" \
  "flint-$FLINT_VERSION.tar.gz"
unpack "flint-$FLINT_VERSION.tar.gz" "flint-$FLINT_VERSION"
# FLINT's configure ignores `--with-pic` and compiles position-dependent code
# unless the shared library is built too, so both are; only the archive is used.
(cd "$SRC/flint-$FLINT_VERSION" &&
  ./configure --prefix="$PREFIX" --with-gmp="$PREFIX" --with-mpfr="$PREFIX" \
    --enable-static --enable-shared &&
  make -j"$JOBS" && make install)

# FLINT's own tests of the `arf` module, the one the backend trusts; minutes.
if [ "${FLINT_CHECK:-0}" = 1 ]; then
  (cd "$SRC/flint-$FLINT_VERSION" && make -j"$JOBS" check MOD=arf)
fi

echo "FLINT $FLINT_VERSION, MPFR $MPFR_VERSION, GMP $GMP_VERSION installed in $PREFIX"
