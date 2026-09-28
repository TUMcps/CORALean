#!/bin/sh
# Builds the one archive `bench-flint` links: `ffi/coralean_flint.c` compiled
# and combined with FLINT's, MPFR's and GMP's static libraries into a single
# relocatable object, then stripped of every global symbol but the shim's own
# `coralean_flint_*` six. That last step is not cosmetic: Lean's runtime links
# its own static GMP (6.1.2), older than the >= 6.2 FLINT 3 needs, so if the
# copy this script bundles kept its GMP symbols global, the final link of
# `bench-flint` would see two definitions of `__gmpz_init` and the like and
# fail, or worse, silently pick one. `objcopy -w --keep-global-symbol` turns
# every other global into local, so the two GMPs coexist in one binary without
# meeting.
#
#   bash scripts/install-flint.sh          # once, builds FLINT/MPFR/GMP
#   bash scripts/build-flint-shim.sh        # this script, into .lake/flint/
#   lake build bench-flint                  # or: lake exe bench-flint ...
#
# `FLINT_PREFIX` must match install-flint.sh's (default $HOME/.local/flint-prefix).

set -eu

cd "$(dirname "$0")/.."

PREFIX=${FLINT_PREFIX:-$HOME/.local/flint-prefix}
OUT=.lake/flint
mkdir -p "$OUT"

for lib in libflint.a libmpfr.a libgmp.a; do
  if [ ! -f "$PREFIX/lib/$lib" ]; then
    echo "build-flint-shim: $PREFIX/lib/$lib not found -- run scripts/install-flint.sh first" >&2
    exit 1
  fi
done

# `leanc` is a bundled clang without the host's usual system include paths
# wired in (it is meant to be driven by Lake, which sets them up), so this
# uses the system `cc` instead, pointed at `lean.h` under the toolchain
# `lean --print-prefix` names, plus FLINT's own include directory.
LEAN_PREFIX=$(lean --print-prefix)
cc -c ffi/coralean_flint.c -I "$LEAN_PREFIX/include" -I "$PREFIX/include" -O2 -fPIC \
  -o "$OUT/coralean_flint.o"

# Pulls in only the FLINT/MPFR/GMP object members the shim's calls (and their
# own transitive calls) actually reach -- not every member of every archive --
# and folds them into one relocatable object alongside the shim itself.
ld -r --start-group \
  "$OUT/coralean_flint.o" "$PREFIX/lib/libflint.a" "$PREFIX/lib/libmpfr.a" "$PREFIX/lib/libgmp.a" \
  --end-group -o "$OUT/combined.o"

# Every global but the six `coralean_flint_*` entry points becomes local: GMP's,
# MPFR's and FLINT's own symbols stop being visible to the linker of the final
# executable, so they cannot clash with Lean's runtime GMP.
objcopy -w --keep-global-symbol='coralean_flint_*' "$OUT/combined.o" "$OUT/hidden.o"

rm -f "$OUT/libcoralean_flint.a"
ar rcs "$OUT/libcoralean_flint.a" "$OUT/hidden.o"

# Verify: only the shim's own six names may be global (`T`/`t`, text section) in
# the finished archive.
bad=$(nm --defined-only -g "$OUT/libcoralean_flint.a" | awk '{print $3}' | grep -v '^coralean_flint_' || true)
if [ -n "$bad" ]; then
  echo "build-flint-shim: unexpected global symbol(s) survived hiding:" >&2
  echo "$bad" >&2
  exit 1
fi

echo "built $OUT/libcoralean_flint.a"
nm --defined-only -g "$OUT/libcoralean_flint.a" | awk '{print $3}' | sort
