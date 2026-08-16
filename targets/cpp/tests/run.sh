#!/usr/bin/env bash
#
# Build and run every test.
#
# Usage: ./run.sh [compiler]
#
# Authors:       Tobias Ladner
# Written:       16-August-2026
# Last update:   ---
# Last revision: ---

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cxx="${1:-g++}"
out_dir="$(mktemp -d)"
trap 'rm -rf "$out_dir"' EXIT

# Each flag stands for an assumption the FloatOps axioms make; see ../README.md.
flags=(-std=c++20 -Wall -Wextra -Werror -O2
       -frounding-math -ffp-contract=off
       -I"$script_dir/../src" -I"$script_dir")

failed=0
for src in "$script_dir"/*.cpp; do
  name="$(basename "$src" .cpp)"
  "$cxx" "${flags[@]}" -o "$out_dir/$name" "$src"
  "$out_dir/$name" || failed=1
done

if [[ $failed -ne 0 ]]; then
  echo "FAILURES"
  exit 1
fi
echo "all suites passed"
