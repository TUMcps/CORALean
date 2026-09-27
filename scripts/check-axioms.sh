#!/bin/sh
# Asks Lean which axioms the library's results rest on, so that the bench's
# round-to-nearest baseline cannot leak into them. That baseline assumes
# `nearestUnsound`, FALSE by design (`Examples/Bench/NearestUnsound/Axioms.lean`),
# and a false axiom proves anything: harmless exactly as long as no library
# theorem's proof term reaches it, which is what this checks.
#
# `check-conventions.sh` refuses the import that would let one in; this reads
# the proof terms themselves, through `Lean.collectAxioms` in
# `scripts/check-axioms.lean`: that it and `trustedHardware` are the only axioms
# CORALean declares, the headline guarantees by name, every declaration of every
# library module by sweep, and, as a positive control, two copies of
# `reachFloat_outer` at the unsound scalars, which must be tainted.
#
# Needs a built tree, like `check-demo.sh`, so it runs in CI's build job and not
# on the pre-commit hook. Seconds once built: the axiom sets are stored in the
# oleans, so the sweep is a lookup per declaration.

set -eu

cd "$(dirname "$0")/.."

if lake env lean scripts/check-axioms.lean; then
  printf 'axioms: no library result rests on nearestUnsound\n'
else
  printf 'axioms: a library result rests on the false nearestUnsound, or the check\n'
  printf '        could not run — see the errors above\n'
  exit 1
fi
