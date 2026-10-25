import CORALean.Examples.Bench.NearestUnsound.NearestUnsound

/-!
# The one thing the bench assumes that is FALSE

`IsNearestUnsound` claims that rounding to nearest rounds in the direction each operation's name
says, which it does not: it lands on whichever side is closer. It is assumed here anyway, once, so
that `SoundFloatArithmetic` can be instantiated at `NearestFloat` and `NearestDyadic p` and the
library run on the arithmetic CORA computes with, the paper's "round-to-nearest (as in CORA)"
baseline. A false axiom proves anything, so every result using it carries `nearestUnsound` in
`#print axioms` and no library result may be one: only files under `Examples/Bench/` may import
this (`scripts/check-conventions.sh`), and `scripts/check-axioms.sh` checks every library
declaration. CORALean has exactly three axioms: this one, `trustedHardware` and `trustedFlint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Bench

axiom nearestUnsound : IsNearestUnsound

end CORALean.Bench
