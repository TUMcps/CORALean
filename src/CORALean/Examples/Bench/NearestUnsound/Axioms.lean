import CORALean.Examples.Bench.NearestUnsound.NearestUnsound

/-!
# The one thing the bench assumes that is FALSE

`NearestUnsound` claims that rounding to nearest rounds in the direction each
operation's name says, which it does not: it lands on whichever side is closer.
It is assumed here anyway, once, deliberately, so that `SoundFloatArithmetic`
can be instantiated at `NearestFloat` and `NearestDyadic p` and the unchanged
library run on the arithmetic CORA computes with — the paper's "round-to-nearest
(as in CORA)" baseline, and it exists for nothing else.

A false axiom proves anything, so a result that uses it proves nothing: every
such result carries this one name, `nearestUnsound`, in `#print axioms`, and no
library result may be one. Only files under `Examples/Bench/` may import this,
which `scripts/check-conventions.sh` enforces, and `scripts/check-axioms.sh`
asks Lean of every library declaration whether its proof reaches it.

Contrast `Binary64.trustedHardware`: true of IEEE 754 hardware only while values
stay in binary64's normal range. CORALean has exactly three axioms: this one,
`trustedHardware` and `trustedFlint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Bench

axiom nearestUnsound : NearestUnsound

end CORALean.Bench
