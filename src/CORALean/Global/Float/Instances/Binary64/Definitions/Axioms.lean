module

public import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

@[expose] public section

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic, so what the machine does has to be trusted once:
`TrustedHardware` is everything `SoundFloatArithmetic` asks of a scalar, and `trustedHardware` says
the machine supplies it. It is false at the extremes (`toReal` reads `∞` as `2 ^ 1024`; a halving
into the subnormals loses a bit), so trusted only while all values remain in the normal range:
operations that overflow or underflow return NaN (`Operations/InRange.lean`), which propagates, so a
run whose result holds no NaN used only true instances: a meta-level argument, not a theorem
(README, "trust base"). CORALean declares three axioms: this one; the opt-in `trustedFlint`; and the
bench's `nearestUnsound`, FALSE BY DESIGN, both kept out of the library (`check-axioms.sh`).
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
