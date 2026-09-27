import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic — `Float.add` is a constant with no equations
— so nothing about the machine is provable and what it does has to be trusted
instead. This is where that happens, once: `TrustedHardware` is everything
`SoundFloatArithmetic` asks of a scalar, and `trustedHardware` says the machine
supplies it. Every `Float` result in the tree carries this one name and no other.

What it does not cover cannot be written into the class, whose obligations are
unconditional: an overflow to `∞` is bounded by nothing real, and a halving into
the subnormals is not exact. So the assumption holds on runs in which every value
stays finite and nothing underflows, which nothing checks — an implementation owes
a range argument. `toReal` of a non-finite float denotes no number; nothing is claimed.

`Dyadic p` has none of this: its exponent is unbounded, and all ten are theorems
there; prefer it wherever its cost is bearable. The bench's `nearestUnsound` is
this one's opposite, FALSE by design where this is true on IEEE 754 hardware,
and `scripts/check-axioms.sh` keeps it out of the library.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   27-September-2026
-- Last revision: ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
