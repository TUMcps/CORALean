import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic — `Float.add` is a constant with no equations
— so nothing about the machine is provable and what it does has to be trusted
instead. This is where that happens, once: `TrustedHardware` is everything
`SoundFloatArithmetic` asks of a scalar, and `trustedHardware` says the machine
supplies it. Every `Float` result in the tree carries this one name and no other.

What it does not cover cannot be written into the class, whose obligations are
unconditional: a sum that overflows to `∞` is bounded by nothing real, and a
halving that underflows into the subnormals is not exact. So the assumption
holds on runs in which every value stays finite and nothing underflows, and
nothing checks that — an implementation owes a range argument, which is the one
gap between these statements and a machine. `toReal` of a non-finite float
decodes a bit pattern that denotes no number, and nothing is claimed there.

`Dyadic p` has none of this: its exponent is unbounded, and every one of the ten
is a theorem there. Prefer it wherever its cost is bearable.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
