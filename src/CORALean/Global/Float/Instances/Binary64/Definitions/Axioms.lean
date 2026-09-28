import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic — `Float.add` is a constant with no equations
— so what the machine does has to be trusted instead, once: `TrustedHardware` is
everything `SoundFloatArithmetic` asks of a scalar, and `trustedHardware` says
the machine supplies it. Every `Float` result carries this one name and no other.

What it does not cover cannot be written into the class, whose obligations are
unconditional: an overflow to `∞` is bounded by nothing real, and a halving into
the subnormals is not exact. The assumption holds on runs where every value stays
finite and nothing underflows, which nothing checks; `toReal` of a non-finite
float denotes no number, and nothing is claimed of it.

`Dyadic p` has none of this: its exponent is unbounded, all ten are theorems
there. CORALean declares three axioms in total: this one; the optional
backend's `trustedFlint` (`Global/Float/Instances/Flint/`), true of FLINT and
opt-in; and the bench's `nearestUnsound`, this one's opposite, FALSE BY DESIGN
-- both kept out of the library, which `check-axioms.sh` checks.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   27-September-2026
-- Last revision: ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
