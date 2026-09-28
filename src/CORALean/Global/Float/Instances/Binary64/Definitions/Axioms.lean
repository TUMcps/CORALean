import CORALean.Global.Float.Instances.Binary64.Definitions.TrustedHardware

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic — `Float.add` is a constant with no equations
— so what the machine does has to be trusted instead, once: `TrustedHardware` is
everything `SoundFloatArithmetic` asks of a scalar, and `trustedHardware` says
the machine supplies it. Every `Float` result carries this one name and no other.

Stated as the class needs it, unconditionally, it is false at the extremes: `toReal` reads `∞`
as `2 ^ 1024`, below an overflowing sum, and a halving into the subnormals loses a bit. It is
trusted only while all values remain in the normal range of binary64: operations that overflow
or underflow return NaN (`Operations/InRange.lean`), which propagates to the result, so such
runs are detected at run time. `toReal` of a NaN denotes no number; nothing is claimed of one.

`Dyadic p` and `IEEE fmt` have none of this: all ten are theorems there, and `IEEE` rounds onto
binary64's own grid. CORALean declares three axioms in total: this one; the optional
backend's `trustedFlint` (`Global/Float/Instances/Flint/`), true of FLINT and
opt-in; and the bench's `nearestUnsound`, this one's opposite, FALSE BY DESIGN
-- both kept out of the library, which `check-axioms.sh` checks.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Last revision: ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
