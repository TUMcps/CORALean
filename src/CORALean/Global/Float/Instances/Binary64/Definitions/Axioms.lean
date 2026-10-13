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
or underflow return NaN (`Operations/InRange.lean`), which propagates, so a run whose result
holds no NaN used only true instances of it: a meta-level argument with limits, not a theorem
(README, "trust base"). `toReal` reads a NaN's bits as the number `1.5 * 2 ^ 1024`; nothing true
is claimed of it, and `hardwarecheck`'s `litFalse` counts the false instances.

`Dyadic p` and `IEEE fmt` have none of this: all ten are theorems there. CORALean declares three
axioms: this one; the opt-in `trustedFlint` (`Flint/`), true of FLINT; and the bench's
`nearestUnsound`, FALSE BY DESIGN -- both kept out of the library, which `check-axioms.sh` checks.
-/

-- Authors:       Claude Sonnet 5
-- Written:       22-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---

namespace CORALean.Float.Binary64

axiom trustedHardware : TrustedHardware

end CORALean.Float.Binary64
