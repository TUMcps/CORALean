module

public import CORALean.Global.Float.Instances.Binary64.Definitions.IsTrustedHardware

@[expose] public section

/-!
# The one thing this repository assumes

`Float` is opaque in Lean's logic, so what the machine does has to be trusted once:
`IsTrustedHardware` is everything `SoundFloatArithmetic` asks of a scalar, and `trustedHardware`
says the machine supplies it. It does not: fields fail where their result is a NaN, which every
rounded operation returns outside the normal range (`stepUp`, `step_inRange`), and together they
are unsatisfiable, so this axiom proves `False` (`not_isTrustedHardware`). A theorem at `Float`
guarantees nothing on its own; what a run rests on instead, an informal argument, is README, "The
trust base". The other two axioms: the opt-in `trustedFlint`, and the bench's `nearestUnsound`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       22-September-2026
-- Last update:   10-November-2026
-- Reviewed:      ---

namespace CORALean.Float.Binary64

/-- FALSE: see the module docstring and `not_isTrustedHardware`. -/
axiom trustedHardware : IsTrustedHardware

end CORALean.Float.Binary64
