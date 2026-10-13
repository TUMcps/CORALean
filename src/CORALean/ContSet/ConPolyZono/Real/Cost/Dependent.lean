import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.Global.Cost

/-!
# `ConPolyZono.dependentCost`

Asserted, and asserted to be zero: `Operations/Dependent.lean` concatenates the
generator blocks, lays `identE` beside the exponent matrix and pads the
constraint block with `padE` — every entry of any of these is one the operand
already held or a literal `0` or `1`, so nothing is computed.

Worth stating rather than leaving out, exactly as `PolyZonotope.dependentCost`
is: `quadMapCost` is `quadMapDepCost` at the sizes this conversion leaves and
nothing more, only because this file is zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.dependent` costs: nothing. Concatenation, the identity
exponent block and the padded constraint block are index and allocation work. -/
def ConPolyZono.dependentCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
