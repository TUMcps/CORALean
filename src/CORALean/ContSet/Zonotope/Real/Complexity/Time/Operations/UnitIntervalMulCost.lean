module

public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.unitIntervalMulCost`

Asserted, not proved: `Operations/UnitIntervalMul.lean` makes the old center the
first generator and the new center zero; both are placed, not computed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.unitIntervalMul` costs: nothing. -/
def Zonotope.unitIntervalMulCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
