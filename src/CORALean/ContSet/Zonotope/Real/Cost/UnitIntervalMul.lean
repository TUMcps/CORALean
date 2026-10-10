import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
import CORALean.Global.Cost

/-!
# `Zonotope.unitIntervalMulCost`

Asserted, not proved: `Operations/UnitIntervalMul.lean` makes the old centre the
first generator and the new centre zero; both are placed, not computed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.unitIntervalMul` costs: nothing. -/
def Zonotope.unitIntervalMulCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
