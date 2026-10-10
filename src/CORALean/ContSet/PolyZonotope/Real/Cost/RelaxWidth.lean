import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidth
import CORALean.ContSet.PolyZonotope.Real.Cost.EDiff

/-!
# `PolyZonotope.relaxWidthCost`

Asserted, not proved: `Operations/RelaxWidth.lean` is one `eDiff` at the exponent
index it names; the factor count does not enter.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidth` costs. -/
def PolyZonotope.relaxWidthCost : Cost := PolyZonotope.eDiffCost

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
