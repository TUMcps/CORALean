import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.Global.Cost

/-!
# `PolyZonotope.eDiffCost`

Asserted, not proved: `Operations/EDiff.lean` compares two exponents for
equality, takes both modulo two and compares those: four operations on
exponents, priced at unit like the scalar operations the model counts.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.eDiff` costs. -/
def PolyZonotope.eDiffCost : Cost := ⟨4⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
