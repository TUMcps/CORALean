module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.eDiffCost`

Asserted, not proved: `Operations/EDiff.lean` compares two exponents for
equality, takes both modulo two and compares those: four operations on
exponents, priced at unit like the scalar operations the model counts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.eDiff` costs. -/
def PolyZonotope.eDiffCost : Cost := ⟨4⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
