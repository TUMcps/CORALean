module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.eDiffCost`

Asserted, not proved: `Operations/EDiff.lean` compares two exponents for
equality, takes both modulo two and compares those: four operations on
exponents, priced at unit like the scalar operations the model counts, and one write of the
result.

## Inputs
* none

## Output
* operation count of an exponent difference
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.eDiff` costs: the equality test and the two parities with their
comparison, and one write of the result. -/
def PolyZonotope.eDiffCost : Cost := ⟨5⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
