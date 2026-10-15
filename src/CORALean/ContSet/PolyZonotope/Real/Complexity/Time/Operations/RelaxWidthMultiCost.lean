module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthMultiCost`

Asserted, not proved: `Operations/RelaxWidthMulti.lean` sums one `eDiff` per
factor, `p` of them and `p` additions, and one write of the sum.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthMulti` costs at `p` factors: `p` calls of `eDiff`, `p` additions
and one write. -/
def PolyZonotope.relaxWidthMultiCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p + 1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
