module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthMultiCost`

Asserted, not proved: `Operations/RelaxWidthMulti.lean` sums one `eDiff` per
factor, `p` of them and `p` additions.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthMulti` costs at `p` factors. -/
def PolyZonotope.relaxWidthMultiCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
