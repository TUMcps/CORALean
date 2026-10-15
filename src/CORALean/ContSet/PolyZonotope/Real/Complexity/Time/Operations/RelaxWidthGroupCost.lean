module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthGroupCost`

Asserted, not proved: `Operations/RelaxWidthGroup.lean` is the same sum as
`relaxWidthMulti`, `p` `eDiff`s and `p` additions, for one grouped generator.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthGroup` costs at `p` factors. -/
def PolyZonotope.relaxWidthGroupCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
