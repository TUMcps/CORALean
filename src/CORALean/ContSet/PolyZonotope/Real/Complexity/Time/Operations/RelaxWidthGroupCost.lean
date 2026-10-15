module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.EDiffCost

@[expose] public section

/-!
# `PolyZonotope.relaxWidthGroupCost`

Asserted, not proved: `Operations/RelaxWidthGroup.lean` is the same sum as
`relaxWidthMulti`, `p` `eDiff`s and `p` additions, for one grouped generator, and one write of the
sum.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthGroup` costs at `p` factors: `p` calls of `eDiff`, `p` additions
and one write. -/
def PolyZonotope.relaxWidthGroupCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p + 1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
