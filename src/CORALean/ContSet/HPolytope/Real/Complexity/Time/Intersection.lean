module

public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.intersectionCost`

Asserted, and asserted to be zero: `Operations/Intersection.lean` is six calls
to `Fin.append`, one per field, which is index work and free under
`Global/Cost.lean`'s model — the same reading `Zonotope.plusCost` gives its own
generator concatenation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.intersection` costs: nothing. The constraint lists
concatenate, and concatenation is index work. -/
def HPolytope.intersectionCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
