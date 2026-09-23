import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import CORALean.Global.Cost

/-!
# `HPolytope.intersectionCost`

Asserted, and asserted to be zero: `Operations/Intersection.lean` is six calls
to `Fin.append`, one per field, which is index work and free under
`Global/Cost.lean`'s model — the same reading `Zonotope.plusCost` gives its own
generator concatenation.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.intersection` costs: nothing. The constraint lists
concatenate, and concatenation is index work. -/
def HPolytope.intersectionCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
