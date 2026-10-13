module

public import CORALean.ContSet.VPolytope.Real.Operations.LinComb
public import CORALean.Global.Cost

@[expose] public section

/-!
# `VPolytope.linCombCost`

Asserted, and asserted to be zero: `Operations/LinComb.lean` is `Fin.append` on
the two vertex lists, which is index work and free under `Global/Cost.lean`'s
model — no fresh vertex is computed, unlike a zonotope's `linComb`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `VPolytope.linComb` costs: nothing. The two vertex lists concatenate. -/
def VPolytope.linCombCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
