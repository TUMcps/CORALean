module

public import CORALean.ContSet.VPolytope.Real.Operations.Map

@[expose] public section

/-!
# `VPolytope.project`

CORA's `@polytope/project`: the vertices at the chosen coordinates (`V(dims,:)` in CORA). `dims`
may repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the
selection map, and `project_exact` is `map_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.project (P : VPolytope (Vec ℝ n)) (dims : Fin m → Fin n) : VPolytope (Vec ℝ m) :=
  P.map (LinearMap.funLeft ℝ ℝ dims)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
