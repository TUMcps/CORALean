import CORALean.ContSet.ConZonotope.Real.Operations.Map

/-!
# `ConZonotope.project`

CORA's `@conZonotope/project`: the centre and generators at the chosen coordinates, with the
constraint untouched. `dims` may repeat or reorder coordinates. Reading coordinates is linear, so
this is `map` at the selection map, and `project_exact` is `map_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.project (cZ : ConZonotope (Vec ℝ n))
    (dims : Fin m → Fin n) : ConZonotope (Vec ℝ m) :=
  cZ.map (LinearMap.funLeft ℝ ℝ dims)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
