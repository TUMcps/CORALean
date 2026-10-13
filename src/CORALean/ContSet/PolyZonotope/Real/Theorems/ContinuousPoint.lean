module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.DifferentiablePoint

@[expose] public section

/-!
# The point map is continuous
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.continuous_point (pZ : PolyZonotope (Vec ℝ n)) :
    Continuous pZ.point :=
  (PolyZonotope.differentiable_point pZ).continuous

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
