import CORALean.ContSet.PolyZonotope.Real.Theorems.DifferentiablePoint

/-!
# The point map is continuous
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.continuous_point (pZ : PolyZonotope (Vec ℝ n)) :
    Continuous pZ.point :=
  (PolyZonotope.differentiable_point pZ).continuous

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
