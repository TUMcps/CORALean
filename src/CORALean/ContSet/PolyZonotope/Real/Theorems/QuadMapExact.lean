import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact

/-!
# `PolyZonotope.quadMap` is exactly the image under a quadratic map

The claim the representation exists for, and one no convex representation here
can make. `quadMapDep` does the work under an empty independent block, and
`dependent` is what empties it — exactly, so nothing is lost on the way in
either.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.quadMap_exact (Q : Fin m → Mat ℝ n n) (PZ : PolyZonotope (Vec ℝ n)) :
    quadEval Q '' PZ.construct = (PZ.quadMap Q).construct := by
  rw [PZ.dependent_exact]
  exact PolyZonotope.quadMapDep_exact Q PZ.dependent rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
