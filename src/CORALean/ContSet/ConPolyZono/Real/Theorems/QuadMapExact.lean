import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.QuadMapDepExact

/-!
# `ConPolyZono.quadMap` is exactly the image under a quadratic map

`quadMapDep` needs an empty independent block, which `hq` asks for; `quadMap`
supplies it by running `dependent` first, and `dependent` is exact. Together
with `and_exact` this is what a nonlinear reachability step needs: propagate
through a quadratic map, then cut by a guard, neither losing anything.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMap_exact (Q : Fin k → Mat ℝ n n) (C : ConPolyZono (Vec ℝ n)) :
    quadEval Q '' C.construct = (C.quadMap Q).construct := by
  rw [C.dependent_exact]
  exact ConPolyZono.quadMapDep_exact Q C.dependent rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
