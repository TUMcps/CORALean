import CORALean.ContSet.Zonotope.Real.Operations.Project
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# `Zonotope.project` is exactly the projected set

Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.project_exact (Z : Zonotope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' Z.construct = (Z.project dims).construct :=
  Zonotope.map_exact (LinearMap.funLeft ℝ ℝ dims) Z


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
