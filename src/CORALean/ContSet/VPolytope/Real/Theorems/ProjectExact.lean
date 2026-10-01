import CORALean.ContSet.VPolytope.Real.Operations.Project
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact

/-!
# `VPolytope.project` is exactly the projected set

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

theorem VPolytope.project_exact (P : VPolytope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' P.construct = (P.project dims).construct :=
  VPolytope.map_exact (LinearMap.funLeft ℝ ℝ dims) P


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
