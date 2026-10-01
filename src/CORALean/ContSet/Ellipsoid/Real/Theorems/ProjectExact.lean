import CORALean.ContSet.Ellipsoid.Real.Operations.Project
import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact

/-!
# `Ellipsoid.project` is exactly the projected set

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

theorem Ellipsoid.project_exact (E : Ellipsoid n) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' E.construct = (E.project dims).construct :=
  Ellipsoid.map_exact (LinearMap.funLeft ℝ ℝ dims) E


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
