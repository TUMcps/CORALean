import CORALean.ContSet.ConPolyZono.Real.Operations.Project
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact

/-!
# `ConPolyZono.project` is exactly the projected set

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

theorem ConPolyZono.project_exact (cPZ : ConPolyZono (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cPZ.construct = (cPZ.project dims).construct :=
  ConPolyZono.map_exact (LinearMap.funLeft ℝ ℝ dims) cPZ


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
