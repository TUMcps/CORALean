import CORALean.ContSet.ConZonotope.Real.Operations.Project
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact

/-!
# `ConZonotope.project` is exactly the projected set

Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.project_exact (cZ : ConZonotope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cZ.construct = (cZ.project dims).construct :=
  ConZonotope.map_exact (LinearMap.funLeft ℝ ℝ dims) cZ


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
