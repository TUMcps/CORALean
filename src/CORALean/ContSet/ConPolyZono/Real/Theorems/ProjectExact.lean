module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Project
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact

@[expose] public section

/-!
# `ConPolyZono.project` is exactly the projected set

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

theorem ConPolyZono.project_exact (cPZ : ConPolyZono (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cPZ.construct = (cPZ.project dims).construct :=
  ConPolyZono.map_exact (LinearMap.funLeft ℝ ℝ dims) cPZ


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
