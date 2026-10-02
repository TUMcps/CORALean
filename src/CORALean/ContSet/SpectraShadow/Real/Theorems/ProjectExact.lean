import CORALean.ContSet.SpectraShadow.Real.Operations.Project
import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact

/-!
# `SpectraShadow.project` is exactly the projected set

Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact on a
spectrahedral shadow, so nothing is added and nothing lost.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.project_exact (S : SpectraShadow (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' S.construct = (S.project dims).construct :=
  SpectraShadow.map_exact (LinearMap.funLeft ℝ ℝ dims) S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
