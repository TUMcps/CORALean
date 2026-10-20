module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Project
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact

@[expose] public section

/-!
# `SpectraShadow.project` is exactly the projected set

Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact on a
spectrahedral shadow, so nothing is added and nothing lost.

## Inputs
* `S` – spectrahedral shadow
* `dims` – indices indexed by `Fin m`

## Hypotheses
* none

## Conclusion
* `SpectraShadow.project` is exactly the projected set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.project_exact (S : SpectraShadow (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' S.construct = (S.project dims).construct :=
  SpectraShadow.map_exact (LinearMap.funLeft ℝ ℝ dims) S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
