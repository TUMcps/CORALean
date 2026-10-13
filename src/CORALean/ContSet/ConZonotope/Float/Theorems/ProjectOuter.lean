import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
import CORALean.ContSet.ConZonotope.Float.Operations.Project
import CORALean.ContSet.ConZonotope.Real.Theorems.ProjectExact

/-!
# `ConZonotope.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal part and the box. The nominal part of the projection is the exact
layer's `project` of the nominal part, so `project_exact` gives the nominal obligation as an
equality; the box is `Interval.project_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.project_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cZ.construct ⊆ (cZ.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (Real.ConZonotope.project_exact (nominal cZ) dims))
    (Interval.project_outer cZ.E dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
