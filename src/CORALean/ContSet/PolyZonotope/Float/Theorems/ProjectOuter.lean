import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.Project
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

/-!
# `PolyZonotope.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal part and the box. The nominal part of the projection is the exact
layer's `map` of the nominal part at the selection map, so `map_exact` gives the nominal
obligation as an equality; the box is `Interval.project_outer`.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.project_outer (pZ : PolyZonotope (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' pZ.construct ⊆ (pZ.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (Real.PolyZonotope.map_exact (LinearMap.funLeft ℝ ℝ dims) (nominal pZ)))
    (Interval.project_outer pZ.err dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
