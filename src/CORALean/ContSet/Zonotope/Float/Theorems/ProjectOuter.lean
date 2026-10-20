module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
public import CORALean.ContSet.Zonotope.Float.Operations.Project
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# `Zonotope.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal zonotope and the box. The nominal zonotope of the projection is
definitionally the exact layer's `project` of the nominal zonotope, so `project_exact` gives
the nominal obligation as an equality; the box is `Interval.project_outer`.

## Inputs
* `Z` – zonotope
* `dims` – chosen coordinates

## Hypotheses
* none

## Conclusion
* projection is contained in the computed zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.project_outer (Z : Zonotope (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' Z.construct ⊆ (Z.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (Real.Zonotope.project_exact (nominal Z) dims))
    (Interval.project_outer Z.I_error dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
