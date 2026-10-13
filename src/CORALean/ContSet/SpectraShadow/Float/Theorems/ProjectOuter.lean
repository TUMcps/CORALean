module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
public import CORALean.ContSet.SpectraShadow.Float.Operations.Project
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ProjectExact

@[expose] public section

/-!
# `SpectraShadow.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal shadow and the box. The nominal shadow of the projection is
definitionally the exact layer's `project` of the nominal shadow, so `project_exact` gives
the nominal obligation as an equality; the box is `Interval.project_outer`.
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

theorem SpectraShadow.project_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' S.construct ⊆ (S.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (Real.SpectraShadow.project_exact (nominal S) dims))
    (Interval.project_outer S.E dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
