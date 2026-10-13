module

public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter
public import CORALean.ContSet.VPolytope.Float.Operations.Project
public import CORALean.ContSet.VPolytope.Real.Theorems.ProjectExact

@[expose] public section

/-!
# `VPolytope.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal part and the box. The nominal part of the projection is the exact
layer's `project` of the nominal part, so `project_exact` gives the nominal obligation as an
equality; the box is `Interval.project_outer`.
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

theorem VPolytope.project_outer (P : VPolytope (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' P.construct ⊆ (P.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (Real.VPolytope.project_exact (nominal P) dims))
    (Interval.project_outer P.E dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
