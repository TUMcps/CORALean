import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

/-!
# `VPolytope.map` is exactly the image

A linear map commutes with the convex hull, and mapping the vertices is the same
as taking the image of their range. Image is the operation this representation
is exact under, where a halfspace description is not.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem VPolytope.aux_range_map (f : α →ₗ[ℝ] β) (P : VPolytope α) :
    Set.range (P.map f).V = ⇑f '' Set.range P.V := Set.range_comp ⇑f P.V


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.map_exact (f : α →ₗ[ℝ] β) (P : VPolytope α) :
    ⇑f '' P.construct = (P.map f).construct := by
  rw [VPolytope.construct_eq_convexHull P, VPolytope.construct_eq_convexHull (P.map f),
    VPolytope.aux_range_map, ← LinearMap.image_convexHull]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
