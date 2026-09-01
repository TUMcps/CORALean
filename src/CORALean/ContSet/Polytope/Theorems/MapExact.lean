import CORALean.ContSet.Polytope.Operations.Mtimes
import CORALean.ContSet.Polytope.Theorems.ConvexHull

/-!
# `VPolytope.map` is exactly the image

A linear map commutes with the convex hull, and mapping the vertices is the same
as taking the image of their range. `mtimes` is this at `A *ᵥ ·`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]

theorem VPolytope.aux_range_map (f : α →ₗ[ℝ] β) (P : VPolytope α) :
    Set.range (P.map f).V = ⇑f '' Set.range P.V := Set.range_comp ⇑f P.V

theorem VPolytope.map_exact (f : α →ₗ[ℝ] β) (P : VPolytope α) :
    ⇑f '' P.construct = (P.map f).construct := by
  rw [VPolytope.construct_eq_convexHull P, VPolytope.construct_eq_convexHull (P.map f),
    VPolytope.aux_range_map, ← LinearMap.image_convexHull]

theorem VPolytope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    (M *ᵥ ·) '' P.construct = (VPolytope.mtimes M P).construct := by
  rw [VPolytope.mtimes_eq_map]
  exact VPolytope.map_exact (Matrix.mulVecLin M) P

end CORALean.Real
