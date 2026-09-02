import CORALean.ContSet.Ellipsoid.Real.Operations.Map
import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact

/-!
# `Ellipsoid.map` is exactly the image under a linear map

`mtimes_exact` read at the matrix the map is, the two being the same thing at
`Vec ℝ n`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

theorem aux_toMatrix'_mulVec (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (x : Vec ℝ n) :
    (LinearMap.toMatrix' f) *ᵥ x = f x := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

theorem Ellipsoid.map_exact (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (E : Ellipsoid n) :
    f '' E.construct = (Ellipsoid.map f E).construct := by
  rw [Ellipsoid.map, ← Ellipsoid.mtimes_exact]
  exact Set.image_congr fun x _ => (aux_toMatrix'_mulVec f x).symm

end CORALean.Real
