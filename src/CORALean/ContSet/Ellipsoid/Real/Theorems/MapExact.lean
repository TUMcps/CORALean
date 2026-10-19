module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Map
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact

@[expose] public section

/-!
# `Ellipsoid.map` is exactly the image under a linear map

`mtimes_exact` read at the matrix the map is, the two being the same thing at
`Vec ℝ n`.

## Inputs
* `f` – linear map
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the image of `E` under `f` is exactly the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_toMatrix'_mulVec (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (x : Vec ℝ n) :
    (LinearMap.toMatrix' f) *ᵥ x = f x := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.map_exact (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (E : Ellipsoid n) :
    f '' E.construct = (Ellipsoid.map f E).construct := by
  rw [Ellipsoid.map, ← Ellipsoid.mtimes_exact]
  exact Set.image_congr fun x _ => (aux_toMatrix'_mulVec f x).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
