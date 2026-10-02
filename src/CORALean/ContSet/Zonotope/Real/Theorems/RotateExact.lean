import CORALean.ContSet.Zonotope.Real.Operations.Rotate
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# Rotating a zonotope is exact

`rotate` denotes the image of the zonotope under the rotation: an equality, a matrix times a
zonotope being exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: the image of `Z` under the rotation is what `rotate` denotes. -/
theorem Zonotope.rotate_exact {n : ℕ} (Z : Zonotope (Vec ℝ n)) (i j : Fin n) (angle : ℝ) :
    (rotMat n i j angle *ᵥ ·) '' Z.construct = (Z.rotate i j angle).construct :=
  Zonotope.mtimes_exact _ Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
