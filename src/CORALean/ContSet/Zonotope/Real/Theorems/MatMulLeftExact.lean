import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# A matrix zonotope multiplied from the left, exactly

CORA's matZonotope times a matrix. `map_exact` at `matMulLeft M`, the whole of
what the matrix case needs: left and right multiplication are two linear maps,
and nothing about them is special.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMulLeft_exact {p q r : ℕ} (M : Mat ℝ p q) (Z : Zonotope (Mat ℝ q r)) :
    (M * ·) '' Z.construct = (Zonotope.mapOf (matMulLeft M) Z).construct :=
  Zonotope.map_exact (matMulLeft M) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
