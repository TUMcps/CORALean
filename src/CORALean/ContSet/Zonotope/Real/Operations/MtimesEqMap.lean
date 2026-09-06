import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `Zonotope.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem Zonotope.mtimes_eq_map (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope.mtimes M Z = Z.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
