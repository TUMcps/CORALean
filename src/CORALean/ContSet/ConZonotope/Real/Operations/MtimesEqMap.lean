import CORALean.ContSet.ConZonotope.Real.Operations.Map
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

/-!
# `ConZonotope.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConZonotope.mtimes_eq_map (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    ConZonotope.mtimes M cZ = cZ.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
