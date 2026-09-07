import CORALean.ContSet.ConPolyZono.Real.Operations.Map
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

/-!
# `ConPolyZono.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConPolyZono.mtimes_eq_map (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono.mtimes M cPZ = cPZ.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
