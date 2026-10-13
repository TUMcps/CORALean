module

public import CORALean.ContSet.ConZonotope.Real.Operations.Map
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConZonotope.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


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
