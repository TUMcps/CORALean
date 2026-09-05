import CORALean.ContSet.VPolytope.Real.Operations.Map
import CORALean.ContSet.VPolytope.Real.Operations.Mtimes

/-!
# `VPolytope.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem VPolytope.mtimes_eq_map (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    VPolytope.mtimes M P = P.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
