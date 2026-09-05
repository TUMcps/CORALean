import CORALean.ContSet.ConPolyZono.Real.Operations.Map
import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

/-!
# `ConPolyZono.mtimes` is `map` at the matrix's linear map
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {k n : ℕ}

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConPolyZono.mtimes_eq_map (M : Mat ℝ k n) (C : ConPolyZono (Vec ℝ n)) :
    ConPolyZono.mtimes M C = C.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
