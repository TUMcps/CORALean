import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes

/-!
# `PolyZonotope.mtimes` is `map` at the matrix's linear map

Split out of `Mtimes.lean` (issue #62), matching `Zonotope`, `VPolytope`,
`ConZonotope` and `ConPolyZono`, which each give this fact its own file too.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem PolyZonotope.mtimes_eq_map (M : Mat ℝ m n) (PZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope.mtimes M PZ = PZ.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
