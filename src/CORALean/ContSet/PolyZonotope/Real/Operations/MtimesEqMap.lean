module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `PolyZonotope.mtimes` is `map` at the matrix's linear map

Split out of `Mtimes.lean` (issue #62), matching `Zonotope`, `VPolytope`,
`ConZonotope` and `ConPolyZono`, which each give this fact its own file too.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem PolyZonotope.mtimes_eq_map (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope.mtimes M pZ = pZ.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
