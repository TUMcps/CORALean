module

public import CORALean.ContSet.ConZonotope.Real.Operations.Map
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ContSet/ConZonotope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ===============================  `ConZonotope.mtimes_eq_map`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConZonotope.mtimes_eq_map (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    ConZonotope.mtimes M cZ = cZ.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
