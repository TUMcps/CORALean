import CORALean.ContSet.Zonotope.Real.Operations.Abs
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import Mathlib.Algebra.BigOperators.Pi

/-!
# What `Zonotope.abs` keeps of its input

`abs` is not an enclosure: the zonotope with generators `(1, 1)` and `(1, -1)` contains
`(2, 0)`, whose entrywise absolute value is not on the segment `abs` leaves. What it keeps is the
box corner: the vertex `|c| + Σ |gⱼ|` of `abs Z` (all coefficients `1`) bounds every point's
entrywise absolute value, and `abs` is idempotent and has the same corner.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `abs` is idempotent. -/
theorem Zonotope.abs_abs (Z : Zonotope (Vec ℝ n)) : Z.abs.abs = Z.abs := by
  simp [Zonotope.abs]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
