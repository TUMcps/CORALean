import CORALean.ContSet.VPolytope.Real.VPolytope
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `VPolytope.distPoint`

CORA's `aux_distPolyPoint(S, x)` of `polytope/hausdorffDist`: the Euclidean distance of a point
`x` to a polytope `S`, `sqrt(val + x'x)` with `val` the optimal value of the quadratic program
`min y'y - 2x'y` over `y ∈ S` (`problem.H = 2 I`, `problem.f = -2x`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_distPolyPoint(S, x)`: `problem.H = 2 I`, `problem.f = -2x`, the minimum of
`y'y - 2x'y` over `S`, then `sqrt(val + x'x)`. -/
noncomputable def VPolytope.distPoint (S : Set (Vec ℝ n)) (x : Vec ℝ n) : ℝ :=
  -- `[~, val] = CORAquadprog(problem)`
  let val : ℝ := sInf ((fun y : Vec ℝ n => ∑ i, y i * y i - 2 * ∑ i, x i * y i) '' S)
  Real.sqrt (val + ∑ i, x i * x i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
