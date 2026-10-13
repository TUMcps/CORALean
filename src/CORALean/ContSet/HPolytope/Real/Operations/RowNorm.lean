module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# `HPolytope.rowNorm`

`‖aᵢ‖₂`, the 2-norm of the coefficients of a constraint row: `A_norm = sqrt(sum(A.^2, 2))` of
`@polytope/center`'s `aux_center_LP`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The 2-norm of the coefficients of a row. -/
noncomputable def HPolytope.rowNorm (a : Vec ℝ n →ₗ[ℝ] ℝ) : ℝ :=
  _root_.Real.sqrt (∑ j, (a (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
