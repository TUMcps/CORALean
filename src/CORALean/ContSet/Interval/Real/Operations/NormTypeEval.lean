module

public import CORALean.ContSet.Interval.Real.Definitions.NormType
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `Interval.NormType.eval`

`norm(M, type)` of a numeric matrix: `1` is the maximum absolute column sum, `Inf` the maximum
absolute row sum, `'fro'` the square root of the sum of squares. The maxima are `⨆` over a
finite index, which is `0` for an empty matrix, as MATLAB's `norm([])` is.

## Inputs
* none

## Output
* the chosen norm of the matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The value of the norm of `type` at a matrix. -/
noncomputable def Interval.NormType.eval : Interval.NormType → Mat ℝ m n → ℝ
  | .one, M => ⨆ j, ∑ i, |M i j|
  | .inf, M => ⨆ i, ∑ j, |M i j|
  | .fro, M => Real.sqrt (∑ i, ∑ j, M i j ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
