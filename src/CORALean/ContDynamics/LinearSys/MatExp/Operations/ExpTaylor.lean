module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The matrix exponential's Taylor truncation

`expTaylor`: [1, Thm. 1]'s series truncated at `η`, the center of the enclosure
`expEnclosure` builds around `exp x`.

## Inputs
* `x` – matrix
* `η` – Taylor order

## Output
* Taylor truncation of the matrix exponential

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The series truncated at `η`, which is the center of the enclosure. -/
noncomputable def MatExp.expTaylor (x : Mat ℝ n n) (η : ℕ) : Mat ℝ n n :=
  ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹) • x ^ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
