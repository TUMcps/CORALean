module

public import CORALean.ContSet.Interval.Real.Operations.Ctranspose
public import CORALean.ContSet.Interval.Real.Theorems.TransposeExact
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

/-!
# `Interval.ctranspose` is exactly the conjugate-transposed set

The conjugate transpose is the transpose over ℝ, so `transpose_exact` carries over.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the conjugate-transposed box is exactly the set of conjugate transposes
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ctranspose_exact (I : Interval (Mat ℝ m n)) :
    I.ctranspose.construct = Matrix.conjTranspose '' I.construct := by
  rw [show (Matrix.conjTranspose : Mat ℝ m n → Mat ℝ n m) = Matrix.transpose from
    funext fun A => Matrix.conjTranspose_eq_transpose_of_trivial A]
  exact Interval.transpose_exact I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
