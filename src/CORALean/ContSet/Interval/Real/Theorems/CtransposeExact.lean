import CORALean.ContSet.Interval.Real.Operations.Ctranspose
import CORALean.ContSet.Interval.Real.Theorems.TransposeExact

/-!
# `Interval.ctranspose` is exactly the conjugate-transposed set

The conjugate transpose is the transpose over ℝ, so `transpose_exact` carries over.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
