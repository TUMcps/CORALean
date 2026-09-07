import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Matrix-vector multiplication as a continuous linear map

`variation_of_constants` and `expIntegral_mulVec` both move a matrix
exponential through an integral or a derivative, which needs the map applying
it to be continuous in the matrix, not only in the vector. Finite dimension is
what makes every piece of it continuous.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

-- the exponential and `toContinuousLinearMap` both cost instance search, throughout
/-- Matrix-vector multiplication as a continuous linear map in the matrix, which
is what lets the product rule apply to `e^{-As} x(s)`. Finite dimension is what
makes every piece of it continuous. -/
noncomputable def mulVecL : Mat ℝ n n →L[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
      map_add' := by intro M N; ext v i; simp
      map_smul' := by intro c M; ext v i; simp }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
