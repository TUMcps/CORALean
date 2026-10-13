import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic

/-!
# The Gram matrix of a matrix's columns

`Σₖ mₖ mₖᵀ = M Mᵀ` over the columns `mₖ` of `M`: the generators `D`, `F` of a disturbance or
noise zonotope give `Q_w = D Dᵀ`, `Q_v = F Fᵀ` in the observer papers' covariation form.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sum_vecMulVec_col (M : Mat ℝ n m) :
    ∑ k, vecMulVec (fun i => M i k) (fun i => M i k) = M * Mᵀ := by
  ext a b
  simp [mul_apply, Matrix.sum_apply, vecMulVec_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
