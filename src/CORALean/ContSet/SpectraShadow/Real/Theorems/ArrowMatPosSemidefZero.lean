import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatQuadForm
import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatIsHermitian
import Mathlib.Analysis.Matrix.Order

/-!
# The arrowhead matrix at the apex

For `s = 0`, `w = 0` and `0 ≤ t` the arrowhead matrix is positive semidefinite: its form is `t a²`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem arrowMat_posSemidef_zero {t : ℝ} (ht : 0 ≤ t) :
    (arrowMat 0 t (0 : Vec ℝ N)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (arrowMat_isHermitian 0 t 0) fun x => ?_
  rw [star_trivial, arrowMat_quadForm]
  simpa using mul_nonneg ht (sq_nonneg (x 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
