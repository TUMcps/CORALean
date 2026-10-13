import CORALean.ContSet.Zonotope.Real.Operations.RotMat
import Mathlib.Data.Matrix.Mul

/-!
# `rotMat` on the first coordinate

On the coordinates `i ≠ j` the matrix is CORA's `R`: the first row is `(cos, -sin)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x_i ↦ cos x_i - sin x_j`. -/
theorem rotMat_mulVec_left {n : ℕ} (i j : Fin n) (hij : i ≠ j) (angle : ℝ) (x : Vec ℝ n) :
    (rotMat n i j angle *ᵥ x) i = Real.cos angle * x i - Real.sin angle * x j := by
  simp only [mulVec, dotProduct, rotMat, if_true]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij]
  · simp [hij.symm]; ring
  · intro b _ hb; simp [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
