import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

/-!
# A linear functional on matrices, entry by entry

`f M = Σ M_{kj} f(E_{kj})`, with `E_{kj}` the matrix unit.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A functional on matrices is `M ↦ Σ M_{kj} f(E_{kj})`. -/
theorem functional_eq_sum_single (f : Matrix (Fin n) (Fin m) ℝ →ₗ[ℝ] ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) :
    f M = ∑ k, ∑ j, M k j * f (single k j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single k j (M k j) = M k j • single k j (1 : ℝ) by simp, map_smul, smul_eq_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
