module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The exponential of a sum of multiples of one matrix

`e^{(a+b)A} = e^{aA} e^{bA}`: both factors are powers of the same matrix, so they commute and
Mathlib's `exp_add_of_commute` applies. The window-by-window reach proofs split `e^{A(r+kr)}`
into a step and the earlier windows with it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{A(a+b)} = e^{Aa} e^{Ab}`. -/
theorem exp_add_smul_eq_mul (A : Mat ℝ n n) (a b : ℝ) :
    exp ((a + b) • A) = exp (a • A) * exp (b • A) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl A).smul_left a).smul_right b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
