module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# The exponential's remainder is continuous in the time

The exponential and its truncation are both continuous in `τ`, so their
difference is, which is what makes the remainder of an input solution
measurable and bounded on a compact step.

## Inputs
* `A` – system matrix
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the exponential minus its truncation is continuous in time
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exponential and its truncation are continuous in the time, so their
difference is too. -/
theorem MatExp.continuous_expDiff (A : Mat ℝ n n) (η : ℕ) :
    Continuous fun τ : ℝ => exp (τ • A) - MatExp.expTaylor (τ • A) η := by -- --- PROOF ---
  have hsmul : Continuous fun τ : ℝ => τ • A := continuous_id.smul continuous_const
  refine (exp_continuous.comp hsmul).sub ?_
  simp only [MatExp.expTaylor]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const : Continuous fun _ : ℝ => ((Nat.factorial i : ℝ)⁻¹)).smul (hsmul.pow i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
