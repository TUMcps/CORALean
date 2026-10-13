module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# How far `timeIntervalStep` reaches past the states the step actually visits

`timeIntervalStepError`, the counterpart [1] tunes for over a whole step, is
dominated by `‖e^{rA} - I‖`, *first* order in the step: a `linComb` between a
set and its image reaches outside every state the flow visits, and the
correction matrix, second order, does not pay for it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far `timeIntervalStep` reaches past the states the step actually visits:
the hull over the step, and the correction matrix it is widened by. -/
noncomputable def LinearSys.timeIntervalStepError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ : Zonotope (Vec ℝ n)) : ℝ :=
  (∑ j, X₀.absBound j) * (‖exp (r • toRealMat sys.A) - 1‖
    + 2 * (Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖
      + MatExp.expRemainderBound (r • toRealMat sys.A) η))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
