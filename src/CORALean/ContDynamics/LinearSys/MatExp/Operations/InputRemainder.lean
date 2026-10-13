import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

/-!
# The exponential's remainder, scaled by a step

`inputRemainder`: the `E(r) · r` of [1]: what the orders past `η` contribute to an input
solution over a step, the exponential's remainder bound scaled by the step and constant in
the entry, the bound being on the norm.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `E(r) · r` of [1]: what the orders past `η` contribute to an input
solution over a step, the exponential's remainder bound scaled by the step and
constant in the entry, the bound being on the norm. -/
noncomputable def MatExp.inputRemainder (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun _ _ => -(r * MatExp.expRemainderBound (r • A) η)
  sup := fun _ _ => r * MatExp.expRemainderBound (r • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
