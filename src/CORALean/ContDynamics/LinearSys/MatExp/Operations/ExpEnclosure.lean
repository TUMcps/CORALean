import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor

/-!
# Enclosing the matrix exponential

`expEnclosure`: [1, Eq. (3.2)–(3.3)], `expTaylor` as the centre and `expRemainderBound` as the
radius.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these must make the same one — the `l∞` operator norm.

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

noncomputable def MatExp.expEnclosure (x : Mat ℝ n n) (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun i j => MatExp.expTaylor x η i j - MatExp.expRemainderBound x η
  sup := fun i j => MatExp.expTaylor x η i j + MatExp.expRemainderBound x η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
