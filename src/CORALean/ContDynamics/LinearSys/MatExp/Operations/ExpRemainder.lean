import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

/-!
# The exponential's remainder, at a step

`expRemainder`: the `E(Δt, η)` of [1] itself, without `inputRemainder`'s extra `r ·`.
`Theorems/SuperlinearDecreaseExpRemainder` is `Lemma 1` about this.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `E(Δt, η)` of [1] itself, without `inputRemainder`'s extra `r ·`.
`Theorems/SuperlinearDecreaseExpRemainder` is `Lemma 1` about this. -/
noncomputable def MatExp.expRemainder (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun _ _ => -MatExp.expRemainderBound (Δt • A) η
  sup := fun _ _ => MatExp.expRemainderBound (Δt • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
