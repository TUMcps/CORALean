module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# The exponential's remainder, at a step

`expRemainder`: the `E(Δt, η)` of [1, Thm. 1] itself, without `inputRemainder`'s extra `r ·`.
`Theorems/SuperlinearDecreaseExpRemainder` is `Lemma 1` about this.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order

## Output
* interval matrix of the exponential remainder at the step

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
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

/-- The `E(Δt, η)` of [1, Thm. 1] itself, without `inputRemainder`'s extra `r ·`.
`Theorems/SuperlinearDecreaseExpRemainder` is `Lemma 1` about this. -/
noncomputable def MatExp.expRemainder (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun _ _ => -MatExp.expRemainderBound (Δt • A) η
  sup := fun _ _ => MatExp.expRemainderBound (Δt • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
