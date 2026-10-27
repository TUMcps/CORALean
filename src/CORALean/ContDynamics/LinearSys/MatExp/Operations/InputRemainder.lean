module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# The exponential's remainder, scaled by a step

`inputRemainder`: the `E(r) · r` of [1, Prop. 2]: what the orders past `η` contribute to an input
solution over a step, the exponential's remainder bound scaled by the step and constant in
the entry, the bound being on the norm.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the exponential remainder scaled by the step

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

/-- The `E(r) · r` of [1, Prop. 2]: what the orders past `η` contribute to an input
solution over a step, the exponential's remainder bound scaled by the step and
constant in the entry, the bound being on the norm. -/
noncomputable def MatExp.inputRemainder (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun _ _ => -(r * MatExp.expRemainderBound (r • A) η)
  sup := fun _ _ => r * MatExp.expRemainderBound (r • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
