module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor

@[expose] public section

/-!
# Enclosing the matrix exponential

`expEnclosure`: [1, Thm. 1] at a single matrix, `expTaylor` as the center and `expRemainderBound` as
the radius.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so every
file reasoning about these must make the same one — the `l∞` operator norm.

## Inputs
* `x` – matrix
* `η` – Taylor order

## Output
* interval matrix enclosing the matrix exponential

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

noncomputable def MatExp.expEnclosure (x : Mat ℝ n n) (η : ℕ) : Interval (Mat ℝ n n) where
  inf := fun i j => MatExp.expTaylor x η i j - MatExp.expRemainderBound x η
  sup := fun i j => MatExp.expTaylor x η i j + MatExp.expRemainderBound x η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
