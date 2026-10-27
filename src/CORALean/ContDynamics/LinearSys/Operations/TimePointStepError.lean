module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

@[expose] public section

/-!
# How far `timePointStep` reaches past the states the step actually ends at

The counterpart of `LinearSysDT.reachError`, as a radius rather than a set: at `Zonotope` the
excess of a continuous step is not a box but a ball, so what is named here is how large that ball
has to be. Both radii scale with `∑ⱼ absBound j`, the operand's `ℓ¹` reach, which bounds a point of
it. `timePointStepError` has two parts, and the second is the one [1] tunes: `e^{r‖A‖} - 1` is what
a Minkowski sum over the orders costs, each order free to pick its own input where a trajectory
holds one (second order in the step and untouched by the truncation order), and
`expRemainderBound` is the series remainder, which the order does reduce.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input zonotope

## Output
* radius by which the time-point step reaches past the states it ends at

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
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

/-- How far `timePointStep` reaches past the states the step actually ends at:
the dependency the Taylor orders lose, and the series remainder. -/
noncomputable def LinearSys.timePointStepError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : Zonotope (Vec ℝ n)) : ℝ :=
  2 * (∑ j, U.absBound j) * r * ((Real.exp (r * ‖toRealMat sys.A‖) - 1)
    + MatExp.expRemainderBound (r • toRealMat sys.A) η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
