import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# How far `timePointStep` reaches past the states the step actually ends at

The counterpart of `LinearSysDT.reachError`, as a radius rather than a set: at
`Zonotope` the excess of a continuous step is not a box but a ball, so what is
named here is how large that ball has to be.

Both radii scale with `∑ⱼ absBound j`, the operand's `ℓ¹` reach, which bounds a
point of it and is what the boxed generators of an interval-matrix product are
summed over. `timePointStepError` has two parts, and the second is the one
[1] tunes: `e^{r‖A‖} - 1` is what a Minkowski sum over the orders costs, each
order free to pick its own input where a trajectory holds one — second order
in the step and untouched by the truncation order — and `expRemainderBound`
is the series remainder, which the order does reduce.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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
