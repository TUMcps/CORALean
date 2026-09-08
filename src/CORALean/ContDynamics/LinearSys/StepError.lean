import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# How much a step's enclosure exceeds what the step actually reaches

The counterpart of `LinearSysDT.reachError`, as a radius rather than a set: at
`Zonotope` the excess of a continuous step is not a box but a ball, so what is
named here is how large that ball has to be.

Both radii scale with `∑ⱼ absBound j`, the operand's `ℓ¹` reach, which bounds a
point of it and is what the boxed generators of an interval-matrix product are
summed over.
`timePointStepError` has two parts, and the second is the one [1] tunes:
`e^{r‖A‖} - 1` is what a Minkowski sum over the orders costs, each order free to
pick its own input where a trajectory holds one — second order in the step and
untouched by the truncation order — and `expRemainderBound` is the series
remainder, which the order does reduce.

`timeIntervalStepError` is dominated by `‖e^{rA} - I‖`, *first* order in the
step: a `linComb` between a set and its image reaches outside every state the
flow visits, and the correction matrix, second order, does not pay for it.

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

/-- How far `timeIntervalStep` reaches past the states the step actually visits:
the hull over the step, and the correction matrix it is widened by. -/
noncomputable def LinearSys.timeIntervalStepError (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ : Zonotope (Vec ℝ n)) : ℝ :=
  (∑ j, X₀.absBound j) * (‖exp (r • toRealMat sys.A) - 1‖
    + 2 * (Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖
      + MatExp.expRemainderBound (r • toRealMat sys.A) η))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
