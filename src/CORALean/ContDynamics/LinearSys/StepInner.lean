import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimePointStep
import CORALean.ContDynamics.LinearSys.StepError
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Inner approximations of a continuous step

`LinearSysDT.reachInner` at a continuous-time step: the computed enclosure minus
the ball its own error is bounded by. `StepError` names those radii, and taking
one back off is what turns an outer approximation into an inner one.

Both are `Set`s. `minkowskiDiff` is a specification and computes nothing, and
the subtrahend here is a ball rather than a representation, so there is no
`minkDiffRep` counterpart to pair them with — a representation of the difference
would need the error as a zonotope, which is what `LinearSysDT.reachError`
supplies discretely and `StepError` deliberately does not.

Soundness never depends on the radius being tight, only on it being an upper
bound: a larger error yields a smaller inner approximation, possibly empty, and
never an unsound one — which is what lets [1] read an inner approximation off an
outer one whose error is bounded. `Theorems.TimePointStepInnerInner` and its
time-interval counterpart are where that is proved.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The step's end minus the ball its enclosure error is bounded by — an inner
approximation of the states the step reaches. -/
noncomputable def LinearSys.timePointStepInner (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ U : Zonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.timePointStep (S := 𝒵) r η X₀ U).construct
    (Metric.closedBall (0 : Vec ℝ n) (sys.timePointStepError r η U))

/-- The same over the whole step: the enclosure of the step minus the ball its
own error is bounded by. -/
noncomputable def LinearSys.timeIntervalStepInner (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (X₀ : Zonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.timeIntervalStep (S := 𝒵) r η X₀).construct
    (Metric.closedBall (0 : Vec ℝ n) (sys.timeIntervalStepError r η X₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
