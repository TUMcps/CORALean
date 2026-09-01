import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContSet.Zonotope.Real.API

/-!
# The step enclosure at a zonotope, over the whole step

`timeInterval_outer_inputSolution` with the representation substituted in, as
`ReachOuterZonotope` does for the sample times. The same three zonotope lemmas
discharge all six properties of `U` and of the remainder product.

`0 ∈ U` does not follow from being a zonotope and stays a hypothesis — Althoff's
first case, the only one with a single enclosure for the whole step.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

set_option maxHeartbeats 1000000 in
/-- Every trajectory whose initial and input sets are zonotopes stays in the
step enclosure at every time of the step, not only at its end. -/
theorem LinearSys.Trajectory.timeInterval_outer_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope (Vec ℝ n)} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory (S := 𝒵) R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus
      (sys.timeIntervalStep (S := 𝒵) r (m + 2) R₀)
      (sys.inputSolution (S := 𝒵) r (m + 2) U)) :=
  traj.timeInterval_outer_inputSolution hr hε ht0 htr
    U.convex_construct U.isClosed_construct U.isBounded_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
      U).convex_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
      U).isClosed_construct
    (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) (MatExp.inputRemainder (toRealMat sys.A) r (m + 2))
      U).isBounded_construct
    h0

end CORALean.Real
